/-
Standalone proof-structure extractor, adapted from LeanDojo's
`ExtractData.lean` (src/lean_dojo/data_extraction/ExtractData.lean),
trimmed down to: process ONE source file by re-elaborating it with
`infoState` enabled, walk the resulting `InfoTree`s the same way LeanDojo
does (TacticInfo -> before/after pretty-printed goal states, TermInfo ->
premise/constant usage), and dump only the slice of the trace that falls
inside a caller-specified byte range (one declaration).

Usage:
  lake env lean --run ExtractOne.lean <path/to/File.lean> <startLine> <endLine> <declName>

Run from inside a directory whose `lake env` has the target module's
dependencies already built (here: ~/git/lean-pool, which has Mathlib
oleans built).
-/
import Lean

open Lean Elab System

set_option maxHeartbeats 2000000

instance : ToJson String.Pos.Raw where
  toJson n := toJson n.byteIdx

namespace Extract1

/-- The trace of one tactic step: pretty-printed goal state before/after. -/
structure TacticTrace where
  stateBefore : String
  stateAfter  : String
  pos         : String.Pos.Raw
  endPos      : String.Pos.Raw
deriving ToJson

/-- The trace of one premise (constant) usage inside a term. -/
structure PremiseTrace where
  fullName : String
  modName  : String
  pos      : Option Position
  endPos   : Option Position
deriving ToJson

structure Trace where
  tactics  : Array TacticTrace
  premises : Array PremiseTrace
deriving ToJson

abbrev TraceM := StateT Trace MetaM

namespace Pp

private def addLine (s : String) : String :=
  if s.isEmpty then s else s ++ "\n"

-- Ported verbatim from LeanDojo: like `Meta.ppGoal` but uses String so that
-- local declarations are always newline-separated.
private def ppGoal (mvarId : MVarId) : MetaM String := do
  match (← getMCtx).findDecl? mvarId with
  | none => return "unknown goal"
  | some mvarDecl =>
    let indent := 2
    let lctx := mvarDecl.lctx
    let lctx := lctx.sanitizeNames.run' { options := (← getOptions) }
    Meta.withLCtx lctx mvarDecl.localInstances do
      let rec pushPending (ids : List Name) (type? : Option Expr) (s : String) : MetaM String := do
        if ids.isEmpty then
          return s
        else
          let s := addLine s
          match type? with
          | none => return s
          | some type =>
            let typeFmt ← Meta.ppExpr type
            return (s ++ (Format.joinSep ids.reverse (format " ") ++ " :" ++
              Format.nest indent (Format.line ++ typeFmt)).group).pretty
      let rec ppVars (varNames : List Name) (prevType? : Option Expr) (s : String)
          (localDecl : LocalDecl) : MetaM (List Name × Option Expr × String) := do
        match localDecl with
        | .cdecl _ _ varName type _ _ =>
          let varName := varName.simpMacroScopes
          let type ← instantiateMVars type
          if prevType? == none || prevType? == some type then
            return (varName :: varNames, some type, s)
          else do
            let s ← pushPending varNames prevType? s
            return ([varName], some type, s)
        | .ldecl _ _ varName type val _ _ => do
          let varName := varName.simpMacroScopes
          let s ← pushPending varNames prevType? s
          let s := addLine s
          let type ← instantiateMVars type
          let typeFmt ← Meta.ppExpr type
          let mut fmtElem := format varName ++ " : " ++ typeFmt
          let val ← instantiateMVars val
          let valFmt ← Meta.ppExpr val
          fmtElem := fmtElem ++ " :=" ++ Format.nest indent (Format.line ++ valFmt)
          let s := s ++ fmtElem.group.pretty
          return ([], none, s)
      let (varNames, type?, s) ← lctx.foldlM (init := ([], none, ""))
        fun (varNames, prevType?, s) (localDecl : LocalDecl) =>
          if localDecl.isAuxDecl || localDecl.isImplementationDetail then
            return (varNames, prevType?, s)
          else
            ppVars varNames prevType? s localDecl
      let s ← pushPending varNames type? s
      let goalTypeFmt ← Meta.ppExpr (← instantiateMVars mvarDecl.type)
      let goalFmt := Meta.getGoalPrefix mvarDecl ++ Format.nest indent goalTypeFmt
      let s := s ++ "\n" ++ goalFmt.pretty
      match mvarDecl.userName with
      | Name.anonymous => return s
      | name => return "case " ++ name.eraseMacroScopes.toString ++ "\n" ++ s

def ppGoals (ctx : ContextInfo) (goals : List MVarId) : IO String :=
  if goals.isEmpty then
    return "no goals"
  else
    let fmt := ctx.runMetaM {} (return Std.Format.prefixJoin "\n\n" (← goals.mapM (ppGoal ·)))
    return (← fmt).pretty.trim

end Pp

namespace Traversal

private def visitTacticInfo (ctx : ContextInfo) (ti : TacticInfo) (parent : InfoTree) : TraceM Unit := do
  match parent with
  | .node (Info.ofTacticInfo i) _ =>
    match i.stx.getKind with
    | ``Lean.Parser.Tactic.tacticSeq1Indented | ``Lean.Parser.Tactic.tacticSeqBracketed
    | ``Lean.Parser.Tactic.rewriteSeq =>
      let ctxBefore := { ctx with mctx := ti.mctxBefore }
      let ctxAfter := { ctx with mctx := ti.mctxAfter }
      let stateBefore ← Pp.ppGoals ctxBefore ti.goalsBefore
      let stateAfter ← Pp.ppGoals ctxAfter ti.goalsAfter
      if stateBefore == "no goals" || stateBefore == stateAfter then
        pure ()
      else
        let some posBefore := ti.stx.getPos? true | pure ()
        let some posAfter := ti.stx.getTailPos? true | pure ()
        modify fun trace => {
          trace with tactics := trace.tactics.push {
            stateBefore, stateAfter, pos := posBefore, endPos := posAfter
          }
        }
    | _ => pure ()
  | _ => pure ()

private def visitTermInfo (ti : TermInfo) (env : Environment) : TraceM Unit := do
  let some fullName := ti.expr.constName? | return ()
  let fileMap ← getFileMap
  let posBefore := match ti.toElabInfo.stx.getPos? with
    | some p => fileMap.toPosition p
    | none => none
  let posAfter := match ti.toElabInfo.stx.getTailPos? with
    | some p => fileMap.toPosition p
    | none => none
  let modName :=
    if let some modIdx := env.const2ModIdx.get? fullName then
      env.header.moduleNames[modIdx.toNat]!
    else
      env.header.mainModule
  modify fun trace => {
    trace with premises := trace.premises.push {
      fullName := toString fullName, modName := toString modName,
      pos := posBefore, endPos := posAfter
    }
  }

private def visitInfo (ctx : ContextInfo) (i : Info) (parent : InfoTree) (env : Environment) : TraceM Unit := do
  match i with
  | .ofTacticInfo ti => visitTacticInfo ctx ti parent
  | .ofTermInfo ti => visitTermInfo ti env
  | _ => pure ()

private partial def traverseTree (ctx : ContextInfo) (tree : InfoTree) (parent : InfoTree) (env : Environment) : TraceM Unit := do
  match tree with
  | .context ctx' t =>
    match ctx'.mergeIntoOuter? ctx with
    | some ctx' => traverseTree ctx' t tree env
    | none => panic! "fail to synthesize contextInfo when traversing infoTree"
  | .node i children =>
    visitInfo ctx i parent env
    for x in children do
      traverseTree ctx x tree env
  | _ => pure ()

private def traverseTopLevelTree (tree : InfoTree) (env : Environment) : TraceM Unit := do
  match tree with
  | .context ctx t =>
    match ctx.mergeIntoOuter? none with
    | some ctx => traverseTree ctx t tree env
    | none => panic! "fail to synthesize contextInfo for top-level infoTree"
  | _ => pure ()

def traverseForest (trees : Array InfoTree) (env : Environment) : TraceM Trace := do
  for t in trees do
    traverseTopLevelTree t env
  get

end Traversal

open Traversal

/-- Process one file: re-parse + re-elaborate with infoState enabled, walk
the trees, and keep only the slice inside `[startPos, endPos)`. -/
unsafe def processFile (path : FilePath) (startLine endLine : Nat) : IO Trace := do
  let input ← IO.FS.readFile path
  enableInitializersExecution
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx

  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        IO.println s!"ERROR: {← msg.toString}"
    throw <| IO.userError "Errors during import; aborting"

  let env := env.setMainModule (← moduleNameOfFileName path none)
  let commandState := { Command.mkState env messages {} with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState commandState
  let env' := s.commandState.env
  let trees := s.commandState.infoState.trees.toArray

  let fileMap := FileMap.ofString input
  let startPos := fileMap.ofPosition ⟨startLine, 0⟩
  let endPos := fileMap.ofPosition ⟨endLine, 0⟩

  let traceM := (traverseForest trees env').run' ⟨#[], #[]⟩
  let (trace, _) ← traceM.run'.toIO {fileName := s!"{path}", fileMap} {env := env'}

  return {
    tactics := trace.tactics.filter (fun t => t.pos >= startPos && t.endPos <= endPos),
    premises := trace.premises.filter (fun p =>
      match p.pos, p.endPos with
      | some pb, some pe => fileMap.ofPosition pb >= startPos && fileMap.ofPosition pe <= endPos
      | _, _ => false)
  }

end Extract1

open Extract1

unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  match args with
  | [path, startLine, endLine] =>
    let trace ← processFile ⟨path⟩ startLine.toNat! endLine.toNat!
    IO.println (toJson trace).pretty
  | _ => throw <| IO.userError "usage: ExtractOne.lean <path> <startLine> <endLine>"
