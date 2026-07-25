/-
Batch corpus extractor: statement-level metadata (name/kind/module/byte-range/
typeclass deps, à la lean-pool's `scripts/exposition/Extract.lean`) FOLDED
INTO the same InfoTree-walking pass that `ExtractOne.lean` used for
tactic-tree + premise-trace extraction.

Rationale for folding both extractors into one pass instead of running the
two tools separately and joining by name afterward: `ExtractOne.lean`
already re-elaborates the whole file with `infoState.enabled := true`, which
produces a full `Environment` with extension state populated (unlike
`Extract.lean`'s `importModules ... loadExts := false`, which is cheap
precisely because it skips that). Since we're paying full-elaboration cost
anyway, the resulting `env'` already supports every query
`Extract.lean` needs (`isGenerated`, `findDeclarationRanges?`, docstrings,
...), so a second re-elaboration pass just to get statement metadata would
be pure waste. One elaboration, one InfoTree walk, one JSONL record per
declaration.

Per-file, not per-declaration: elaboration cost is dominated by imports and
whole-file processing, not by declaration count, so this script batches
over a LIST of files (one elaboration each) rather than requiring a
caller-supplied line range per declaration the way `ExtractOne.lean` did.

Declaration boundaries: after `IO.processCommands` on the *unimported*
source, declarations newly introduced by this file have no module index yet
(`env.getModuleIdxFor?` only resolves constants that arrived via imported
oleans) — so "defined in this file" is exactly `getModuleIdxFor? = none`.
Each tactic/premise trace entry (which carries a byte position from the
InfoTree walk) is assigned to the first declaration whose
`findDeclarationRanges?` byte-span contains it. This does not disambiguate
nested/auxiliary declarations sharing overlapping ranges (e.g. `where`
clauses); see README.md for known limitations.

Cross-file dependency edges: each input file is elaborated independently
(matching the single-file re-elaboration model of `ExtractOne.lean`), so a
declaration's `deps` only includes edges to OTHER declarations defined in
the SAME file. References to declarations from other files in the batch are
counted only via `ext` (external-dependency count), not resolved into edges
- there is no cross-file join. See README.md.

Usage:
  lake env lean --run ExtractBatch.lean <out.jsonl> <path/to/File1.lean> [<path/to/File2.lean> ...]

Run from inside ~/git/lean-pool (built Mathlib oleans on lean-toolchain
v4.32.0-rc1), the same way as ExtractOne.lean.
-/
import Lean

open Lean Elab Meta System

set_option maxHeartbeats 4000000

instance : ToJson String.Pos.Raw where
  toJson n := toJson n.byteIdx

namespace ExtractBatch

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

/-- Raw (unassigned) InfoTree walk output for one file. -/
structure RawTrace where
  tactics  : Array TacticTrace
  premises : Array PremiseTrace
deriving ToJson

/-- One declaration's joined corpus record: statement-level metadata plus
the tactic/premise trace entries assigned to it. -/
structure DeclRecord where
  id       : String            -- fully qualified name
  n        : String            -- display name
  m        : String            -- module
  k        : String            -- kind (theorem/def/opaque/axiom/structure/inductive)
  r        : Array Nat         -- [startLine, startCol, endLine, endCol]
  s        : Array Nat         -- [nameLine, nameCol]
  doc      : Option String
  deps     : Array String      -- intra-file dependency edges (see file doc)
  tdeps    : Option (Array String)  -- statement-only (type) deps, theorems only
  ext      : Nat                -- count of distinct out-of-file deps encountered
  tactics  : Array TacticTrace
  premises : Array PremiseTrace
deriving ToJson

abbrev TraceM := StateT RawTrace MetaM

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

def traverseForest (trees : Array InfoTree) (env : Environment) : TraceM RawTrace := do
  for t in trees do
    traverseTopLevelTree t env
  get

end Traversal

open Traversal

-- ---------------------------------------------------------------------
-- Statement-level metadata, ported from lean-pool's
-- scripts/exposition/Extract.lean, adapted so "in-pool" means "defined in
-- the file currently being processed" instead of "under a fixed root
-- namespace". See file doc for why `getModuleIdxFor? = none` identifies
-- locally-defined constants.
-- ---------------------------------------------------------------------

namespace Statements

def kindOf (env : Environment) (name : Name) (info : ConstantInfo) : Option String :=
  match info with
  | .thmInfo _ => some "theorem"
  | .defnInfo _ => some "def"
  | .opaqueInfo _ => some "opaque"
  | .axiomInfo _ => some "axiom"
  | .inductInfo _ => if isStructure env name then some "structure" else some "inductive"
  | _ => none

def isGenerated (env : Environment) (name : Name) : CoreM Bool := do
  let display := privateToUserName name
  if display.isInternalDetail then return true
  if isAuxRecursor env name || isNoConfusion env name then return true
  if (← isRec name) || (← Meta.isMatcher name) then return true
  if (env.getProjectionFnInfo? name).isSome then return true
  if let .str _ "quot" := display then
    if let some info := env.find? name then
      if info.type.isConstOf ``Lean.ParserDescr
          || info.type.isConstOf ``Lean.TrailingParserDescr then
        return true
  return false

/-- Is `name` newly introduced by the file currently being elaborated
(rather than arriving via an imported olean)? -/
def isLocal (env : Environment) (name : Name) : Bool :=
  (env.getModuleIdxFor? name).isNone

def isExposed (env : Environment) (name : Name) (info : ConstantInfo) : CoreM Bool := do
  unless isLocal env name do return false
  if (kindOf env name info).isNone then return false
  if ← isGenerated env name then return false
  return (← findDeclarationRanges? name).isSome

def directUses (env : Environment) (info : ConstantInfo) : Array Name :=
  match info with
  | .inductInfo v =>
    v.ctors.foldl (init := info.getUsedConstantsAsSet)
      (fun acc c => match env.find? c with
        | some ci => acc.insertMany ci.getUsedConstantsAsSet
        | none => acc)
      |>.toArray
  | _ => info.getUsedConstantsAsSet.toArray

def resolveSeeds (env : Environment) (self : Name) (seeds : Array Name)
    (exposed : NameSet) : NameSet × Nat := Id.run do
  let mut edges : NameSet := {}
  let mut externals : NameSet := {}
  let mut visited : NameSet := {}
  let mut stack : Array Name := seeds
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if c == self || visited.contains c then continue
    visited := visited.insert c
    if exposed.contains c then
      edges := edges.insert c
      continue
    if isLocal env c then
      if let some ci := env.find? c then
        stack := stack ++ directUses env ci
    else
      externals := externals.insert c
  return (edges, externals.size)

def escapeName (n : Name) : String := n.toString

/-- Statement-level fields for one exposed declaration, minus the r/s
byte-range conversion (done by the caller, which also has the `FileMap`). -/
structure StmtInfo where
  id     : String
  n      : String
  m      : String
  k      : String
  ranges : DeclarationRanges
  doc    : Option String
  deps   : Array String
  tdeps  : Option (Array String)
  ext    : Nat

def stmtInfo (env : Environment) (name : Name) (info : ConstantInfo)
    (exposed : NameSet) : CoreM (Option StmtInfo) := do
  let some ranges ← findDeclarationRanges? name | return none
  let some kind := kindOf env name info | return none
  let module := env.header.mainModule
  let display := privateToUserName name
  let doc ← findDocString? env name
  let (edges, extCount) := resolveSeeds env name (directUses env info) exposed
  let typeEdges : Option NameSet := match info with
    | .thmInfo v => some (resolveSeeds env name v.type.getUsedConstants exposed).1
    | _ => none
  return some {
    id := escapeName name, n := escapeName display, m := module.toString, k := kind,
    ranges, doc, deps := edges.toArray.map escapeName,
    tdeps := typeEdges.map (·.toArray.map escapeName), ext := extCount
  }

/-- All exposed (locally-defined, non-generated, ranged) declarations in
`env`, in declaration order. -/
def collectExposed (env : Environment) : CoreM (Array (Name × ConstantInfo × StmtInfo)) := do
  let mut exposed : NameSet := {}
  let mut acc : Array (Name × ConstantInfo) := #[]
  for (name, info) in env.constants.toList do
    if isLocal env name then
      if ← isExposed env name info then
        exposed := exposed.insert name
        acc := acc.push (name, info)
  let mut out : Array (Name × ConstantInfo × StmtInfo) := #[]
  for (name, info) in acc do
    if let some si ← stmtInfo env name info exposed then
      out := out.push (name, info, si)
  return out

end Statements

open Statements

/-- Heuristic for `moduleNameOfFileName`'s `rootDir` argument: Lean/Lake
convention puts a package's Lean sources under `<lowercase-package-dir>/
<CapitalizedRootNamespace>/...` (e.g. `.lake/packages/mathlib/Mathlib/...`,
`langlands/Langlands/...`). Passing `none` makes `moduleNameOfFileName` fall
back to a naive raw-path module name (e.g. `«.lake».packages.mathlib.…`)
whenever the file isn't under a directory already on the Lean search path
as a *source* root (our LEAN_PATH only has built `.olean` dirs). Splitting
the path at the first capitalized component recovers the intended module
name without needing a source search path. Falls back to `none` (naive
behavior) if no capitalized component is found. -/
def guessRootDir (path : FilePath) : Option FilePath :=
  let comps := (path.toString.splitOn "/").filter (· ≠ "")
  match comps.findIdx? (fun c => match c.toList.head? with | some ch => ch.isUpper | none => false) with
  | some 0 | none => none
  | some i => some ⟨String.intercalate "/" (comps.take i)⟩

/-- Does byte range `[aStart, aEnd)` contain `[bStart, bEnd)`? -/
private def contains (aStart aEnd bStart bEnd : String.Pos.Raw) : Bool :=
  aStart <= bStart && bEnd <= aEnd

/-- Process one file: re-parse + re-elaborate with infoState enabled, walk
the InfoTrees for tactic/premise traces, collect exposed-declaration
statement metadata, and assign each trace entry to its enclosing
declaration by byte range. -/
unsafe def processFile (path : FilePath) : IO (Array DeclRecord) := do
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

  let env := env.setMainModule (← moduleNameOfFileName path (guessRootDir path))
  let commandState := { Command.mkState env messages {} with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState commandState
  let env' := s.commandState.env
  let trees := s.commandState.infoState.trees.toArray
  let fileMap := FileMap.ofString input

  let coreContext : Core.Context := { fileName := path.toString, fileMap, maxHeartbeats := 0 }

  let traceM := (traverseForest trees env').run' ⟨#[], #[]⟩
  let (rawTrace, _) ← traceM.run'.toIO {fileName := path.toString, fileMap} {env := env'}

  let (exposed, _) ← (collectExposed env').toIO coreContext { env := env' }

  let declSpans := exposed.map fun (name, _, si) =>
    (name, si, fileMap.ofPosition si.ranges.range.pos, fileMap.ofPosition si.ranges.range.endPos)

  let findEnclosing (pos endPos : String.Pos.Raw) : Option (Name × StmtInfo) :=
    declSpans.findSome? fun (name, si, s, e) =>
      if contains s e pos endPos then some (name, si) else none

  let mut byDecl : Std.HashMap Name (Array TacticTrace × Array PremiseTrace) :=
    Std.HashMap.ofList (declSpans.toList.map fun (name, _, _, _) => (name, (#[], #[])))

  for t in rawTrace.tactics do
    if let some (name, _) := findEnclosing t.pos t.endPos then
      byDecl := byDecl.modify name fun (ts, ps) => (ts.push t, ps)

  for p in rawTrace.premises do
    match p.pos, p.endPos with
    | some pb, some pe =>
      let bp := fileMap.ofPosition pb
      let be := fileMap.ofPosition pe
      if let some (name, _) := findEnclosing bp be then
        byDecl := byDecl.modify name fun (ts, ps) => (ts, ps.push p)
    | _, _ => pure ()

  return declSpans.map fun (name, si, _, _) =>
    let (tactics, premises) := byDecl.getD name (#[], #[])
    let r := si.ranges.range
    let sel := si.ranges.selectionRange
    {
      id := si.id, n := si.n, m := si.m, k := si.k,
      r := #[r.pos.line, r.pos.column, r.endPos.line, r.endPos.column],
      s := #[sel.pos.line, sel.pos.column],
      doc := si.doc, deps := si.deps, tdeps := si.tdeps, ext := si.ext,
      tactics, premises
    }

end ExtractBatch

open ExtractBatch

unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  match args with
  | outPath :: (path0 :: pathsRest) =>
    let paths := path0 :: pathsRest
    let handle ← IO.FS.Handle.mk outPath .write
    let mut total := 0
    for path in paths do
      IO.eprintln s!"processing {path} ..."
      let recs ← processFile ⟨path⟩
      for r in recs do
        handle.putStrLn (toJson r).compress
      total := total + recs.size
      IO.eprintln s!"  {recs.size} declarations"
    handle.flush
    IO.eprintln s!"wrote {total} declarations across {paths.length} files to {outPath}"
  | _ => throw <| IO.userError "usage: ExtractBatch.lean <out.jsonl> <path/to/File1.lean> [<path/to/File2.lean> ...]"
