use clap::{Parser, Subcommand, ValueEnum};
use motif::classify::{classify, detect_properties};
use motif::conjecture::conjecture;
use motif::diff::equiv_diff;
use motif::discover::discover_morphisms;
use motif::explore::explore;
use motif::inclusion::check_inclusion;
use motif::lattice::TheoryLattice;
use motif::lean;
use motif::parse::{parse_theory_full, ParsedTheory};
use motif::pretty::{
    ascii_notation, latex_notation, pretty, unicodemath_notation, Notation, NotationSpec,
};
use motif::theory::SaturationConfig;
use std::path::PathBuf;
use std::process;

#[derive(Parser)]
#[command(name = "motif", about = "Structural exploration of mathematics")]
struct Cli {
    #[command(subcommand)]
    command: Command,

    /// Saturation iteration limit
    #[arg(long, default_value = "5", global = true)]
    iters: usize,

    /// Output format for mathematical expressions
    #[arg(long, default_value = "unicodemath", global = true)]
    format: OutputFormat,
}

#[derive(Clone, Copy, ValueEnum)]
enum OutputFormat {
    /// UnicodeMath: a · b, a⁻¹, ¬a
    #[value(name = "unicodemath")]
    UnicodeMath,
    /// LaTeX math mode: a \cdot b, a^{-1}, \lnot a
    Latex,
    /// Plain ASCII: a * b, a^(-1), ~a
    Ascii,
}

#[derive(Subcommand)]
enum Command {
    /// Detect structural properties and classify a theory
    Classify {
        /// Path to a .theory file
        file: PathBuf,
    },
    /// Check if one theory is a subtheory of another
    Check {
        /// Path to the candidate subtheory
        sub: PathBuf,
        /// Path to the candidate supertheory
        sup: PathBuf,
    },
    /// Check equivalence of two expressions under a theory
    Equiv {
        /// Path to a .theory file
        file: PathBuf,
        /// First expression (s-expression with Var)
        expr_a: String,
        /// Second expression (s-expression with Var)
        expr_b: String,
    },
    /// Explore: enumerate expressions and discover equivalences
    Explore {
        /// Path to a .theory file
        file: PathBuf,
        /// Expression depth limit
        #[arg(long, default_value = "2")]
        depth: usize,
        /// Variable names to use (comma-separated)
        #[arg(long, default_value = "a,b")]
        vars: String,
    },
    /// Discover novel equivalences in a theory relative to a base
    Conjecture {
        /// Path to the base (weaker) .theory file
        base: PathBuf,
        /// Path to the extended (stronger) .theory file
        extended: PathBuf,
        /// Expression depth limit
        #[arg(long, default_value = "2")]
        depth: usize,
        /// Variable names to use (comma-separated)
        #[arg(long, default_value = "a")]
        vars: String,
    },
    /// Export a theory as Lean 4 code
    Lean {
        /// Path to a .theory file
        file: PathBuf,
        /// Also explore and export discovered equivalences as theorems
        #[arg(long)]
        explore: bool,
        /// Expression depth limit (with --explore)
        #[arg(long, default_value = "1")]
        depth: usize,
        /// Variable names (with --explore, comma-separated)
        #[arg(long, default_value = "a,b")]
        vars: String,
    },
    /// Discover operation mappings between theories that preserve axioms
    Discover {
        /// Path to the source theory
        source: PathBuf,
        /// Path to the target theory
        target: PathBuf,
        /// Template expression depth (0 = rename-only, 1+ = also try compound templates)
        #[arg(long, default_value = "0")]
        depth: usize,
    },
    /// Discover subtheory relationships between theories
    Lattice {
        /// Paths to .theory files
        #[arg(required = true)]
        files: Vec<PathBuf>,
        /// Output DOT (Graphviz) format
        #[arg(long)]
        dot: bool,
    },
    /// Compare what two theories prove about an expression
    Diff {
        /// Path to first .theory file
        first: PathBuf,
        /// Path to second .theory file
        second: PathBuf,
        /// Expression to test
        expr: String,
        /// Candidate expressions to check equivalence against
        candidates: Vec<String>,
    },
}

fn notation_for(fmt: OutputFormat, specs: &[(String, NotationSpec)]) -> Notation {
    let mut n = match fmt {
        OutputFormat::UnicodeMath => unicodemath_notation(),
        OutputFormat::Latex => latex_notation(),
        OutputFormat::Ascii => ascii_notation(),
    };
    n.add_specs(specs);
    n
}

fn load_theory(path: &PathBuf) -> ParsedTheory {
    let content = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: cannot read {}: {e}", path.display());
            process::exit(1);
        }
    };
    match parse_theory_full(&content) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("error: {}: {e}", path.display());
            process::exit(1);
        }
    }
}

fn main() {
    let cli = Cli::parse();
    let config = SaturationConfig {
        iter_limit: cli.iters,
    };
    let fmt = cli.format;

    match cli.command {
        Command::Classify { file } => {
            let parsed = load_theory(&file);
            let props = detect_properties(&parsed.theory);
            let classes = classify(&parsed.theory);

            println!("Theory: {}", parsed.theory.name);
            println!();
            println!("Properties:");
            for prop in &props {
                println!("  {prop:?}");
            }
            println!();
            println!("Classifications:");
            if classes.is_empty() {
                println!("  (none detected)");
            } else {
                for class in &classes {
                    println!("  {class:?}");
                }
            }
        }
        Command::Explore { file, depth, vars } => {
            let parsed = load_theory(&file);
            let notation = notation_for(fmt, &parsed.notation);
            let var_list: Vec<&str> = vars.split(',').map(|s| s.trim()).collect();
            let expr_count =
                motif::explore::enumerate(&parsed.theory.signature, &var_list, depth).len();

            eprintln!(
                "Exploring {} with {} expressions (depth {}, vars: {})...",
                parsed.theory.name, expr_count, depth, vars
            );

            match explore(&parsed.theory, &var_list, depth, &config) {
                Ok(classes) => {
                    if classes.is_empty() {
                        println!("No non-trivial equivalences found.");
                    } else {
                        println!("Found {} equivalence classes:\n", classes.len());
                        for (i, class) in classes.iter().enumerate() {
                            let members: Vec<String> =
                                class.members.iter().map(|m| pretty(m, &notation)).collect();
                            println!("  {}.  {}", i + 1, members.join("  =  "));
                            println!();
                        }
                    }
                }
                Err(e) => {
                    eprintln!("error: {e}");
                    process::exit(1);
                }
            }
        }
        Command::Check { sub, sup } => {
            let sub_parsed = load_theory(&sub);
            let sup_parsed = load_theory(&sup);

            match check_inclusion(&sub_parsed.theory, &sup_parsed.theory, &config) {
                Ok(result) => {
                    println!(
                        "{} ⊂ {} : {}",
                        sub_parsed.theory.name,
                        sup_parsed.theory.name,
                        if result.is_included { "yes" } else { "no" }
                    );
                    if !result.signature_compatible {
                        println!("  (signatures incompatible)");
                    } else {
                        for (name, preserved) in &result.axioms {
                            let mark = if *preserved { "✓" } else { "✗" };
                            println!("  {mark} {name}");
                        }
                    }
                }
                Err(e) => {
                    eprintln!("error: {e}");
                    process::exit(1);
                }
            }
        }
        Command::Equiv {
            file,
            expr_a,
            expr_b,
        } => {
            let parsed = load_theory(&file);
            match parsed.theory.equiv(&expr_a, &expr_b, &config) {
                Ok(true) => println!("equivalent"),
                Ok(false) => println!("not equivalent"),
                Err(e) => {
                    eprintln!("error: {e}");
                    process::exit(1);
                }
            }
        }
        Command::Conjecture {
            base,
            extended,
            depth,
            vars,
        } => {
            let base_parsed = load_theory(&base);
            let ext_parsed = load_theory(&extended);
            let notation = notation_for(fmt, &ext_parsed.notation);
            let var_list: Vec<&str> = vars.split(',').map(|s| s.trim()).collect();

            eprintln!(
                "Conjecturing: what does {} prove that {} can't? (depth {}, vars: {})...",
                ext_parsed.theory.name, base_parsed.theory.name, depth, vars
            );

            match conjecture(
                &base_parsed.theory,
                &ext_parsed.theory,
                &var_list,
                depth,
                &config,
            ) {
                Ok(conjectures) => {
                    if conjectures.is_empty() {
                        println!("No novel equivalences found.");
                    } else {
                        println!("Found {} novel equivalence(s):\n", conjectures.len());
                        for (i, c) in conjectures.iter().enumerate() {
                            println!("  {}.", i + 1);
                            for (a, b) in &c.novel_pairs {
                                println!(
                                    "    {}  =  {}",
                                    pretty(a, &notation),
                                    pretty(b, &notation)
                                );
                            }
                            println!();
                        }
                    }
                }
                Err(e) => {
                    eprintln!("error: {e}");
                    process::exit(1);
                }
            }
        }
        Command::Lean {
            file,
            explore: do_explore,
            depth,
            vars,
        } => {
            let parsed = load_theory(&file);
            println!("{}", lean::theory_to_lean(&parsed.theory));

            if do_explore {
                let var_list: Vec<&str> = vars.split(',').map(|s| s.trim()).collect();
                match motif::explore::explore(&parsed.theory, &var_list, depth, &config) {
                    Ok(classes) => {
                        if !classes.is_empty() {
                            println!();
                            println!(
                                "{}",
                                lean::equiv_classes_to_lean(&parsed.theory, &classes, "discovered")
                            );
                        }
                    }
                    Err(e) => {
                        eprintln!("error exploring: {e}");
                        process::exit(1);
                    }
                }
            }
        }
        Command::Discover {
            source,
            target,
            depth,
        } => {
            let src = load_theory(&source);
            let tgt = load_theory(&target);

            eprintln!(
                "Discovering morphisms: {} → {}...{}",
                src.theory.name,
                tgt.theory.name,
                if depth > 0 {
                    format!(" (template depth {depth})")
                } else {
                    String::new()
                }
            );

            match discover_morphisms(&src.theory, &tgt.theory, &config, depth) {
                Ok(results) => {
                    if results.is_empty() {
                        println!("No axiom-preserving morphisms found.");
                    } else {
                        println!(
                            "Found {} morphism(s) from {} → {}:\n",
                            results.len(),
                            src.theory.name,
                            tgt.theory.name
                        );
                        for (i, m) in results.iter().enumerate() {
                            let mapping_str: Vec<String> = m
                                .mapping
                                .iter()
                                .map(|(s, t)| format!("{s} → {t}"))
                                .collect();
                            println!(
                                "  {}.  {{{}}}  ({}/{} axioms preserved)",
                                i + 1,
                                mapping_str.join(", "),
                                m.preserved_count,
                                m.total_count
                            );
                            for (name, preserved) in &m.axioms {
                                let mark = if *preserved { "✓" } else { "✗" };
                                println!("      {mark} {name}");
                            }
                            println!();
                        }
                    }
                }
                Err(e) => {
                    eprintln!("error: {e}");
                    process::exit(1);
                }
            }
        }
        Command::Lattice { files, dot } => {
            let parsed: Vec<ParsedTheory> = files.iter().map(load_theory).collect();
            let theory_refs: Vec<(&str, &motif::theory::Theory)> = parsed
                .iter()
                .map(|p| (p.theory.name.as_str(), &p.theory))
                .collect();

            eprintln!(
                "Checking pairwise inclusion for {} theories...",
                theory_refs.len()
            );

            match TheoryLattice::from_theories(&theory_refs, &config) {
                Ok(lattice) => {
                    let reduced = lattice.reduce();
                    if dot {
                        println!("digraph theories {{");
                        println!("  rankdir=BT;");
                        for name in &lattice.theories {
                            println!("  \"{name}\";");
                        }
                        for edge in &reduced {
                            println!("  \"{}\" -> \"{}\";", edge.sub, edge.sup);
                        }
                        println!("}}");
                    } else if reduced.is_empty() {
                        println!("No subtheory relationships found.");
                    } else {
                        println!("Subtheory relationships (transitive reduction):\n");
                        for edge in &reduced {
                            println!("  {} ⊂ {}", edge.sub, edge.sup);
                        }
                    }
                }
                Err(e) => {
                    eprintln!("error: {e}");
                    process::exit(1);
                }
            }
        }
        Command::Diff {
            first,
            second,
            expr,
            candidates,
        } => {
            let first_parsed = load_theory(&first);
            let second_parsed = load_theory(&second);
            let notation = notation_for(fmt, &first_parsed.notation);
            let candidate_refs: Vec<&str> = candidates.iter().map(|s| s.as_str()).collect();

            let diff = equiv_diff(
                &expr,
                &candidate_refs,
                &first_parsed.theory,
                &second_parsed.theory,
                &config,
            );

            let pp = |s: &str| pretty(s, &notation);
            let only_a = diff.only_first();
            let only_b = diff.only_second();
            let both = diff.in_both();

            if !both.is_empty() {
                println!(
                    "Both {} and {}:",
                    first_parsed.theory.name, second_parsed.theory.name
                );
                for c in &both {
                    println!("  {} = {}", pp(&diff.expr), pp(c));
                }
            }
            if !only_a.is_empty() {
                println!("Only {}:", first_parsed.theory.name);
                for c in &only_a {
                    println!("  {} = {}", pp(&diff.expr), pp(c));
                }
            }
            if !only_b.is_empty() {
                println!("Only {}:", second_parsed.theory.name);
                for c in &only_b {
                    println!("  {} = {}", pp(&diff.expr), pp(c));
                }
            }
            if both.is_empty() && only_a.is_empty() && only_b.is_empty() {
                println!("No equivalences found in either theory.");
            }
        }
    }
}
