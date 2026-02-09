use clap::{Parser, Subcommand};
use motif::classify::{classify, detect_properties};
use motif::conjecture::conjecture;
use motif::diff::equiv_diff;
use motif::explore::explore;
use motif::inclusion::check_inclusion;
use motif::lean;
use motif::parse::parse_theory;
use motif::theory::{SaturationConfig, Theory};
use std::path::PathBuf;
use std::process;

#[derive(Parser)]
#[command(name = "motif", about = "Structural exploration of mathematics")]
struct Cli {
    #[command(subcommand)]
    command: Command,

    /// Saturation iteration limit
    #[arg(long, default_value = "10", global = true)]
    iters: usize,
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

fn load_theory(path: &PathBuf) -> Theory {
    let content = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: cannot read {}: {e}", path.display());
            process::exit(1);
        }
    };
    match parse_theory(&content) {
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

    match cli.command {
        Command::Classify { file } => {
            let theory = load_theory(&file);
            let props = detect_properties(&theory);
            let classes = classify(&theory);

            println!("Theory: {}", theory.name);
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
            let theory = load_theory(&file);
            let var_list: Vec<&str> = vars.split(',').map(|s| s.trim()).collect();
            let expr_count = motif::explore::enumerate(&theory.signature, &var_list, depth).len();

            eprintln!(
                "Exploring {} with {} expressions (depth {}, vars: {})...",
                theory.name, expr_count, depth, vars
            );

            match explore(&theory, &var_list, depth, &config) {
                Ok(classes) => {
                    if classes.is_empty() {
                        println!("No non-trivial equivalences found.");
                    } else {
                        println!("Found {} equivalence classes:\n", classes.len());
                        for (i, class) in classes.iter().enumerate() {
                            println!("  {}.", i + 1);
                            for member in &class.members {
                                println!("    {member}");
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
        Command::Check { sub, sup } => {
            let sub_theory = load_theory(&sub);
            let sup_theory = load_theory(&sup);

            match check_inclusion(&sub_theory, &sup_theory, &config) {
                Ok(result) => {
                    println!(
                        "{} ⊂ {} : {}",
                        sub_theory.name,
                        sup_theory.name,
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
            let theory = load_theory(&file);
            match theory.equiv(&expr_a, &expr_b, &config) {
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
            let base_theory = load_theory(&base);
            let ext_theory = load_theory(&extended);
            let var_list: Vec<&str> = vars.split(',').map(|s| s.trim()).collect();

            eprintln!(
                "Conjecturing: what does {} prove that {} can't? (depth {}, vars: {})...",
                ext_theory.name, base_theory.name, depth, vars
            );

            match conjecture(&base_theory, &ext_theory, &var_list, depth, &config) {
                Ok(conjectures) => {
                    if conjectures.is_empty() {
                        println!("No novel equivalences found.");
                    } else {
                        println!("Found {} novel equivalence(s):\n", conjectures.len());
                        for (i, c) in conjectures.iter().enumerate() {
                            println!("  {}. Novel pairs:", i + 1);
                            for (a, b) in &c.novel_pairs {
                                println!("    {a}  =  {b}");
                            }
                            println!("    (from class: {} members)", c.equiv_class.members.len());
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
            let theory = load_theory(&file);
            println!("{}", lean::theory_to_lean(&theory));

            if do_explore {
                let var_list: Vec<&str> = vars.split(',').map(|s| s.trim()).collect();
                match motif::explore::explore(&theory, &var_list, depth, &config) {
                    Ok(classes) => {
                        if !classes.is_empty() {
                            println!();
                            println!(
                                "{}",
                                lean::equiv_classes_to_lean(&theory, &classes, "discovered")
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
        Command::Diff {
            first,
            second,
            expr,
            candidates,
        } => {
            let theory_a = load_theory(&first);
            let theory_b = load_theory(&second);
            let candidate_refs: Vec<&str> = candidates.iter().map(|s| s.as_str()).collect();

            let diff = equiv_diff(&expr, &candidate_refs, &theory_a, &theory_b, &config);

            let only_a = diff.only_first();
            let only_b = diff.only_second();
            let both = diff.in_both();

            if !both.is_empty() {
                println!("Both {} and {}:", theory_a.name, theory_b.name);
                for c in &both {
                    println!("  {c}");
                }
            }
            if !only_a.is_empty() {
                println!("Only {}:", theory_a.name);
                for c in &only_a {
                    println!("  {c}");
                }
            }
            if !only_b.is_empty() {
                println!("Only {}:", theory_b.name);
                for c in &only_b {
                    println!("  {c}");
                }
            }
            if both.is_empty() && only_a.is_empty() && only_b.is_empty() {
                println!("No equivalences found in either theory.");
            }
        }
    }
}
