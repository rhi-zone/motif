use clap::{Parser, Subcommand};
use motif::classify::{classify, detect_properties};
use motif::diff::equiv_diff;
use motif::inclusion::check_inclusion;
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
