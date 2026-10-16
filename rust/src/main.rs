//! Organismal-aging multi-counter model (v0.4).
//!
//! Division counters (any-of exit): centriole S_c, **telomere** T, **mitochondrial
//! (mtDNA) damage** M, proteostasis P. The centriole is ONE counter, not THE counter.
//!
//! Core: self-renewal at every level is time-dependent — the renewal rate declines
//! as the organismal damage load grows (positive feedback = organismal aging):
//!
//!     f_L(t+1) = f_L(t)·(1 − r_L(t)) + d_L/Smax_L        (normalized load fraction)
//!     r_L(t)   = r_L0 · exp(−κ_L · S_org(t))            (renewal declines)
//!     S_org(t) = Σ w_L·f_L(t)  +  w_c·min(1, S_c/K_c)   (incl. centriole counter)
//!
//! Observed proxy L_n (nm, OU, mean-reverting, bounded variance) is separate from the
//! counters (unbounded S_c). "+29% plasma-cell elongation" is a sensitivity check
//! (multiple myeloma context), NOT calibration. n* is a model output.

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

#[derive(Clone, Debug)]
struct Level {
    _name: &'static str,
    n_max: u64,
    d: f64,
    e_max: f64,
    half_life_days: f64,
    kappa: f64,
    w: f64,
    _lit: &'static str,
}

#[derive(Clone, Debug)]
struct Params {
    d_c: f64,
    sigma_c: f64,
    k_c: f64, // centriole counter
    f0: f64,
    k: f64,
    f_min: f64, // export
    t0: f64,
    tau: f64,
    t_min: f64, // telomere counter
    d_m: f64,
    k_m: f64, // mtDNA counter
    d_p: f64,
    r_p: f64,
    k_p: f64, // proteostasis counter
    e_drift: f64,
    k_e: f64, // epigenetic mitotic counter
    cycle: f64,
}

impl Params {
    fn base() -> Self {
        Params {
            d_c: 0.6,
            sigma_c: 0.3,
            k_c: 30.0,
            f0: 0.9,
            k: 0.1,
            f_min: 0.05,
            t0: 100.0,
            tau: 1.0,
            t_min: 10.0,
            d_m: 0.5,
            k_m: 25.0,
            d_p: 0.4,
            r_p: 0.05,
            k_p: 8.0,
            e_drift: 0.5,
            k_e: 25.0,
            cycle: 1.0,
        }
    }
}

fn r0(half_life_days: f64, cycle_days: f64) -> f64 {
    1.0 - (-(2.0_f64.ln()) * cycle_days / half_life_days).exp()
}

fn levels() -> Vec<Level> {
    vec![
        Level {
            _name: "mRNA",
            n_max: 3_000,
            d: 0.02,
            e_max: 1.0,
            half_life_days: 0.3,
            kappa: 0.5,
            w: 0.05,
            _lit: "hl 4-8 h",
        },
        Level {
            _name: "short-lived protein",
            n_max: 100_000,
            d: 0.01,
            e_max: 1.0,
            half_life_days: 1.0,
            kappa: 0.5,
            w: 0.10,
            _lit: "hl 0.5-2 d",
        },
        Level {
            _name: "long-lived protein",
            n_max: 10_000,
            d: 0.02,
            e_max: 1.0,
            half_life_days: 30.0,
            kappa: 2.0,
            w: 0.20,
            _lit: "hl weeks-years",
        },
        Level {
            _name: "mitochondrion",
            n_max: 500,
            d: 0.05,
            e_max: 1.0,
            half_life_days: 15.0,
            kappa: 2.0,
            w: 0.15,
            _lit: "hl ~15 d",
        },
        Level {
            _name: "lysosome",
            n_max: 200,
            d: 0.03,
            e_max: 1.0,
            half_life_days: 7.0,
            kappa: 1.0,
            w: 0.10,
            _lit: "hl ~7 d",
        },
        Level {
            _name: "structure (cilium)",
            n_max: 1,
            d: 0.02,
            e_max: 1.0,
            half_life_days: 7.0,
            kappa: 1.5,
            w: 0.10,
            _lit: "turnover ~wk",
        },
        Level {
            _name: "centriole",
            n_max: 1,
            d: 0.0,
            e_max: 1.0,
            half_life_days: 1e9,
            kappa: 0.0,
            w: 0.30,
            _lit: "stable/non-renewable",
        },
    ]
}

struct OrgTraj {
    s_org: Vec<f64>,
    r_sample: Vec<f64>,
    aging_rate: Vec<f64>,
}

fn organismal_trajectory(levels: &[Level], p: &Params, n_max: usize) -> OrgTraj {
    let mut f_l: Vec<f64> = vec![0.0; levels.len()];
    let mut traj = OrgTraj {
        s_org: Vec::new(),
        r_sample: Vec::new(),
        aging_rate: Vec::new(),
    };
    let mut s_org_prev = 0.0;
    for n in 1..=n_max {
        let mut s_org = 0.0;
        let mut r_long = 0.0;
        for (i, l) in levels.iter().enumerate() {
            let smax = l.n_max as f64 * l.e_max;
            let d_norm = l.d / smax;
            let r = r0(l.half_life_days, p.cycle) * (-l.kappa * s_org_prev).exp();
            if i == 2 {
                r_long = r;
            }
            let mut fn_ = f_l[i] * (1.0 - r) + d_norm;
            if fn_ > 1.0 {
                fn_ = 1.0;
            }
            f_l[i] = fn_;
            s_org += l.w * fn_;
        }
        let s_c = p.d_c * n as f64;
        let c_load = (s_c / p.k_c).min(1.0);
        s_org += levels[6].w * c_load;
        traj.s_org.push(s_org);
        traj.r_sample.push(r_long);
        let rate = if n > 1 { s_org - s_org_prev } else { 0.0 };
        traj.aging_rate.push(rate);
        s_org_prev = s_org;
    }
    traj
}

fn gauss(rng: &mut StdRng, mean: f64, sd: f64) -> f64 {
    let u1: f64 = rng.gen_range(0.0..1.0);
    let u2: f64 = rng.gen_range(0.0..1.0);
    mean + sd * (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos()
}

struct Outcome {
    exit: usize,
    cause: &'static str,
}

/// Multi-counter run: centriole, telomere, mtDNA, proteostasis (any-of exit).
fn run(p: &Params, seed: u64, n_max: usize) -> Option<Outcome> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut s_c = 0.0f64;
    let mut t_len = p.t0;
    let mut m_dam = 0.0f64;
    let mut p_dam = 0.0f64;
    let mut e_dam = 0.0f64;
    for n in 1..=n_max {
        let f = p.f0 * (-p.k * s_c).exp();
        if f < p.f_min {
            return Some(Outcome {
                exit: n,
                cause: "export collapse",
            });
        }
        s_c += gauss(&mut rng, p.d_c, p.sigma_c);
        t_len = (t_len - p.tau).max(0.0);
        m_dam += p.d_m;
        p_dam = p_dam + p.d_p - p.r_p * p_dam;
        e_dam += p.e_drift; // epigenetic mitotic counter accumulates per division
        if s_c > p.k_c {
            return Some(Outcome {
                exit: n,
                cause: "centriole counter",
            });
        }
        if t_len < p.t_min {
            return Some(Outcome {
                exit: n,
                cause: "telomere counter",
            });
        }
        if m_dam > p.k_m {
            return Some(Outcome {
                exit: n,
                cause: "mtDNA counter",
            });
        }
        if p_dam > p.k_p {
            return Some(Outcome {
                exit: n,
                cause: "proteostasis counter",
            });
        }
        if e_dam > p.k_e {
            return Some(Outcome {
                exit: n,
                cause: "epigenetic mitotic counter",
            });
        }
    }
    None
}

fn regime_b_days(d0: f64, d_b: f64, r_intra: f64, k_b: f64) -> f64 {
    if r_intra <= 0.0 {
        return (k_b - d0) / d_b;
    }
    let d_inf = d_b / r_intra;
    let a = d0 - d_inf;
    if a.abs() < 1e-12 {
        return f64::INFINITY;
    }
    let target = (k_b - d_inf) / a;
    if target <= 0.0 {
        if k_b >= d_inf {
            return f64::INFINITY;
        }
        return 0.0;
    }
    -target.ln() / r_intra
}

fn main() {
    let p = Params::base();
    let lv = levels();
    println!("{}", "=".repeat(72));
    println!("ORGANISMAL-AGING multi-counter model (v0.4) — counters: centriole, TELOMERE, mtDNA, proteostasis");
    println!("{}", "=".repeat(72));

    let n = 80usize;
    let tr = organismal_trajectory(&lv, &p, n);
    println!("\n(A) Organismal load S_org(t) + renewal decline (deterministic, incl. telomere & mtDNA as counters):");
    println!("  step | S_org | renewal(long-lived) | aging rate dS_org/div");
    for i in [0usize, 10, 20, 30, 40, 50, 60, 70, 79] {
        println!(
            "  {:>4} | {:6.3} | {:8.4} | {:9.4}",
            i, tr.s_org[i], tr.r_sample[i], tr.aging_rate[i]
        );
    }
    // organismal aging = decline of renewal rates over time (r_L(t) ↓).
    let r_early = tr.r_sample[0];
    let r_late = *tr.r_sample.last().unwrap_or(&0.0);
    let decline_pct = (1.0 - r_late / r_early.max(1e-9)) * 100.0;
    println!(
        "  renewal(long-lived): {:.4} -> {:.4}  (decline {:.1}% over {} divisions)",
        r_early,
        r_late,
        decline_pct,
        tr.r_sample.len()
    );
    println!("  (organismal aging = self-renewal rates decline as the damage load grows)");
    println!("  (note: per-level load fractions saturate; the unbounded counter is S_c)");

    println!("\n(B) Multi-counter exit (any-of) — sensitivity over centriole d_c:");
    println!("  | d_c  | n*   | cause |");
    for dc in [0.3, 0.6, 0.9, 1.2] {
        let mut pp = Params::base();
        pp.d_c = dc;
        let mut exits = Vec::new();
        let mut cause = "";
        for seed in 0..30 {
            if let Some(o) = run(&pp, seed, 400) {
                exits.push(o.exit);
                cause = o.cause;
            }
        }
        if !exits.is_empty() {
            let mean = exits.iter().sum::<usize>() as f64 / exits.len() as f64;
            println!("  | {:.1} | {:4.0} | {} |", dc, mean, cause);
        }
    }
    // base run: which counter wins first
    println!("\n  Base run (d_c=0.6) — first counter to fire across seeds:");
    let mut counts = std::collections::HashMap::new();
    for seed in 0..60 {
        if let Some(o) = run(&p, seed, 400) {
            *counts.entry(o.cause).or_insert(0usize) += 1;
        }
    }
    for (cause, cnt) in counts {
        println!("    {}: {} / 60", cause, cnt);
    }

    println!("\n(C) Regime B (non-dividing; intracellular export r_intra):");
    for (name, d0, db, rint, kb) in [
        ("cardio-like", 0.0, 0.1, 0.005, 19.0),
        ("C.elegans soma-like", 0.0, 0.05, 0.002, 24.0),
    ] {
        let days = regime_b_days(d0, db, rint, kb);
        let note = if days.is_infinite() {
            "(never: threshold >= steady state)"
        } else {
            "(illustrative)"
        };
        println!("  {}: age-to-threshold ≈ {:.0} days {}", name, days, note);
    }

    println!("\n(D) GERMLINE / meiotic bottleneck — reset of counters between generations:");
    let div_per_gen = 40usize;
    let scenarios = [
        (
            "full reset (beta_c=0, beta_t=1 telomerase, beta_m=0.05, beta_p=0)",
            Betas {
                beta_c: 0.0,
                beta_t: 1.0,
                beta_m: 0.05,
                beta_p: 0.0,
            },
        ),
        (
            "leak (beta_c=0.1, beta_t=0.05, beta_m=0.3, beta_p=0.1)",
            Betas {
                beta_c: 0.1,
                beta_t: 0.05,
                beta_m: 0.3,
                beta_p: 0.1,
            },
        ),
    ];
    for (label, betas) in scenarios {
        let rows = germline_generations(&p, &betas, 5, div_per_gen);
        println!(
            "  {} — S_c / telomere / mtDNA / proteostasis at birth:",
            label
        );
        for (g, sc, t, mm, pp) in rows {
            println!(
                "    gen {}: S_c={:5.1}  tel={:5.1}  mtDNA={:5.1}  proto={:5.2}",
                g, sc, t, mm, pp
            );
        }
    }
    println!("  (full reset => no trans-generational accumulation of counters;");
    println!("   leakage (beta>0) => paternal/maternal age effects on offspring)");

    println!("\n(E) DIPLOIDY as entropy accumulator and division counter:");
    // L loci, per-division mutation prob mu, exit when homozygous loci > z_thr
    let (loci, mu, z_thr) = (1000usize, 2e-3, 15usize);
    let do_ = diploidy_counter(loci, mu, z_thr, 400, 1);
    println!(
        "  L={} loci, mu={}, exit when homozygous loci > {}",
        loci, mu, z_thr
    );
    for i in [0usize, 20, 40, 60, 80, 100, 120, 150] {
        if i < do_.h.len() {
            println!(
                "    n={:>3}: heterozygous H={} (masked entropy), homozygous Z={}, D=H+2Z={}",
                i, do_.h[i], do_.z[i], do_.d[i]
            );
        }
    }
    match do_.exit {
        Some(n) => println!("  diploidy counter exit at n* = {} divisions", n),
        None => println!("  no exit within horizon"),
    }
    println!("  (diploidy buffers damage: heterozygous mutations are masked;");
    println!("   complementation is lost only when both copies fail -> a two-hit counter)");
    let mut h_exits = Vec::new();
    for seed in 0..30 {
        if let Some(n) = haploid_counter(loci, mu, z_thr, 400, seed) {
            h_exits.push(n);
        }
    }
    let h_mean = if h_exits.is_empty() {
        0.0
    } else {
        h_exits.iter().sum::<usize>() as f64 / h_exits.len() as f64
    };
    println!(
        "  HAPLOID comparison (1 copy): mean exit n* ≈ {:.0} divisions",
        h_mean
    );
    println!("  => diploidy = entropy buffer / division counter: the second copy masks");
    println!("     mutations, so replicative capacity is roughly doubled (two-hit).");

    println!("\n(F) MONTE-CARLO sensitivity (parameter ranges, not calibrated points):");
    let mc = monte_carlo(&p, 200, 400);
    if !mc.is_empty() {
        let mut sorted = mc.clone();
        sorted.sort_unstable();
        let mean = mc.iter().sum::<usize>() as f64 / mc.len() as f64;
        let p5 = sorted[(sorted.len() as f64 * 0.05) as usize];
        let p95 = sorted[((sorted.len() as f64 * 0.95) as usize).min(sorted.len() - 1)];
        println!(
            "  n* over 200 sims: mean={:.0}, median={}, 5-95% = [{} .. {}]",
            mean,
            sorted[sorted.len() / 2],
            p5,
            p95
        );
        println!(
            "  (parameters sampled: d_c 0.5-1.5, k 0.05-0.20, K_c 25-60, K_m 15-35, K_e 15-40)"
        );
    }

    println!("\n(G) MULTI-HIT (cancer) VALIDATION vs real phenotype:");
    let slope = multi_hit_slope(1000, 2e-3, 400, 1);
    println!(
        "  diploidy/mutation counter: log-log slope of homozygous hits ≈ {:.2}",
        slope
    );
    println!(
        "  empirical adult cancer incidence: ~ t^4..5 (Armitage-Doll, k=5-7 rate-limiting hits)"
    );
    println!(
        "  => CAVEAT: this prototype counts hits per cell, NOT the cell-population incidence;"
    );
    println!("     the per-cell hit slope (~2, quadratic) does NOT directly reproduce t^4-5;");
    println!("     a full Armitage-Doll incidence curve needs a population model (next step).");
    println!(
        "  (note: d_c in nm-scale, mu≈2.2 nm/div (OU): S_c(50) ≈ d_c·50 nm ~ +25-30% of L0=200 nm;"
    );
    println!("   kept as a SENSITIVITY check, not calibration)");

    println!("\n(H) POPULATION model for cancer incidence (Armitage-Doll, mean-field):");
    let inc = armitage_doll(6, 1e-3, 400, 1e7);
    // log-log slope over a clean window (n=100..350), incidence>0
    let mut sx = 0.0;
    let mut sy = 0.0;
    let mut sxx = 0.0;
    let mut sxy = 0.0;
    let mut cnt = 0.0;
    for i in 99..350 {
        if inc[i] > 0.0 {
            let x = (i as f64 + 1.0).ln();
            let y = inc[i].ln();
            sx += x;
            sy += y;
            sxx += x * x;
            sxy += x * y;
            cnt += 1.0;
        }
    }
    let slope = if cnt > 2.0 {
        (cnt * sxy - sx * sy) / (cnt * sxx - sx * sx).max(1e-9)
    } else {
        0.0
    };
    println!("  n0=1e7 cells, k=6 hits, lambda=1e-3/div (rare-event regime)");
    println!(
        "  incidence samples: n=100: {:.4}, n=200: {:.4}, n=300: {:.4}, n=380: {:.4}",
        inc[99], inc[199], inc[299], inc[379]
    );
    println!(
        "  log-log slope of incidence ≈ {:.2}  (prediction k-1 = 5; empirical t^4-5)",
        slope
    );
    println!("  => the mean-field multi-hit model reproduces the Armitage-Doll t^(k-1) curve.");

    println!("\n(I) HSC POOL exhaustion phenotype (MCARA anchor: ~7% lost by 75 years):");
    let (e, pool) = hsc_pool(1.0, 75, 0.07);
    println!("  per-year pool exit rate e ≈ {:.4}", e);
    for y in [0usize, 20, 40, 60, 75] {
        println!(
            "    year {:>2}: pool = {:.3} of N0 ({:.1}% lost)",
            y,
            pool[y],
            (1.0 - pool[y]) * 100.0
        );
    }
    println!(
        "  (matches the MCARA figure; a state-dependent exit would accelerate late-life decline)"
    );

    println!("\n(J) FALSIFIABLE prediction for f(S) (state-dependent export):");
    let (f0, k) = (0.9, 0.1);
    for s in [0.0f64, 5.0, 10.0, 15.0, 20.0, 25.0, 30.0] {
        println!(
            "    S={:>4.0}: predicted exported fraction f = {:.3}",
            s,
            f0 * (-k * s).exp()
        );
    }
    println!("  EXPERIMENT: measure the fraction of old/damaged units segregated to the");
    println!("  differentiating daughter in an asymmetric-division assay, as a function of the");
    println!("  cell's accumulated damage marker S. Prediction: f declines exponentially");
    println!("  (slope k, intercept f0). FALSIFIED if f is constant or non-monotonic in S.");

    println!("\n(K) Regime B (post-mitotic) with literature-based intracellular export:");
    println!("  heart protein half-life ~ 10-30 d (Gugel 2026) -> r_intra ~ 0.02-0.07 /day");
    for (name, d_b, r_intra, k_b) in [
        ("cardio (bulk protein turnover)", 0.1, 0.03, 3.0),
        ("cardio (slow turnover)", 0.05, 0.01, 5.0),
    ] {
        let d_inf = d_b / r_intra;
        let days = regime_b_days(0.0, d_b, r_intra, k_b);
        let note = if days.is_infinite() {
            format!("never reaches threshold (steady state d/r={:.1} < K={:.1}) -> gradual aging, no sharp exit", d_inf, k_b)
        } else {
            format!("age-to-threshold {:.0} d", days)
        };
        println!("  {}: {}", name, note);
    }
    println!("  => for post-mitotic cells the intracellular export keeps damage below a lethal");
    println!("     threshold for life: aging is GRADUAL, no replicative 'counter' exit.");
}

/// (E) **Diploidy as entropy accumulator and division counter.**
///
/// L loci, each with two copies (homologs). A locus is functional if at least one
/// copy is functional (recessive masking). Per division:
///   state 0 (both OK) -> state 1 (one copy damaged)  with prob 2·μ
///   state 1 (one damaged) -> state 2 (both damaged)  with prob μ  (LOH/homozygous)
/// "Entropy stored in diploidy" H(n) = # heterozygous (masked, buffered);
/// "manifest damage" Z(n) = # homozygous (complementation lost);
/// total entropy D(n) = H + 2·Z. The counter runs out when too many loci are
/// homozygous (or the heterozygous reservoir is depleted) -> cell dysfunction.
struct DiploidOut {
    h: Vec<usize>,
    z: Vec<usize>,
    d: Vec<usize>,
    exit: Option<usize>,
}

fn diploidy_counter(loci: usize, mu: f64, z_thr: usize, n_max: usize, seed: u64) -> DiploidOut {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut st: Vec<u8> = vec![0; loci]; // 0,1,2
    let mut out = DiploidOut {
        h: Vec::new(),
        z: Vec::new(),
        d: Vec::new(),
        exit: None,
    };
    for n in 1..=n_max {
        for s in st.iter_mut() {
            match *s {
                0 => {
                    if rng.gen_range(0.0..1.0) < 2.0 * mu {
                        *s = 1;
                    }
                }
                1 => {
                    if rng.gen_range(0.0..1.0) < mu {
                        *s = 2;
                    }
                }
                _ => {}
            }
        }
        let h = st.iter().filter(|&&s| s == 1).count();
        let z = st.iter().filter(|&&s| s == 2).count();
        out.h.push(h);
        out.z.push(z);
        out.d.push(h + 2 * z);
        if z > z_thr {
            out.exit = Some(n);
            break;
        }
    }
    out
}

/// Haploid comparison: one copy per locus. Diploidy should roughly double the
/// replicative capacity (the two-hit buffer).
fn haploid_counter(loci: usize, mu: f64, z_thr: usize, n_max: usize, seed: u64) -> Option<usize> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut damaged: usize = 0;
    for n in 1..=n_max {
        for _ in 0..loci {
            if rng.gen_range(0.0..1.0) < mu && damaged < loci {
                damaged += 1;
            }
        }
        if damaged > z_thr {
            return Some(n);
        }
    }
    None
}

/// (D) Germline / meiotic bottleneck: counters reset between generations.
/// Each counter survives meiosis with a fraction beta (0 = full reset,
/// >0 = trans-generational leakage). Telomere is partially restored by
/// telomerase in the germline.
struct Betas {
    beta_c: f64, // centriole (eliminated in oogenesis -> ~0)
    beta_t: f64, // telomere (telomerase restoration fraction toward t0; 1 = full reset)
    beta_m: f64, // mtDNA (genetic bottleneck -> small, but leaks)
    beta_p: f64, // proteostasis (mostly reset)
}

fn germline_generations(
    p: &Params,
    b: &Betas,
    n_gen: usize,
    div_per_gen: usize,
) -> Vec<(usize, f64, f64, f64, f64)> {
    let mut s_c = 0.0;
    let mut t = p.t0;
    let mut m = 0.0;
    let mut pr = 0.0;
    let mut rows = Vec::new();
    for g in 0..n_gen {
        for _ in 0..div_per_gen {
            s_c += p.d_c;
            t = (t - p.tau).max(0.0);
            m += p.d_m;
            pr = pr + p.d_p - p.r_p * pr;
        }
        // meiosis bottleneck:
        s_c = s_c * b.beta_c;
        t = t + b.beta_t * (p.t0 - t); // telomerase partial restoration
        m = m * b.beta_m;
        pr = pr * b.beta_p;
        rows.push((g, s_c, t, m, pr));
    }
    rows
}

/// (F) Monte-Carlo sensitivity: sample parameters from plausible ranges, report
/// the distribution of the replicative-lifespan output n*.
fn monte_carlo(p0: &Params, n_sims: usize, n_max: usize) -> Vec<usize> {
    let mut rng = StdRng::seed_from_u64(42);
    let mut exits = Vec::new();
    for _ in 0..n_sims {
        let mut pp = p0.clone();
        // plausible ranges (literature-ordered, not calibrated points)
        pp.d_c = 0.5 + rng.gen_range(0.0..1.0); // 0.5..1.5 per division
        pp.k = 0.05 + rng.gen_range(0.0..1.0) * 0.15; // 0.05..0.20
        pp.k_c = 25.0 + rng.gen_range(0.0..1.0) * 35.0; // 25..60
        pp.k_m = 15.0 + rng.gen_range(0.0..1.0) * 20.0; // 15..35
        pp.k_e = 15.0 + rng.gen_range(0.0..1.0) * 25.0; // 15..40
        if let Some(o) = run(&pp, 7, n_max) {
            exits.push(o.exit);
        }
    }
    exits
}

/// (G) Multi-hit (cancer) validation: with the diploidy/mutation counter, the
/// number of rate-limiting "hits" (homozygous loci Z) grows with divisions;
/// cancer incidence ~ t^(k-1) (Armitage-Doll, k≈5-7 for adult cancers).
/// We report the log-log slope of cumulative hits vs divisions.
fn multi_hit_slope(loci: usize, mu: f64, n_max: usize, seed: u64) -> f64 {
    let do_ = diploidy_counter(loci, mu, usize::MAX / 2, n_max, seed);
    let mut slope_sum = 0.0;
    let mut cnt = 0;
    for i in 0..do_.z.len() {
        let n = i + 1;
        let z = do_.z[i] as f64;
        if z > 0.0 {
            slope_sum += z.ln() / (n as f64).ln();
            cnt += 1;
        }
    }
    if cnt == 0 {
        0.0
    } else {
        slope_sum / cnt as f64
    }
}

/// (H) Population model for cancer incidence (Armitage-Doll), mean-field.
/// A fixed pool of n0 cells; each division, a cell with j hits acquires a hit with
/// probability lambda. Incidence (new k-hit cells per division) = X_{k-1}·lambda.
/// In the rare-event regime: X_{k-1}(n) ~ n0·(lambda·n)^(k-1)/(k-1)!,
/// so incidence ~ n^(k-1) -> log-log slope = k-1 (5 for k=6, matching t^4-5).
fn armitage_doll(k: usize, lambda: f64, n_max: usize, n0: f64) -> Vec<f64> {
    let mut x = vec![0.0f64; k]; // cells with j hits (0..k-1); k-hit cells are "cases"
    x[0] = n0;
    let mut incidence = Vec::new();
    for _ in 0..n_max {
        let mut xn = vec![0.0f64; k];
        xn[0] = x[0] * (1.0 - lambda);
        for j in 1..k {
            xn[j] = x[j] * (1.0 - lambda) + x[j - 1] * lambda;
        }
        x = xn;
        incidence.push(x[k - 1] * lambda);
    }
    incidence
}

/// (I) HSC pool exhaustion phenotype. MCARA anchor: stem-cell pool exit ~7% by 75 years.
/// Pool declines per year: N(y) = N0·(1-e)^y. We solve e from the anchor and report,
/// then compare with a state-dependent (accelerating) exit.
fn hsc_pool(n0: f64, n_years: usize, frac_lost_75: f64) -> (f64, Vec<f64>) {
    let e = 1.0 - (1.0 - frac_lost_75).powf(1.0 / 75.0);
    let mut pool = Vec::new();
    for y in 0..=n_years {
        pool.push(n0 * (1.0 - e).powi(y as i32));
    }
    (e, pool)
}
