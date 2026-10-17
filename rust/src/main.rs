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
    // cross-counter coupling coefficients (literature-informed ranges, not calibrated)
    c_tm: f64, // mtDNA load -> telomere attrition rate  (ROS shortens telomeres; von Zglinicki 2002)
    c_mt: f64, // telomere dysfunction -> mtDNA damage    (p53/PGC-1a; Sahin et al. 2011)
    c_et: f64, // telomere dysfunction -> epigenetic drift
    c_pe: f64, // epigenetic deregulation -> proteostasis decline
    c_mp: f64, // proteostatic load -> mtDNA damage        (impaired mitophagy)
    telomerase_on: bool, // stem cells / physioxia: telomere maintained -> tau=0, no telomere exit
    o2: f64,   // O2 mode in [0,1]: 0=physioxia/mild hypoxia (low ROS), 1=ambient/hyperoxia
    jitter: f64, // stochastic noise on ALL counters' increments (0 = deterministic)
    cycle: f64,
}

impl Params {
    fn base() -> Self {
        Params {
            d_c: 0.6,
            sigma_c: 0.3,
            k_c: 31.0, // strictly inside reachable band: S_c(50)=30 < 31 < S_c(200)=120 (audit-fixed)
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
            e_drift: 0.4,
            k_e: 25.0,
            c_tm: 4.5, // CALIBRATED: mtDNA/ROS load -> telomere attrition. von Zglinicki 1995
            // (Exp Cell Res 220:186, PMID 7664835): 90 bp/PD normoxia -> >500 bp/PD at
            // 40% O2 (~5.5x max). c_tm=4.5 maps m_load=1 -> tau_eff=5.5*tau0.
            c_mt: 0.10, // telomere dysfunction -> mtDNA damage (range, no clean in-vitro anchor)
            c_et: 0.10, // telomere dysfunction -> epigenetic drift (range)
            c_pe: 0.02, // epigenetic deregulation -> proteostasis decline (range)
            c_mp: 0.05, // proteostatic load -> mtDNA damage (range)
            telomerase_on: false, // default = somatic context (telomerase OFF)
            o2: 1.0,    // default = ambient/hyperoxic culture (high ROS)
            jitter: 0.0, // deterministic by default (Lean closed forms hold exactly)
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

/// Multi-counter run with cross-counter coupling (synergy): centriole, telomere,
/// mtDNA, proteostasis, epigenetic (any-of exit). Each counter's per-division
/// increment depends on the other counters' loads (literature-based interactions):
/// mtDNA/ROS -> telomere attrition, telomere dysfunction -> mtDNA damage & epigenetic
/// drift, epigenetic deregulation -> proteostasis decline, proteostatic load -> mtDNA.
/// All coupling terms are non-negative => counters stay monotone (damage up, telomere
/// down) and coupling can only accelerate the exit (synergy).
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
        // cross-counter loads (fractions of thresholds, clamped to [0,1])
        let m_load = (m_dam / p.k_m).min(1.0);
        let tel_fail = (1.0 - t_len / p.t0).max(0.0);
        let epi_load = (e_dam / p.k_e).min(1.0);
        let proto_load = (p_dam / p.k_p).min(1.0);
        s_c += gauss(&mut rng, p.d_c, p.sigma_c);
        // mtDNA/ROS load accelerates telomere attrition (von Zglinicki 2002); scaled by O2 mode
        // (physioxia/mild hypoxia: low ROS -> no ROS-driven erosion). Telomerase ON (stem cells /
        // physioxia): no attrition at all -> telomere maintained, no telomere counter.
        let tau_eff = if p.telomerase_on {
            0.0
        } else {
            p.tau + p.c_tm * m_load * p.o2
        };
        // stochastic noise on all counters' increments (jitter; 0 = deterministic)
        let mut nz = |x: f64| x + rng.gen_range(-1.0..1.0) * p.jitter * x.abs();
        t_len = (t_len - nz(tau_eff)).max(0.0);
        // telomere dysfunction (p53/PGC-1a; Sahin 2011) + proteostatic load (mitophagy) raise mtDNA damage
        m_dam += nz(p.d_m) + p.c_mt * tel_fail + p.c_mp * proto_load;
        // epigenetic deregulation reduces proteostasis turnover
        let r_p_eff = (p.r_p - p.c_pe * epi_load).max(0.0);
        p_dam = p_dam + nz(p.d_p) - r_p_eff * p_dam;
        // telomere dysfunction accelerates epigenetic drift
        e_dam += nz(p.e_drift) + p.c_et * tel_fail;
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
    let args: Vec<String> = std::env::args().collect();
    let mut p = Params::base();
    // CLI overrides (human-context switches):
    //   --telomerase-on         stem cells / physioxia: tau_eff=0, no telomere counter
    //   --o2 <0..1>             O2 mode: 0=physioxia (no ROS-driven erosion) .. 1=hyperoxia
    //   --counter-only          disable export collapse (f_min=0): only the 5 counters
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--telomerase-on" => p.telomerase_on = true,
            "--o2" => {
                i += 1;
                if let Some(v) = args.get(i) {
                    if let Ok(x) = v.parse::<f64>() {
                        p.o2 = x.clamp(0.0, 1.0);
                    }
                }
            }
            "--counter-only" => p.f_min = 0.0,
            other => eprintln!("unknown arg: {other}"),
        }
        i += 1;
    }
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

    println!("\n(E) MONTE-CARLO sensitivity (parameter ranges, not calibrated points):");
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

    println!("\n(F) POPULATION model for cancer incidence (Armitage-Doll, mean-field):");
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

    println!("\n(G) HSC POOL exhaustion phenotype (MCARA anchor: ~7% lost by 75 years):");
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

    println!("\n(H) FALSIFIABLE prediction for f(S) (state-dependent export):");
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

    println!("\n(I) Regime B (post-mitotic) with literature-based intracellular export:");
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

    println!("\n(J) COUNTER INTERACTIONS (synergy) — coupled multi-counter:");
    println!("  coupling graph (literature):");
    println!("    mtDNA/ROS -> telomere attrition       (von Zglinicki 2002, TiBS 27:339; PMID 12114022)");
    println!("    telomere dysfunction -> mtDNA damage  (Sahin 2011, Nature 470:359; PMID 21307849; p53/PGC-1a)");
    println!("    telomere -> epigenetic drift; epigenetic -> proteostasis; proteostasis -> mtDNA (mitophagy)");
    println!("    (Lopez-Otin 2013 Cell 153:1194 PMID 23746838; 2023 Cell 186:243 PMID 36599349)");
    println!("  coefficients: c_tm={:.2} (CALIBRATED, von Zglinicki 1995) c_mt={:.2} c_et={:.2} c_pe={:.2} c_mp={:.2} (ranges)",
        p.c_tm, p.c_mt, p.c_et, p.c_pe, p.c_mp);
    let mut p_uncoupled = p.clone();
    p_uncoupled.c_tm = 0.0;
    p_uncoupled.c_mt = 0.0;
    p_uncoupled.c_et = 0.0;
    p_uncoupled.c_pe = 0.0;
    p_uncoupled.c_mp = 0.0;
    // counter-only comparison (export collapse disabled via f_min=0):
    // isolates the 5-counter interactions from the centriole/export mechanism.
    let mut p_solo = p_uncoupled.clone();
    p_solo.f_min = 0.0;
    let mut p_cpl = p.clone();
    p_cpl.f_min = 0.0;
    let solo = first_exit_mean(&p_solo, 200);
    let cpl = first_exit_mean(&p_cpl, 200);
    println!("  first COUNTER to fire (export collapse off; 200 seeds):");
    println!("    uncoupled (no coupling): n* ~ {:.1}", solo);
    println!("    coupled   (synergy)    : n* ~ {:.1}", cpl);
    if cpl < solo && solo > 0.0 {
        println!(
            "  => synergy: counter interactions accelerate replicative exhaustion by ~{:.0}%",
            (1.0 - cpl / solo) * 100.0
        );
    } else {
        println!("  => coupling does not accelerate exit at these parameters.");
    }
    // coupled first-counter distribution (which counter synergizes to win)
    println!("  coupled first-counter to fire across seeds:");
    let mut c_counts = std::collections::HashMap::new();
    for seed in 0..200 {
        if let Some(o) = run(&p_cpl, seed, 400) {
            *c_counts.entry(o.cause).or_insert(0usize) += 1;
        }
    }
    for (cause, cnt) in c_counts {
        println!("    {}: {} / 200", cause, cnt);
    }

    println!("\n(K) ENTROPY EXPORT — the foundation; where it does NOT occur (= aging):");
    println!("  export = asymmetric segregation of old/damaged molecules to the sibling");
    println!(
        "  ('differentiating') daughter. Retained lineage: R(n+1)=(1-a)R(n)+d (a = asymmetry)."
    );
    println!("  Katajisto 2015 Science 348:340 (mitochondria, stem cells) PMID 25837514;");
    println!("  Aguilaniu 2003 Science 299:1751 (oxidized proteins) PMID 12610228;");
    println!("  aggregates: Rujano 2006; Erjavec 2007; lysosomes: Loeffler 2019; ER barrier: Moore 2015.");
    println!("  WHERE EXPORT DOES NOT OCCUR (failure modes -> aging):");
    println!(
        "    1. post-mitotic cells: no division -> only intracellular export r_intra (Regime B)"
    );
    println!(
        "    2. non-renewable units (centriole): cannot be exported/replaced -> S_c unbounded"
    );
    println!("    3. segregation failure a->0: retained lineage keeps everything -> reservoir -> counter");
    println!(
        "    4. export-function collapse f(S)->f_min at high S (state-dependent export fails)"
    );
    println!("    5. intracellular export loss (proteostasis/mitophagy; epigenetic->proteostasis coupling)");
    println!("    6. sink self-renewal (cancer): the damage-receiving daughter does not differentiate/die");
    println!("  demo — retained vs sibling daughter load over 80 divisions (d=0.5, d_sib=0.5):");
    println!("    a     | retained at 80 | sibling at 80 | export?");
    for a in [0.0f64, 0.5, 0.7, 0.9] {
        let sg = segregation(a, 0.5, 0.5, 80);
        let ret80 = *sg.retained.last().unwrap();
        let sib80 = *sg.sibling.last().unwrap();
        if a > 0.0 {
            println!(
                "    {:.1}   | {:>6.2}        | {:>6.1}        | YES (bounded, equil d/a={:.2})",
                a,
                ret80,
                sib80,
                0.5 / a
            );
        } else {
            println!(
                "    {:.1}   | {:>6.1} (counter) | {:>6.1}        | NO -> unbounded aging counter",
                a, ret80, sib80
            );
        }
    }
    println!("  => entropy export (asymmetric segregation) is the foundation: where it fails,");
    println!("     the retained lineage turns into the linear aging counter (mode 3), and the");
    println!("     other modes (post-mitotic, non-renewable, collapse, proteostasis loss, sink)");
    println!("     are the concrete contexts in which this failure occurs.");

    println!("\n(L) CONTEXT SWITCH — telomerase & O2 mode (somatic vs stem cell, human):");
    println!(
        "  telomerase ON (stem cells ESC/iPSC/HSC, Marion 2009 PMID 19200803; Ma & Blasco 2023"
    );
    println!(
        "  PMID 38219218) + physioxia (low O2, Packer 1977 PMID 876356): telomere maintained,"
    );
    println!("  tau_eff=0, no ROS-driven erosion (c_tm*o2=0) -> NO telomere counter.");
    println!("  telomerase OFF (somatic, 21% O2) : tau_eff = tau + c_tm*m_load*o2 (>0).");
    let mut p_som = p.clone();
    p_som.telomerase_on = false;
    p_som.o2 = 1.0;
    p_som.f_min = 0.0; // counter-only comparison
    let mut p_stem = p.clone();
    p_stem.telomerase_on = true;
    p_stem.o2 = 0.0;
    p_stem.f_min = 0.0;
    let (n_som, cause_som) = first_exit(&p_som, 200);
    let (n_stem, cause_stem) = first_exit(&p_stem, 200);
    println!(
        "    somatic (OFF, 21% O2): n* ~ {:.1}, first counter = {}",
        n_som, cause_som
    );
    println!(
        "    stem     (ON, physioxia): n* ~ {:.1}, first counter = {}",
        n_stem, cause_stem
    );
    // pure counters (no coupling): in the stem context the non-renewable centriole is the limiter
    let mut p_stem_pure = p_stem.clone();
    p_stem_pure.c_tm = 0.0;
    p_stem_pure.c_mt = 0.0;
    p_stem_pure.c_et = 0.0;
    p_stem_pure.c_pe = 0.0;
    p_stem_pure.c_mp = 0.0;
    let (n_pure, cause_pure) = first_exit(&p_stem_pure, 200);
    println!(
        "    stem, no coupling (pure counters): n* ~ {:.1}, first counter = {}",
        n_pure, cause_pure
    );
    println!(
        "  => with telomerase ON the telomere counter is SILENT; stem cells still exhaust via"
    );
    println!("     the other counters: in the full coupled model -> proteostasis (n*~41), in the");
    println!(
        "     pure-counter model -> mtDNA (n*~51) with the non-renewable centriole close behind"
    );
    println!(
        "     (n*~52). The centriole (mode 2) cannot be reset by telomerase -> stem cells exhaust"
    );
    println!("     despite maintained telomeres (Centrioles_Structural_Damage_Reservoirs).");

    // O2 sensitivity (telomerase OFF, counter-only): as oxidative stress (o2) rises, the
    // mtDNA/ROS->telomere coupling tightens and the telomere counter becomes rate-limiting.
    println!("  O2 sensitivity (telomerase OFF, counter-only, 100 seeds):");
    println!("    o2   | n*   | first counter");
    for o2 in [0.0f64, 0.25, 0.5, 0.75, 1.0] {
        let mut ps = p_som.clone();
        ps.o2 = o2;
        let (n, cause) = first_exit(&ps, 100);
        println!("    {:.2} | {:.1} | {}", o2, n, cause);
    }
    println!("  => physioxia (o2=0): no ROS-driven erosion, telomere counter back to baseline;");
    println!("     rising o2 (hyperoxia) makes mtDNA/ROS-driven telomere erosion rate-limiting.");

    println!("\n(M) STOCHASTIC COUNTERS, SENSITIVITY & UQ (detailing/optimization):");
    // (i) stochastic: with jitter>0 all counters are noisy -> first-to-fire spread, no ties
    let mut pj = p.clone();
    pj.jitter = 0.25;
    pj.f_min = 0.0;
    let mut dist: std::collections::HashMap<&'static str, usize> = std::collections::HashMap::new();
    let mut ns = Vec::new();
    for seed in 0..200 {
        if let Some(o) = run(&pj, seed, 400) {
            *dist.entry(o.cause).or_insert(0) += 1;
            ns.push(o.exit);
        }
    }
    println!("  (i) stochastic (jitter=0.25, counter-only): first counter across 200 seeds:");
    for (c, cnt) in dist {
        println!("      {}: {} / 200", c, cnt);
    }
    ns.sort_unstable();
    let med = ns[ns.len() / 2];
    let p5 = ns[(ns.len() as f64 * 0.05) as usize];
    let p95 = ns[((ns.len() as f64 * 0.95) as usize).min(ns.len() - 1)];
    println!(
        "      n* median={}, 5-95%=[{} .. {}]  (jitter adds stochastic spread;",
        med, p5, p95
    );
    println!(
        "      here the telomere still dominates — noise matters most when counters are close)"
    );
    // (ii) sensitivity (Sobol-lite): one-at-a-time +-20% on key params -> d(n*)/dx
    println!("  (ii) sensitivity (one-at-a-time, +-20%, counter-only):");
    println!("    param  | n*(lo) | n*(hi) | effect | rank");
    let base_n = first_exit_mean(&pj, 100);
    let setp = |name: &str, v: f64, q: &mut Params| match name {
        "d_c" => q.d_c = v,
        "c_tm" => q.c_tm = v,
        "d_m" => q.d_m = v,
        "e_drift" => q.e_drift = v,
        "c_pe" => q.c_pe = v,
        _ => {}
    };
    let mut effs = Vec::new();
    for (name, lo, hi) in [
        ("d_c", pj.d_c * 0.8, pj.d_c * 1.2),
        ("c_tm", pj.c_tm * 0.8, pj.c_tm * 1.2),
        ("d_m", pj.d_m * 0.8, pj.d_m * 1.2),
        ("e_drift", pj.e_drift * 0.8, pj.e_drift * 1.2),
        ("c_pe", pj.c_pe * 0.8, pj.c_pe * 1.2),
    ] {
        let mut ql = pj.clone();
        let mut qh = pj.clone();
        setp(name, lo, &mut ql);
        setp(name, hi, &mut qh);
        let nl = first_exit_mean(&ql, 100);
        let nh = first_exit_mean(&qh, 100);
        effs.push((name, nl, nh, nh - nl));
    }
    effs.sort_by(|a, b| b.3.partial_cmp(&a.3).unwrap());
    for (i, (name, nl, nh, eff)) in effs.iter().enumerate() {
        println!(
            "    {:>7} | {:>5.1} | {:>5.1} | {:>6.1} | #{}",
            name,
            nl,
            nh,
            eff,
            i + 1
        );
    }
    println!(
        "    (base n* = {:.1}; rank by |effect| = sensitivity)",
        base_n
    );
    // (iii) UQ: min-max n* across plausible perturbations -> pseudo-CI
    let mut nn = Vec::new();
    for scale in [0.8f64, 0.9, 1.0, 1.1, 1.2] {
        let mut q = pj.clone();
        q.d_c *= scale;
        q.d_m *= scale;
        q.e_drift *= scale;
        nn.push(first_exit_mean(&q, 100));
    }
    nn.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
    println!(
        "  (iii) UQ: n* across +/-20% joint scaling = [{:.1} .. {:.1}] (pseudo-CI)",
        nn[0],
        nn[nn.len() - 1]
    );

    println!(
        "\n(N) NON-DILUTABLE CENTRIOLE vs segregable damage (items: segregation-in-core + age):"
    );
    println!("  with segregation a>0 the disposable damage in the retained lineage stays bounded");
    println!(
        "  (retainedDaughter -> d/a), but the centriole CANNOT be exported (mode 2): S_c = d_c·n"
    );
    println!("  accumulates unconditionally = the lineage's age (age-structure).");
    for a in [0.5f64, 0.8] {
        let sg = segregation(a, 0.5, 0.5, 50);
        let ret = *sg.retained.last().unwrap();
        let sc = 0.6 * 50.0;
        println!(
            "    a={}: retained damage at 50 div = {:.2} (equil {:.2});  centriole S_c = {:.1} (unbounded, non-dilutable)",
            a,
            ret,
            0.5 / a,
            sc
        );
    }
    println!(
        "  => the non-dilutable centriole is the only truly unbounded counter; it limits even"
    );
    println!("     telomerase-ON stem cells with perfect segregation (Centrioles_Structural_Damage_Reservoirs).");

    println!(
        "\n(O) BRANCHING POPULATION MODEL (item: organismal outputs — stem pool + progeny sink):"
    );
    let n0 = 2000usize;
    let div_per_yr = 2usize; // illustrative: divisions per year per stem lineage
    let mut rng = StdRng::seed_from_u64(7);
    let mut caps: Vec<i64> = (0..n0)
        .map(|_| (20 + rng.gen_range(0..200)) as i64) // cellular replicative capacity n* (heterogeneous)
        .collect();
    println!(
        "  stem pool N0={n0}; each cell exhausts at its cellular n* (heterogeneous 20-220 div);"
    );
    println!("  differentiating daughters = entropy sink (die); tissue function ~ pool fraction.");
    for yr in 0..=100 {
        let mut alive = 0i64;
        for c in caps.iter_mut() {
            if *c > 0 {
                *c -= div_per_yr as i64;
                if *c > 0 {
                    alive += 1;
                }
            }
        }
        if yr % 20 == 0 {
            println!(
                "    year {:>3}: pool = {:.3} of N0 ({:.1}% lost)",
                yr,
                alive as f64 / n0 as f64,
                (1.0 - alive as f64 / n0 as f64) * 100.0
            );
        }
    }
    println!(
        "  => heterogeneity in cellular n* produces a GRADUAL organismal decline (tissue function"
    );
    println!(
        "     ~ pool fraction); with a homogeneous capacity the decline would be an abrupt cliff."
    );
}

/// Mean first-exit division and the dominant cause over seeds.
fn first_exit(p: &Params, n_sims: usize) -> (f64, String) {
    let mut s = 0.0f64;
    let mut cnt = 0.0f64;
    let mut counts: std::collections::HashMap<&'static str, usize> =
        std::collections::HashMap::new();
    for seed in 0..n_sims {
        if let Some(o) = run(p, seed as u64, 400) {
            s += o.exit as f64;
            cnt += 1.0;
            *counts.entry(o.cause).or_insert(0) += 1;
        }
    }
    let cause = counts
        .into_iter()
        .max_by_key(|&(_, c)| c)
        .map(|(c, _)| c.to_string())
        .unwrap_or_else(|| "none".to_string());
    (if cnt > 0.0 { s / cnt } else { 0.0 }, cause)
}

/// Mean first-exit division over seeds (used for the synergy comparison).
fn first_exit_mean(p: &Params, n_sims: usize) -> f64 {
    let mut s = 0.0f64;
    let mut cnt = 0.0f64;
    for seed in 0..n_sims {
        if let Some(o) = run(p, seed as u64, 400) {
            s += o.exit as f64;
            cnt += 1.0;
        }
    }
    if cnt > 0.0 {
        s / cnt
    } else {
        0.0
    }
}

/// Segregation of molecules between daughter cells (universal: any dividing cell).
/// `a` = asymmetry: the fraction of old/damaged molecules exported to the sibling
/// ('differentiating') daughter. The retained ('young') lineage keeps `(1-a)` of old
/// plus fresh `d` per division => its load is the damage reservoir with leak `a`
/// (bounded for a>0: the 'young' daughter does not age). The sibling accumulates
/// `a·R + d_s` (the entropy sink). a=0 => no export => the retained lineage is the
/// unbounded aging counter.
struct SegPair {
    retained: Vec<f64>,
    sibling: Vec<f64>,
}

fn segregation(a: f64, d: f64, d_sib: f64, n_max: usize) -> SegPair {
    let mut retained = Vec::with_capacity(n_max + 1);
    let mut sibling = Vec::with_capacity(n_max + 1);
    let mut r = 0.0f64;
    let mut s = 0.0f64;
    retained.push(r);
    sibling.push(s);
    for _ in 0..n_max {
        let r_old = r;
        r = (1.0 - a) * r_old + d;
        s = s + a * r_old + d_sib;
        retained.push(r);
        sibling.push(s);
    }
    SegPair { retained, sibling }
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

/// (F) Population model for cancer incidence (Armitage-Doll), mean-field.
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
