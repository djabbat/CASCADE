# CASCADE — Counter-based Asymmetric Stem-Cell Aging: Division Counters & Entropy Export

A quantitative model of **organismal aging** built on the stem-cell-centric
multi-counter theory: asymmetric division exports entropy/damage, division counters
(centriole, telomeres, mtDNA, proteostasis, epigenetic mitotic clock) accumulate, and
self-renewal declines as the organismal damage load grows (positive feedback = aging).

```
L_{n+1} = α·L_n + (1−α)·L_0 + μ + ε_n,          α ≈ 0.97     (geometric aging)
r_L(t)  = r_L0 · exp(−κ_L · S_org(t))                        (renewal decline)
S_org(t)= Σ w_L·f_L(t) + w_c·min(1, S_c/K_c)                 (organismal load)
```

## Two verified implementations

- **Lean 4 + Mathlib** (`lean/`) — formally machine-checked mathematical core, 0 errors:
  - `CASCADE.lean` — geometric aging as a division counter: closed forms, variance
    accumulation (persistence), strict monotonicity (counter function), finite equilibria.
  - `CASCADE_Core.lean` — damage-reservoir counter, multi-hit, Armitage–Doll incidence,
    self-renewal decline → entropy, falsifiable export `f(S)=f₀·e^(−kS)`.
- **Rust** (`rust/`) — stochastic multi-counter simulation (sections A–K):
  `counter_model`, `audit_cycles`, `pubmed_verify` (NCBI E-utilities).

## Key outputs (parameter ranges, not calibration)

| Section | Result |
|---|---|
| Organismal aging | self-renewal decline of long-lived proteins 49% over 80 divisions |
| Multi-counter | replicative limit n* = 15–45 (Monte-Carlo) |
| Meiotic bottleneck | counters reset between generations; β-leak → parental-age effect |
| Diploidy | two-hit buffer: haploid n*≈9 vs diploid n*≈66 |
| Cancer (Armitage–Doll) | incidence slope ≈ t⁴⁻⁵, k=6 — reproduces the curve |
| HSC pool | ~7% lost by age 75 (matches MCARA anchor) |

## Falsifiable predictions
1. In asymmetric division the exported-damage fraction decays exponentially:
   `f(S)=f₀·e^(−kS)` — falsified if `f` is constant or non-monotone in `S`.
2. Self-renewal rates of long-lived proteins/organelles decline with age (measurable).
3. Meiotic reset of centriole and telomere counters; β-leak predicts parental-age
   effects (mtDNA maternal; telomeres/centriole paternal).
4. Diploid replicative capacity ≈ 2× haploid (two-hit buffer); LOH accelerates exit.

## Build & run
```bash
cd rust && cargo run --bin counter_model          # model (sections A–K)
cd rust && cargo run --bin pubmed_verify -- batch # PubMed evidence base
# Lean: needs Lean 4 + Mathlib
lean CASCADE.lean          # ~1 min, 0 errors
lean CASCADE_Core.lean
```

## DOI
**Zenodo: https://doi.org/10.5281/zenodo.23417047** (v0.4.0) · concept DOI 10.5281/zenodo.23417046

## Citation
See `CITATION.cff`. Author: Jaba Tqemaladze (ORCID 0000-0001-8651-7243).
License: Apache-2.0.
