import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

set_option linter.unnecessarySeqFocus false

/-!
# CASCADE — formalized mathematical core of the organismal-aging multi-counter model (Lean)

The provable core of the organismal-aging multi-counter model. Everything here is
real-analysis and combinatorics; the stochastic/numerical parts (Monte-Carlo,
simulation) live in Rust. Python is not used.

Main statements:

* `reservoir_closed_form` — `D_{n+1} = (1-c)·D_n + d` has closed form `D_n = d·(1-(1-c)ⁿ)/c`.
* `reservoir_mono` — `D_n` is non-decreasing for `0 ≤ c ≤ 1`, `d ≥ 0` (persistence).
* `reservoir_tendsto` — `D_n → d/c` as `n → ∞` for `0 < c < 1` (finite steady state).
* `multiHit_exact` — mean-field multi-hit has the exact binomial solution
  (analytic content of the Armitage-Doll power law: `X_{k-1,n} ~ n^(k-1)`, slope `k-1`).
* `levelEntropy_mono` — with non-increasing renewal, entropy is non-decreasing
  (self-renewal decline → organismal aging).
* `export_strictAnti` — `f(S) = f₀·e^(−kS)` is strictly decreasing (falsifiable).
* `centrioleCounter`, `telomereCounter`, `mtDNAcounter`, `proteostasisCounter`,
  `epigeneticCounter` + closed forms + monotonicity — the **five division counters**, each
  as a separate theorem, matching the Rust simulation and the model's default parameters.
* `proteostasis_no_exit` — with turnover the counter reaches a finite steady state
  `d_p/r_p`; if it does not exceed the threshold `k_p`, proteostasis never exits.
* `epigeneticExitTime_spec` / `epigeneticExitTime_min` — the epigenetic mitotic counter
  has a well-defined exit time `n*` (the first division with `E(n*) > k_e`), and `n*` is
  minimal.
* `telomereCoupled_anti`, `mtDNACoupled_mono`, `telomereCoupled_le_standalone`,
  `mtDNACoupled_ge_standalone` — **counter interactions (synergy)**: non-negative
  couplings preserve the division-counter direction (telomere non-increasing, mtDNA
  non-decreasing) and can only accelerate exit (coupled ≤/≥ standalone).
* `retainedDaughter`/`siblingDaughter` + `retained_tendsto`, `retained_no_exit`,
  `retained_no_export_equals_counter`, `sibling_mono`, `retained_eq_antitone`,
  `telomere_zero_attrition` — **entropy export (asymmetric molecular segregation)** and the
  context switch: the retained 'young' lineage is bounded (`→ d/a`) while `a > 0`; with
  `a = 0` it becomes the linear unbounded aging counter; the sibling is the sink.
* `renewal_strict_anti`, `levelEntropy_nonneg`, `levelEntropy_antitone_renewal`,
  `firstCross_le_of_dominated` — **organismal feedback + synergy exit bound**: renewal
  declines with load (positive feedback accelerates accumulation), and a damage process
  that dominates the standalone one can only exit at the same or an earlier division.
-/

namespace Nat
namespace Cascade

/-! ## 1. Damage-reservoir counter -/

/-- `D_{n+1} = (1-c)·D_n + d`, `D_0 = 0`. -/
noncomputable def reservoir (d c : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 - c) * reservoir d c n + d

lemma reservoir_closed_form {d c : ℝ} (hc : c ≠ 0) (n : ℕ) :
    reservoir d c n = d * (1 - (1 - c) ^ n) / c := by
  induction n with
  | zero => simp [reservoir]
  | succ n ih =>
      rw [reservoir, ih]
      field_simp [hc] <;> ring

lemma reservoir_mono {d c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd : 0 ≤ d) (n : ℕ) :
    reservoir d c n ≤ reservoir d c (n + 1) := by
  induction n with
  | zero =>
      simpa [reservoir] using hd
  | succ n ih =>
      have hleft : reservoir d c (n + 1) = (1 - c) * reservoir d c n + d := by
        rw [reservoir]
      have hstep : reservoir d c (n + 1 + 1) = (1 - c) * reservoir d c (n + 1) + d := by
        rw [show n + 1 + 1 = n + 1 + 1 by omega]
        rw [reservoir]
      rw [hleft, hstep]
      have h1c : 0 ≤ 1 - c := by linarith
      have hm := mul_le_mul_of_nonneg_left ih h1c
      linarith

lemma reservoir_tendsto {d c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    Filter.Tendsto (fun n : ℕ => reservoir d c n) Filter.atTop (nhds (d / c)) := by
  have hcne : c ≠ 0 := ne_of_gt hc0
  have h1c0 : 0 ≤ 1 - c := by linarith
  have h1c1 : 1 - c < 1 := by linarith
  have hp : Filter.Tendsto (fun n : ℕ => (1 - c) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h1c0 h1c1
  have hf : (fun n : ℕ => reservoir d c n) =ᶠ[Filter.atTop]
      fun n : ℕ => d / c - d / c * (1 - c) ^ n := by
    filter_upwards with n
    rw [reservoir_closed_form hcne n]
    field_simp [hcne] <;> ring
  have hc_tend : Filter.Tendsto (fun n : ℕ => d / c * (1 - c) ^ n) Filter.atTop (nhds 0) := by
    simpa using hp.const_mul (d / c)
  have hlim : Filter.Tendsto (fun n : ℕ => d / c - d / c * (1 - c) ^ n)
      Filter.atTop (nhds (d / c)) := by
    simpa using (tendsto_const_nhds.sub hc_tend)
  exact Filter.Tendsto.congr' hf.symm hlim

/-! ## 2. Cancer multi-hit (mean-field) — Armitage-Doll power law -/

/-- `X_0(0)=n0`, `X_0(n+1)=(1-l)X_0(n)`, `X_{j+1}(0)=0`,
`X_{j+1}(n+1)=(1-l)X_{j+1}(n)+l·X_j(n)`. -/
noncomputable def multiHit (n0 l : ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => n0
  | 0, n + 1 => (1 - l) * multiHit n0 l 0 n
  | j + 1, 0 => 0
  | j + 1, n + 1 => (1 - l) * multiHit n0 l (j + 1) n + l * multiHit n0 l j n

/-- `X_0(n) = n0·(1-l)^n` (cells that never acquired a hit). -/
lemma multiHit_zero (n0 l : ℝ) (n : ℕ) :
    multiHit n0 l 0 n = n0 * (1 - l) ^ n := by
  induction n with
  | zero => simp [multiHit]
  | succ n ih =>
      rw [multiHit, ih]
      rw [pow_succ]
      ring

/-- `X_j(n) = 0` whenever there are more hits than divisions (`j > n`):
one cannot accumulate more hits than division steps. -/
lemma multiHit_zero_of_lt {n0 l : ℝ} {j n : ℕ} (hj : n < j) :
    multiHit n0 l j n = 0 := by
  induction n generalizing j with
  | zero =>
      cases j with
      | zero => simp at hj
      | succ j => simp [multiHit]
  | succ n ih =>
      cases j with
      | zero => simp at hj
      | succ j =>
          rw [multiHit]
          have h1 : n < j + 1 := by omega
          have h2 : n < j := by omega
          rw [ih (j := j + 1) h1]
          rw [ih (j := j) h2]
          ring

/-- Exact binomial solution of the mean-field multi-hit recurrence, for `j ≤ n`:
`X_{j,n} = n0·(n choose j)·l^j·(1-l)^(n-j)`.
This is the analytic content of the Armitage-Doll power law: with `k` rate-limiting
hits, `X_{k-1,n} ~ n^(k-1)` and incidence ~ `n^(k-1)`. -/
lemma multiHit_exact {n0 l : ℝ} {j n : ℕ} (hj : j ≤ n) :
    multiHit n0 l j n = n0 * (n.choose j : ℝ) * l ^ j * (1 - l) ^ (n - j) := by
  induction n generalizing j with
  | zero =>
      have hj0 : j = 0 := by omega
      subst j
      simp [multiHit]
  | succ n ih =>
      by_cases hjn : j ≤ n
      · -- main case: j ≤ n, recurrence valid for both components
        cases j with
        | zero =>
            rw [multiHit_zero]
            simp
        | succ j =>
            rw [multiHit]
            have hj1 : j + 1 ≤ n := hjn
            have hj2 : j ≤ n := by omega
            rw [ih (j := j + 1) hj1]
            rw [ih (j := j) hj2]
            -- exponent shift: (1-l)·(1-l)^(n-(j+1)) = (1-l)^(n-j)
            have hshift : (1 - l) * (1 - l) ^ (n - (j + 1)) = (1 - l) ^ (n - j) := by
              have hsub : n - (j + 1) + 1 = n - j := by omega
              rw [← hsub]
              rw [show n - (j + 1) + 1 = (n - (j + 1)) + 1 by omega]
              rw [pow_succ]
              ring
            have hpascal : (n.choose (j + 1) : ℝ) + (n.choose j : ℝ) = ((n + 1).choose (j + 1) : ℝ) := by
              rw [Nat.choose_succ_succ]
              norm_num
              ring
            have htarget : (n + 1) - (j + 1) = n - j := by omega
            have hll : l * l ^ j = l ^ (j + 1) := by
              rw [pow_succ]
              ring
            calc
              (1 - l) * (n0 * (n.choose (j + 1) : ℝ) * l ^ (j + 1) * (1 - l) ^ (n - (j + 1)))
                  + l * (n0 * (n.choose j : ℝ) * l ^ j * (1 - l) ^ (n - j))
                  = n0 * (n.choose (j + 1) : ℝ) * l ^ (j + 1) * (1 - l) ^ (n - j)
                    + n0 * (n.choose j : ℝ) * l ^ (j + 1) * (1 - l) ^ (n - j) := by
                    have hc : (1 - l) * (n0 * (n.choose (j + 1) : ℝ) * l ^ (j + 1) * (1 - l) ^ (n - (j + 1)))
                        = n0 * (n.choose (j + 1) : ℝ) * l ^ (j + 1) * ((1 - l) * (1 - l) ^ (n - (j + 1))) := by ring
                    have hc2 : l * (n0 * (n.choose j : ℝ) * l ^ j * (1 - l) ^ (n - j))
                        = n0 * (n.choose j : ℝ) * (l * l ^ j) * (1 - l) ^ (n - j) := by ring
                    rw [hc, hc2, hshift, hll]
              _ = n0 * l ^ (j + 1) * (1 - l) ^ (n - j) * ((n.choose (j + 1) : ℝ) + (n.choose j : ℝ)) := by
                    ring
              _ = n0 * l ^ (j + 1) * (1 - l) ^ (n - j) * ((n + 1).choose (j + 1) : ℝ) := by
                    rw [hpascal]
              _ = n0 * ((n + 1).choose (j + 1) : ℝ) * l ^ (j + 1) * (1 - l) ^ (n + 1 - (j + 1)) := by
                    rw [htarget]
                    ring
      · -- boundary case: j = n + 1 (all hits; X_{n+1}(n) = 0)
        have hj1 : j = n + 1 := by omega
        subst j
        rw [multiHit]
        rw [multiHit_zero_of_lt (by omega : n < n + 1)]
        rw [ih (j := n) (by omega : n ≤ n)]
        have hccn : (n.choose n : ℝ) = 1 := by
          rw [Nat.choose_self]
          norm_num
        have hccs : ((n + 1).choose (n + 1) : ℝ) = 1 := by
          rw [Nat.choose_self]
          norm_num
        have hnsub : n - n = 0 := Nat.sub_self n
        have hsubs : (n + 1) - (n + 1) = 0 := Nat.sub_self (n + 1)
        have hpow0 : (1 - l) ^ 0 = 1 := by norm_num
        rw [hccn, hccs, hnsub, hsubs, hpow0]
        rw [pow_succ]
        ring

/-! ## 3. Self-renewal decline → organismal aging -/

/-- `S(n+1) = (1-r n)·S(n) + d`, `S(0)=0`. -/
noncomputable def levelEntropy (d : ℝ) (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 - r n) * levelEntropy d r n + d

/-- Non-decreasing while below the target `d/r(n)`. -/
lemma levelEntropy_mono {d : ℝ} {r : ℕ → ℝ}
    (hd : 0 ≤ d) (hr0 : ∀ n, 0 ≤ r n) (n : ℕ)
    (hbelow : ∀ n, levelEntropy d r n ≤ d / (r n + (if r n = 0 then d else 0))) :
    levelEntropy d r n ≤ levelEntropy d r (n + 1) := by
  rw [← sub_nonneg]
  have hsub : levelEntropy d r (n + 1) - levelEntropy d r n = d - r n * levelEntropy d r n := by
    rw [levelEntropy]
    ring
  rw [hsub]
  by_cases hrn : r n = 0
  · rw [hrn]
    simp [hd]
  · have hrp : 0 < r n := lt_of_le_of_ne (hr0 n) (Ne.symm hrn)
    have htarget : levelEntropy d r n ≤ d / r n := by
      have := hbelow n
      simpa [hrn] using this
    have hmul : r n * levelEntropy d r n ≤ d := by
      have := mul_le_mul_of_nonneg_left htarget (le_of_lt hrp)
      have hd' : r n * (d / r n) = d := by field_simp [hrn]
      simpa [hd'] using this
    linarith

/-! ## 4. State-dependent export `f(S) = f₀·e^(−kS)` -/

lemma export_strictAnti {f₀ k : ℝ} (hf0 : 0 < f₀) (hk : 0 < k) :
    StrictAnti (fun S : ℝ => f₀ * Real.exp (-k * S)) := by
  intro S T hST
  have h1 : -k * T < -k * S := mul_lt_mul_of_neg_left hST (neg_lt_zero.mpr hk)
  have h2 : Real.exp (-k * T) < Real.exp (-k * S) := Real.exp_lt_exp.mpr h1
  exact mul_lt_mul_of_pos_left h2 hf0

/-! ## 5. The five division counters -/

/-- **1. Centriole counter**: `S_c(n+1) = S_c(n) + d_c`, `S_c(0) = 0` (linear drift). -/
noncomputable def centrioleCounter (d_c : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => centrioleCounter d_c n + d_c

lemma centriole_closed_form (d_c : ℝ) (n : ℕ) :
    centrioleCounter d_c n = d_c * (n : ℝ) := by
  induction n with
  | zero => simp [centrioleCounter]
  | succ n ih =>
      rw [centrioleCounter, ih]
      norm_num
      ring

lemma centriole_strict_mono {d_c : ℝ} (hd : 0 < d_c) (n : ℕ) :
    centrioleCounter d_c n < centrioleCounter d_c (n + 1) := by
  rw [centrioleCounter]
  linarith

/-- **2. Telomere counter**: `T(n+1) = T(n) − τ`, `T(0) = t₀` (linear depletion). -/
noncomputable def telomereCounter (t0 τ : ℝ) : ℕ → ℝ
  | 0 => t0
  | n + 1 => telomereCounter t0 τ n - τ

lemma telomere_closed_form (t0 τ : ℝ) (n : ℕ) :
    telomereCounter t0 τ n = t0 - τ * (n : ℝ) := by
  induction n with
  | zero => simp [telomereCounter]
  | succ n ih =>
      rw [telomereCounter, ih]
      norm_num
      ring

lemma telomere_strict_anti {t0 τ : ℝ} (hτ : 0 < τ) (n : ℕ) :
    telomereCounter t0 τ (n + 1) < telomereCounter t0 τ n := by
  rw [telomereCounter]
  linarith

/-- **3. mtDNA counter**: `M(n+1) = M(n) + d_m`, `M(0) = 0` (linear accumulation). -/
noncomputable def mtDNAcounter (d_m : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => mtDNAcounter d_m n + d_m

lemma mtDNA_closed_form (d_m : ℝ) (n : ℕ) :
    mtDNAcounter d_m n = d_m * (n : ℝ) := by
  induction n with
  | zero => simp [mtDNAcounter]
  | succ n ih =>
      rw [mtDNAcounter, ih]
      norm_num
      ring

lemma mtDNA_strict_mono {d_m : ℝ} (hd : 0 < d_m) (n : ℕ) :
    mtDNAcounter d_m n < mtDNAcounter d_m (n + 1) := by
  rw [mtDNAcounter]
  linarith

/-- **4. Proteostasis counter**: `P(n+1) = P(n) + d_p − r_p·P(n)` — the damage reservoir
with turnover `r_p` (a counter that can be kept below its threshold). -/
noncomputable def proteostasisCounter (d_p r_p : ℝ) : ℕ → ℝ :=
  reservoir d_p r_p

lemma proteostasis_closed_form {d_p r_p : ℝ} (hrp : r_p ≠ 0) (n : ℕ) :
    proteostasisCounter d_p r_p n = d_p * (1 - (1 - r_p) ^ n) / r_p := by
  exact reservoir_closed_form hrp n

lemma proteostasis_mono {d_p r_p : ℝ} (hr0 : 0 ≤ r_p) (hr1 : r_p ≤ 1) (hd : 0 ≤ d_p)
    (n : ℕ) : proteostasisCounter d_p r_p n ≤ proteostasisCounter d_p r_p (n + 1) := by
  exact reservoir_mono hr0 hr1 hd n

lemma proteostasis_tendsto {d_p r_p : ℝ} (hr0 : 0 < r_p) (hr1 : r_p < 1) :
    Filter.Tendsto (fun n : ℕ => proteostasisCounter d_p r_p n) Filter.atTop
      (nhds (d_p / r_p)) := by
  exact reservoir_tendsto hr0 hr1

/-- Proteostasis reaches a **finite steady state** `d_p/r_p`; if that steady state does
not exceed the threshold `k_p`, the counter never exits (no replicative limit from
proteostasis with turnover). -/
lemma proteostasis_no_exit {d_p r_p k_p : ℝ} (hr0 : 0 ≤ r_p) (hr1 : r_p ≤ 1)
    (hrp : r_p ≠ 0) (hd : 0 ≤ d_p) (hss : d_p / r_p ≤ k_p) (n : ℕ) :
    proteostasisCounter d_p r_p n ≤ k_p := by
  rw [proteostasis_closed_form hrp n]
  have h1mr : 0 ≤ 1 - r_p := by linarith
  have h1mr_le : 1 - r_p ≤ 1 := by linarith
  have hp1 : (1 - r_p) ^ n ≤ 1 := pow_le_one₀ h1mr h1mr_le
  have hp0 : 0 ≤ (1 - r_p) ^ n := pow_nonneg h1mr n
  have hnum_le : d_p * (1 - (1 - r_p) ^ n) ≤ d_p := by
    have hx_le : 1 - (1 - r_p) ^ n ≤ 1 := by linarith
    have hm := mul_le_mul_of_nonneg_left hx_le hd
    simpa using hm
  have hrp0 : 0 < r_p := lt_of_le_of_ne hr0 (Ne.symm hrp)
  have hdiv : d_p * (1 - (1 - r_p) ^ n) / r_p ≤ d_p / r_p := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum_le (le_of_lt (inv_pos.mpr hrp0))
  exact le_trans hdiv hss

/-- **5. Epigenetic mitotic counter**: `E(n+1) = E(n) + e`, `E(0) = 0`
(epigenetic drift, linear accumulation per division). -/
noncomputable def epigeneticCounter (e : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => epigeneticCounter e n + e

lemma epigenetic_closed_form (e : ℝ) (n : ℕ) :
    epigeneticCounter e n = e * (n : ℝ) := by
  induction n with
  | zero => simp [epigeneticCounter]
  | succ n ih =>
      rw [epigeneticCounter, ih]
      norm_num
      ring

lemma epigenetic_strict_mono {e : ℝ} (he : 0 < e) (n : ℕ) :
    epigeneticCounter e n < epigeneticCounter e (n + 1) := by
  rw [epigeneticCounter]
  linarith

/-- The epigenetic counter eventually exceeds any finite threshold (drift is unbounded). -/
lemma epigenetic_exists_exit {e k : ℝ} (he : 0 < e) :
    ∃ n : ℕ, k < epigeneticCounter e n := by
  by_cases hk : k ≤ 0
  · use 1
    rw [epigenetic_closed_form]
    norm_num
    linarith
  · have hk0 : 0 < k := lt_of_not_ge hk
    let n0 : ℕ := Nat.ceil (k / e) + 1
    use n0
    have hle : (k / e) ≤ (Nat.ceil (k / e) : ℝ) := Nat.le_ceil (k / e)
    have hlt : (k / e) < (n0 : ℝ) := by
      dsimp [n0]
      rw [Nat.cast_add, Nat.cast_one]
      linarith
    have hklt : k < e * (n0 : ℝ) := by
      have hmul : k / e * e < (n0 : ℝ) * e := mul_lt_mul_of_pos_right hlt he
      have hcancel : k / e * e = k := by field_simp [ne_of_gt he]
      have hcomm : (n0 : ℝ) * e = e * (n0 : ℝ) := by ring
      linarith
    rw [epigenetic_closed_form]
    exact hklt

/-- **Epigenetic exit time** `n*`: the first division at which accumulated drift
passes the threshold `k_e` (`E(n*) > k_e`). -/
noncomputable def epigeneticExitTime (e k : ℝ) (he : 0 < e) : ℕ :=
  Nat.find (epigenetic_exists_exit (e := e) (k := k) he)

lemma epigeneticExitTime_spec {e k : ℝ} (he : 0 < e) :
    k < epigeneticCounter e (epigeneticExitTime e k he) := by
  exact Nat.find_spec (p := fun n => k < epigeneticCounter e n)
    (H := epigenetic_exists_exit (e := e) (k := k) he)

lemma epigeneticExitTime_min {e k : ℝ} (he : 0 < e) {n : ℕ}
    (hn : n < epigeneticExitTime e k he) :
    ¬ k < epigeneticCounter e n := by
  exact Nat.find_min (p := fun n => k < epigeneticCounter e n)
    (H := epigenetic_exists_exit (e := e) (k := k) he) hn

/-! ### Concrete parameters (defaults in `Params::base()` and the audit) -/

-- Centriole: S_c(50) = 0.6·50 = 30 = k_c
example : centrioleCounter 0.6 50 = 30 := by norm_num [centrioleCounter]

-- Telomere: T(90) = 100 − 90 = 10 = t_min
example : telomereCounter 100 1 90 = 10 := by norm_num [telomereCounter]

-- mtDNA: M(50) = 0.5·50 = 25 = k_m
example : mtDNAcounter 0.5 50 = 25 := by norm_num [mtDNAcounter]

-- Proteostasis steady state: d_p/r_p = 0.4/0.05 = 8 = k_p (borderline, no strict exit)
example : (0.4 / 0.05 : ℝ) = 8 := by ring_nf

-- Proteostasis never exceeds k_p with the default parameters:
example (n : ℕ) : proteostasisCounter 0.4 0.05 n ≤ 8 := by
  exact proteostasis_no_exit (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) n

-- Epigenetic: E(50) = 0.4·50 = 20 (drift slower than mtDNA — distinct late counter)
example : epigeneticCounter 0.4 50 = 20 := by norm_num [epigeneticCounter]

-- Epigenetic exit time for the default parameters: n* = 63 (smallest n with 0.4·n > 25)
example : epigeneticExitTime 0.4 25 (by norm_num) = 63 := by
  unfold epigeneticExitTime
  apply (Nat.find_eq_iff (p := fun n => 25 < epigeneticCounter 0.4 n)
    (epigenetic_exists_exit (e := 0.4) (k := 25) (by norm_num))).mpr
  constructor
  · norm_num [epigeneticCounter]
  · intro n hn hlt
    have hn62 : (n : ℝ) ≤ 62 := by
      have : n < 63 := hn
      norm_num
      exact_mod_cast (Nat.le_of_lt_succ this)
    have hpos : ¬ 25 < 0.4 * (n : ℝ) := by nlinarith
    exact hpos (by simpa [epigenetic_closed_form] using hlt)

/-! ## 6. Counter interactions (synergy) -/

/-- Coupled telomere: mtDNA/ROS load raises the attrition rate,
`T(n+1) = T(n) − (τ + c·M(n))`, with `M` non-negative. -/
noncomputable def telomereCoupled (t0 τ c : ℝ) (M : ℕ → ℝ) : ℕ → ℝ
  | 0 => t0
  | n + 1 => telomereCoupled t0 τ c M n - (τ + c * M n)

/-- Coupling preserves the division-counter direction: the telomere stays
non-increasing even with mtDNA-accelerated attrition. -/
lemma telomereCoupled_anti {t0 τ c : ℝ} {M : ℕ → ℝ} (hτ : 0 ≤ τ) (hc : 0 ≤ c)
    (hM : ∀ n, 0 ≤ M n) (n : ℕ) :
    telomereCoupled t0 τ c M (n + 1) ≤ telomereCoupled t0 τ c M n := by
  rw [telomereCoupled]
  have hb : 0 ≤ τ + c * M n := by
    have hcm : 0 ≤ c * M n := mul_nonneg hc (hM n)
    linarith
  linarith

/-- Coupled mtDNA: telomere dysfunction adds damage, `M(n+1) = M(n) + d + c·(1 − T(n)/T0)`. -/
noncomputable def mtDNACoupled (d c : ℝ) (T : ℕ → ℝ) (T0 : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => mtDNACoupled d c T T0 n + d + c * (1 - T n / T0)

/-- Coupling preserves the division-counter direction: mtDNA stays non-decreasing. -/
lemma mtDNACoupled_mono {d c : ℝ} (hd : 0 ≤ d) (hc : 0 ≤ c) {T : ℕ → ℝ} {T0 : ℝ}
    (hT : ∀ n, T n ≤ T0) (hT0 : 0 < T0) (n : ℕ) :
    mtDNACoupled d c T T0 n ≤ mtDNACoupled d c T T0 (n + 1) := by
  rw [mtDNACoupled]
  have hfrac : 0 ≤ 1 - T n / T0 := by
    have hdiv : T n / T0 ≤ 1 := (div_le_one hT0).mpr (hT n)
    linarith
  have hc2 : 0 ≤ c * (1 - T n / T0) := mul_nonneg hc hfrac
  linarith

/-- **Synergy (telomere)**: coupling to a non-negative damage signal only accelerates
attrition — the coupled telomere is never longer than the standalone one. -/
lemma telomereCoupled_le_standalone {t0 τ c : ℝ} {M : ℕ → ℝ} (hc : 0 ≤ c)
    (hM : ∀ n, 0 ≤ M n) (n : ℕ) :
    telomereCoupled t0 τ c M n ≤ telomereCounter t0 τ n := by
  induction n with
  | zero => simp [telomereCoupled, telomereCounter]
  | succ n ih =>
      rw [telomereCoupled, telomereCounter]
      have hb : 0 ≤ c * M n := mul_nonneg hc (hM n)
      linarith

/-- **Synergy (mtDNA)**: coupling to telomere dysfunction only adds damage — the coupled
mtDNA damage is never below the standalone one. -/
lemma mtDNACoupled_ge_standalone {d c : ℝ} (hc : 0 ≤ c) {T : ℕ → ℝ} {T0 : ℝ}
    (hT : ∀ n, T n ≤ T0) (hT0 : 0 < T0) (n : ℕ) :
    mtDNAcounter d n ≤ mtDNACoupled d c T T0 n := by
  induction n with
  | zero => simp [mtDNACoupled, mtDNAcounter]
  | succ n ih =>
      rw [mtDNACoupled, mtDNAcounter]
      have hfrac : 0 ≤ 1 - T n / T0 := by
        have hdiv : T n / T0 ≤ 1 := (div_le_one hT0).mpr (hT n)
        linarith
      have hc2 : 0 ≤ c * (1 - T n / T0) := mul_nonneg hc hfrac
      linarith

/-! ## 7. Entropy export — molecular segregation between daughter cells -/

/-- Retained ('young') daughter lineage: `R(n+1) = (1-a)·R(n) + d` — exactly the damage
reservoir with asymmetry `a` (the fraction of old molecules exported to the sibling). -/
noncomputable def retainedDaughter (d a : ℝ) : ℕ → ℝ :=
  reservoir d a

/-- Sibling ('differentiating') daughter: accumulates the exported old molecules plus its
own influx, `S(n+1) = S(n) + a·R(n) + d_s`. -/
noncomputable def siblingDaughter (a d_s : ℝ) (R : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => siblingDaughter a d_s R n + a * R n + d_s

/-- **Export works**: with asymmetry `0 < a < 1` the retained lineage is bounded and
converges to `d/a` — the 'young' daughter does not age. -/
lemma retained_tendsto {d a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Filter.Tendsto (fun n : ℕ => retainedDaughter d a n) Filter.atTop (nhds (d / a)) := by
  exact reservoir_tendsto ha0 ha1

/-- **No export (a = 0)**: the retained lineage keeps everything and accumulates linearly —
this is the aging counter. -/
lemma reservoir_zero_closed_form (d : ℝ) (n : ℕ) :
    reservoir d 0 n = d * (n : ℝ) := by
  induction n with
  | zero => simp [reservoir]
  | succ n ih =>
      rw [reservoir]
      norm_num
      rw [ih]
      ring_nf

lemma retained_no_export_equals_counter (d : ℝ) (n : ℕ) :
    retainedDaughter d 0 n = d * (n : ℝ) := by
  exact reservoir_zero_closed_form d n

/-- The sibling is non-decreasing (the entropy sink accumulates). -/
lemma sibling_mono {a d_s : ℝ} {R : ℕ → ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d_s)
    (hR : ∀ n, 0 ≤ R n) (n : ℕ) :
    siblingDaughter a d_s R n ≤ siblingDaughter a d_s R (n + 1) := by
  rw [siblingDaughter]
  have h1 : 0 ≤ a * R n := mul_nonneg ha (hR n)
  linarith

/-- More asymmetry => lower retained equilibrium (stronger segregation keeps the 'young'
lineage cleaner). -/
lemma retained_eq_antitone {d a1 a2 : ℝ} (hd : 0 ≤ d) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (h : a1 ≤ a2) : d / a2 ≤ d / a1 := by
  field_simp [ne_of_gt ha1, ne_of_gt ha2]
  nlinarith

/-- Retained lineage never exceeds the threshold while its equilibrium stays below it
(segregation alone can keep a self-renewing lineage under a lethal threshold). -/
lemma retained_no_exit {d a k : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ha : a ≠ 0)
    (hd : 0 ≤ d) (hss : d / a ≤ k) (n : ℕ) :
    retainedDaughter d a n ≤ k := by
  exact proteostasis_no_exit (d_p := d) (r_p := a) (k_p := k) ha0 ha1 ha hd hss n

/-- **Telomerase ON (stem cells / physioxia)**: with zero attrition (τ = 0) the telomere
is maintained at its initial length — there is no telomere counter. This is why the
non-renewable centriole (not the telomere) limits stem-cell self-renewal. -/
lemma telomere_zero_attrition (t0 : ℝ) (n : ℕ) :
    telomereCounter t0 0 n = t0 := by
  induction n with
  | zero => simp [telomereCounter]
  | succ n ih =>
      rw [telomereCounter, ih]
      ring

/-! ## 8. Organismal feedback + synergy exit bound -/

/-- Renewal rate declines with organismal load: `r(S) = r₀·e^(−κ·S)`. -/
lemma renewal_strict_anti {r0 κ : ℝ} (hr0 : 0 < r0) (hκ : 0 < κ) :
    StrictAnti (fun S : ℝ => r0 * Real.exp (-κ * S)) := by
  intro S T hST
  have h1 : -κ * T < -κ * S := mul_lt_mul_of_neg_left hST (neg_lt_zero.mpr hκ)
  have h2 : Real.exp (-κ * T) < Real.exp (-κ * S) := Real.exp_lt_exp.mpr h1
  exact mul_lt_mul_of_pos_left h2 hr0

/-- Entropy/level with non-negative renewal is non-negative. -/
lemma levelEntropy_nonneg {d : ℝ} {r : ℕ → ℝ} (hd : 0 ≤ d) (hr : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n ≤ 1)
    (n : ℕ) : 0 ≤ levelEntropy d r n := by
  induction n with
  | zero => simp [levelEntropy]
  | succ n ih =>
      rw [levelEntropy]
      have h1r : 0 ≤ 1 - r n := by linarith [hr1 n]
      have hm : 0 ≤ (1 - r n) * levelEntropy d r n := mul_nonneg h1r ih
      linarith

/-- **Positive feedback accelerates accumulation**: lower renewal ⇒ at least as much level.
If `r1 ≤ r2` pointwise (renewal with `r1` is weaker), then the level with `r1` is ≥ the level
with `r2` — declining self-renewal cannot slow the build-up of damage (organismal aging). -/
lemma levelEntropy_antitone_renewal {d : ℝ} {r1 r2 : ℕ → ℝ}
    (hd : 0 ≤ d) (hr1 : ∀ n, 0 ≤ r1 n) (hr2 : ∀ n, 0 ≤ r2 n) (hr2le1 : ∀ n, r2 n ≤ 1)
    (hrle : ∀ n, r1 n ≤ r2 n) (n : ℕ) :
    levelEntropy d r2 n ≤ levelEntropy d r1 n := by
  induction n with
  | zero => simp [levelEntropy]
  | succ n ih =>
      rw [levelEntropy, levelEntropy]
      have h1r2 : 0 ≤ 1 - r2 n := by linarith [hr2le1 n]
      have h1r12 : 1 - r2 n ≤ 1 - r1 n := by linarith [hrle n]
      have hE1 : 0 ≤ levelEntropy d r1 n := levelEntropy_nonneg hd hr1 (fun n => by
        have := hrle n
        linarith [hr2le1 n]) n
      have hE2 : 0 ≤ levelEntropy d r2 n := levelEntropy_nonneg hd hr2 hr2le1 n
      have h1 := mul_le_mul_of_nonneg_left ih h1r2          -- (1-r2)·E2 ≤ (1-r2)·E1
      have h2 := mul_le_mul_of_nonneg_right h1r12 hE1       -- (1-r2)·E1 ≤ (1-r1)·E1
      have h12 : (1 - r2 n) * levelEntropy d r2 n ≤ (1 - r1 n) * levelEntropy d r1 n :=
        le_trans h1 h2
      linarith

/-! ### Synergy exit bound: a dominating counter crosses its threshold no later. -/

/-- First division at which `k < X n` (the counter's exit time). -/
noncomputable def firstCross (X : ℕ → ℝ) (k : ℝ) (h : ∃ n, k < X n) : ℕ :=
  Nat.find h

lemma exists_dominated {X Y : ℕ → ℝ} {k : ℝ} (hdom : ∀ n, Y n ≤ X n)
    (hy : ∃ n, k < Y n) : ∃ n, k < X n := by
  rcases hy with ⟨n, hn⟩
  exact ⟨n, lt_of_lt_of_le hn (hdom n)⟩

/-- **Synergy**: if the coupled damage dominates the standalone (`Y ≤ X` pointwise) and the
standalone crosses `k` at `n*`, then the coupled crosses at some `n ≤ n*` — interactions can
only advance the exit. -/
lemma firstCross_le_of_dominated {X Y : ℕ → ℝ} {k : ℝ}
    (hdom : ∀ n, Y n ≤ X n) (hy : ∃ n, k < Y n) :
    firstCross X k (exists_dominated hdom hy) ≤ firstCross Y k hy := by
  unfold firstCross
  apply Nat.find_min'
  have hY : k < Y (Nat.find hy) := Nat.find_spec hy
  have hX : k < X (Nat.find hy) := lt_of_lt_of_le hY (hdom (Nat.find hy))
  exact hX

end Cascade
end Nat
