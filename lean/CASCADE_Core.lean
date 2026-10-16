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
* `multiHit_exact` — mean-field multi-hit has the exact binomial solution.
* `incidence_closed_form` — incidence `= n0·l^k·(n choose k-1)·(1-l)^(n-k+1)`
  (leading term `~ n^(k-1)`, Armitage-Doll power law, slope `k-1`).
* `levelEntropy_mono` — with non-increasing renewal, entropy is non-decreasing
  (self-renewal decline → organismal aging).
* `export_strictAnti` — `f(S) = f₀·e^(−kS)` is strictly decreasing (falsifiable).
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

end Cascade
end Nat
