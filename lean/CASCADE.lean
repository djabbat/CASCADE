import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
set_option linter.unnecessarySeqFocus false

/-!
# Formally verified mathematics of the centriole geometric-aging model

This file formalizes the mathematical core of the quantitative model of centriole
geometric aging (Tqemaladze, centriole geometric-aging manuscript, in preparation).
The model: a length/geometry trait `L` is passed from mother to daughter with
transmission coefficient `α ∈ [0,1]`:

```
L_{n+1} = α · L_n + (1-α) · L_0 + μ + ε_n ,
```

where `L_0` is the regulated equilibrium length, `μ` a small directed drift
(accumulation of geometric change), and `ε_n` independent noise with variance `σ²`.

The three claims of the abstract are made precise and **proved here** (deterministic
core, plus the variance recurrence):

1. **Persistence** — the geometric trait does not relax back to a population-standard
   value: the variance `Var(L_n)` is **non-decreasing** in `n` (`variance_mono`).
2. **Accumulation** — the divergence from `L_0` grows, in mean and in variance, across
   successive divisions (`length_drift_strict_mono`, `variance_mono`).
3. **Counter function** — the accumulated geometry predicts the number of divisions:
   for `μ > 0` the length is **strictly monotone** in `n` (`length_drift_strict_mono`),
   and both mean and variance converge to finite equilibria
   `L_0 + μ/(1-α)` and `σ²/(1-α²)` (`length_tendsto`, `variance_tendsto`).

All statements are elementary real analysis (geometric series, limits); no probability
machinery is needed — `Var(L_n)` is computed from the exact recurrence
`Var(L_{n+1}) = α²·Var(L_n) + σ²`, `Var(L_0) = 0`.
-/

namespace Cascade

/-- The deterministic length recurrence (noise `ε` set to zero):
`L_0 = L₀`, `L_{n+1} = α·L_n + (1-α)·L₀ + μ`. -/
noncomputable def length (α L₀ μ : ℝ) : ℕ → ℝ
  | 0 => L₀
  | n + 1 => α * length α L₀ μ n + (1 - α) * L₀ + μ

/-- Closed form of the length recurrence: `L_n = L₀ + μ·(1-αⁿ)/(1-α)`. -/
lemma length_closed_form {α L₀ μ : ℝ} (hα : α ≠ 1) (n : ℕ) :
    length α L₀ μ n = L₀ + μ * (1 - α ^ n) / (1 - α) := by
  induction n with
  | zero =>
      simp [length]
  | succ n ih =>
      rw [length, ih]
      field_simp [hα] ; ring

/-- The variance recurrence: `Var(L_0) = 0`, `Var(L_{n+1}) = α²·Var(L_n) + σ²`. -/
noncomputable def variance (α σ2 : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => α ^ 2 * variance α σ2 n + σ2

/-- Closed form of the variance: `Var(L_n) = σ²·(1-(α²)ⁿ)/(1-α²)`. -/
lemma variance_closed_form {α σ2 : ℝ} (hα2 : α ^ 2 ≠ 1) (n : ℕ) :
    variance α σ2 n = σ2 * (1 - (α ^ 2) ^ n) / (1 - α ^ 2) := by
  induction n with
  | zero =>
      simp [variance]
  | succ n ih =>
      rw [variance, ih]
      field_simp [hα2] ; ring

/-- Consecutive variance increment: `Var(L_{n+1}) - Var(L_n) = σ²·(α²)ⁿ`. -/
lemma variance_succ_sub {α σ2 : ℝ} (hα2 : α ^ 2 ≠ 1) (n : ℕ) :
    variance α σ2 (n + 1) - variance α σ2 n = σ2 * (α ^ 2) ^ n := by
  rw [variance_closed_form hα2 (n + 1), variance_closed_form hα2 n]
  field_simp [hα2] ; ring

/-- **Persistence & accumulation (variance)**: for `0 ≤ α² < 1` and `σ² ≥ 0` the variance
is non-decreasing with the number of divisions — the geometric trait does not relax
back to a population-standard value. -/
lemma variance_mono {α σ2 : ℝ} (_hα2 : 0 ≤ α ^ 2) (hα2lt : α ^ 2 < 1) (hσ2 : 0 ≤ σ2)
    (n : ℕ) : variance α σ2 n ≤ variance α σ2 (n + 1) := by
  rw [← sub_nonneg]
  rw [variance_succ_sub (ne_of_lt hα2lt) n]
  positivity

/-- Consecutive length increment: `L_{n+1} - L_n = μ·αⁿ`. -/
lemma length_succ_sub {α L₀ μ : ℝ} (hα : α ≠ 1) (n : ℕ) :
    length α L₀ μ (n + 1) - length α L₀ μ n = μ * α ^ n := by
  rw [length_closed_form hα (n + 1), length_closed_form hα n]
  field_simp [hα] ; ring

/-- **Counter function (mean accumulation)**: for `μ > 0`, `0 < α < 1`, the length
strictly increases with each division — from the observed length one can count the
number of divisions a lineage has undergone. -/
lemma length_drift_strict_mono {α L₀ μ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hμ : 0 < μ)
    (n : ℕ) : length α L₀ μ n < length α L₀ μ (n + 1) := by
  have hpos : 0 < μ * α ^ n := mul_pos hμ (pow_pos hα0 n)
  have hsub : length α L₀ μ (n + 1) - length α L₀ μ n = μ * α ^ n :=
    length_succ_sub (ne_of_lt hα1) n
  rwa [← sub_pos, hsub]

/-- **Mean equilibrium**: `L_n → L₀ + μ/(1-α)` as `n → ∞` for `0 ≤ α < 1` — the directed
drift converges to a finite equilibrium (bounded accumulation, not unbounded growth). -/
lemma length_tendsto {α L₀ μ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Filter.Tendsto (fun n : ℕ => length α L₀ μ n) Filter.atTop
      (nhds (L₀ + μ / (1 - α))) := by
  have hαn0 : Filter.Tendsto (fun n : ℕ => α ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1
  have hf : (fun n : ℕ => length α L₀ μ n) =ᶠ[Filter.atTop]
      fun n : ℕ => (L₀ + μ / (1 - α)) - μ / (1 - α) * α ^ n := by
    filter_upwards with n
    rw [length_closed_form (ne_of_lt hα1) n]
    field_simp [ne_of_lt hα1] ; ring
  have hc : Filter.Tendsto (fun n : ℕ => μ / (1 - α) * α ^ n) Filter.atTop (nhds 0) := by
    simpa using (hαn0.const_mul (μ / (1 - α)))
  have hlim : Filter.Tendsto (fun n : ℕ => (L₀ + μ / (1 - α)) - μ / (1 - α) * α ^ n)
      Filter.atTop (nhds (L₀ + μ / (1 - α))) := by
    simpa using (tendsto_const_nhds.sub hc)
  exact Filter.Tendsto.congr' hf.symm hlim

/-- **Variance equilibrium**: `Var(L_n) → σ²/(1-α²)` as `n → ∞` for `0 ≤ α² < 1` — the
variance accumulation is bounded (persistence without divergence). -/
lemma variance_tendsto {α σ2 : ℝ} (hα2 : 0 ≤ α ^ 2) (hα2lt : α ^ 2 < 1) :
    Filter.Tendsto (fun n : ℕ => variance α σ2 n) Filter.atTop
      (nhds (σ2 / (1 - α ^ 2))) := by
  have hαn0 : Filter.Tendsto (fun n : ℕ => (α ^ 2) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hα2 hα2lt
  have hf : (fun n : ℕ => variance α σ2 n) =ᶠ[Filter.atTop]
      fun n : ℕ => σ2 / (1 - α ^ 2) - σ2 / (1 - α ^ 2) * (α ^ 2) ^ n := by
    filter_upwards with n
    rw [variance_closed_form (ne_of_lt hα2lt) n]
    field_simp [ne_of_lt hα2lt]
  have hc : Filter.Tendsto (fun n : ℕ => σ2 / (1 - α ^ 2) * (α ^ 2) ^ n) Filter.atTop
      (nhds 0) := by
    simpa using (hαn0.const_mul (σ2 / (1 - α ^ 2)))
  have hlim : Filter.Tendsto (fun n : ℕ => σ2 / (1 - α ^ 2) - σ2 / (1 - α ^ 2) * (α ^ 2) ^ n)
      Filter.atTop (nhds (σ2 / (1 - α ^ 2))) := by
    simpa using (tendsto_const_nhds.sub hc)
  exact Filter.Tendsto.congr' hf.symm hlim

end Cascade
