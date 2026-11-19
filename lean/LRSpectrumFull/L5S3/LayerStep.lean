/-
# L5S3.LayerStep : the 3/4 dual-shift inequality, the layer step, the rank recursion

Pure real/integer arithmetic behind the layering argument.

* `dual_shift_34` : if `u = y + c w/|w|` lies in the dual lattice for every integer shift `n`
  (`c² = W2 (n - β)²`) and `w` is shortest, then `|y|² ≥ (3/4)|w|²` (shift by at most `|w|/2`).
* `dual_shift_34_int` : the same, cross-multiplied for `β = t/m` with integers.
* `layer_step` : `ρ(L)² ≤ ρ(M)² + 1/(4|w|²)` and `λ₁(M*)² ≥ (3/4)|w|²` give
  `ρ(L)² |w|² ≤ 1/4 + (4/3) c_prev`.
* `rank_recursion` : `c_d² ≤ 1/4 + (4/3) c_{d-1}²`, `c_1² ≤ 1/4` gives `c_d² ≤ (4/3)^(d-1) - 3/4`.
  Values `7/12, 37/36, 175/108, 781/324` by `norm_num`; geometric sums `175/27, 37/9, 7/3`.
* `tail_geom`, `tail_sum` : `μ²_{i+1} ≥ (3/4) μ²_i` iterated gives the tail constants of the node tests.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace LRSpectrumFull
namespace L5S3

open Finset

/-- Real form of the `3/4` inequality: shifting by the nearest integer moves `c` by at most `|w|/2`. -/
theorem dual_shift_34 (W2 Y2 β : ℝ) (hW : 0 < W2)
    (h : ∀ n : ℤ, W2 ≤ Y2 + W2 * ((n : ℝ) - β) ^ 2) : 3 / 4 * W2 ≤ Y2 := by
  have h1 := h (round β)
  have hb : |(round β : ℝ) - β| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact abs_sub_round β
  have hsq : ((round β : ℝ) - β) ^ 2 ≤ 1 / 4 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at this
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hsq hW.le]

/-- Integer form: `β = t / m`.  If `W2 m² ≤ Y2 m² + W2 (n m - t)²` for every integer `n`, then
`3 W2 ≤ 4 Y2`. -/
theorem dual_shift_34_int (W2 Y2 t m : ℤ) (hm : 0 < m) (hW : 0 < W2)
    (h : ∀ n : ℤ, W2 * m ^ 2 ≤ Y2 * m ^ 2 + W2 * (n * m - t) ^ 2) : 3 * W2 ≤ 4 * Y2 := by
  have hm2 : 0 < 2 * m := by omega
  have h1 : (2 * t + m) % (2 * m) + (2 * m) * ((2 * t + m) / (2 * m)) = 2 * t + m :=
    Int.emod_add_mul_ediv _ _
  have h2 : 0 ≤ (2 * t + m) % (2 * m) := Int.emod_nonneg _ (by omega)
  have h3 : (2 * t + m) % (2 * m) < 2 * m := Int.emod_lt_of_pos _ hm2
  have hn := h ((2 * t + m) / (2 * m))
  generalize (2 * t + m) % (2 * m) = r at *
  generalize (2 * t + m) / (2 * m) = n at *
  have he : 2 * (n * m - t) = m - r := by linear_combination h1
  have hbd : 4 * (n * m - t) ^ 2 ≤ m ^ 2 := by
    have : (2 * (n * m - t)) ^ 2 = (m - r) ^ 2 := by rw [he]
    nlinarith [mul_nonneg h2 (by omega : (0 : ℤ) ≤ 2 * m - r)]
  have hm2' : 0 < m ^ 2 := by positivity
  have key : 3 * W2 * m ^ 2 ≤ 4 * Y2 * m ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hbd hW.le]
  have : (3 * W2) * m ^ 2 ≤ (4 * Y2) * m ^ 2 := by linarith
  exact le_of_mul_le_mul_right this hm2'

/-- The layer step: `rL = ρ(L)²`, `rM = ρ(M)²`, `W2 = |w|²`, `Lam = λ₁(M*)²`, `cprev` a bound for
`rM * Lam`.  Conclusion: `rL * W2 ≤ 1/4 + (4/3) cprev`. -/
theorem layer_step (rL rM W2 Lam cprev : ℝ) (hW : 0 < W2) (hrM : 0 ≤ rM)
    (hcov : rL ≤ rM + 1 / (4 * W2)) (hLam : 3 / 4 * W2 ≤ Lam) (hprev : rM * Lam ≤ cprev) :
    rL * W2 ≤ 1 / 4 + 4 / 3 * cprev := by
  have e : (rM + 1 / (4 * W2)) * W2 = rM * W2 + 1 / 4 := by field_simp
  have h1 : rL * W2 ≤ rM * W2 + 1 / 4 := by
    have := mul_le_mul_of_nonneg_right hcov hW.le
    linarith
  have h2 : rM * W2 ≤ 4 / 3 * (rM * Lam) := by
    nlinarith [mul_le_mul_of_nonneg_left hLam hrM]
  linarith

/-- Rank recursion, exact solution of `x ↦ 1/4 + (4/3) x`: `c2 (e+1)` is the bound at rank `e+1`. -/
theorem rank_recursion (c2 : ℕ → ℝ) (h1 : c2 1 ≤ 1 / 4)
    (hrec : ∀ e : ℕ, c2 (e + 2) ≤ 1 / 4 + 4 / 3 * c2 (e + 1)) :
    ∀ e : ℕ, c2 (e + 1) ≤ (4 / 3 : ℝ) ^ e - 3 / 4 := by
  intro e
  induction e with
  | zero => norm_num; linarith
  | succ e ih =>
    have := hrec e
    have hp : (4 / 3 : ℝ) ^ (e + 1) = (4 / 3) * (4 / 3) ^ e := by rw [pow_succ]; ring
    rw [hp]
    linarith

/-- Numerical values of the constants `c_2², c_3², c_4², c_5²`. -/
theorem c2_values :
    (4 / 3 : ℝ) ^ 1 - 3 / 4 = 7 / 12 ∧ (4 / 3 : ℝ) ^ 2 - 3 / 4 = 37 / 36 ∧
    (4 / 3 : ℝ) ^ 3 - 3 / 4 = 175 / 108 ∧ (4 / 3 : ℝ) ^ 4 - 3 / 4 = 781 / 324 := by
  norm_num

/-- The recursion itself, over `ℚ`: `cSq e` is the rank-`(e+1)` constant. -/
def cSq : ℕ → ℚ
  | 0 => 1 / 4
  | e + 1 => 1 / 4 + 4 / 3 * cSq e

theorem cSq_closed (e : ℕ) : cSq e = (4 / 3 : ℚ) ^ e - 3 / 4 := by
  induction e with
  | zero => simp [cSq]; norm_num
  | succ e ih => rw [cSq, ih, pow_succ]; ring

theorem cSq_values :
    cSq 1 = 7 / 12 ∧ cSq 2 = 37 / 36 ∧ cSq 3 = 175 / 108 ∧ cSq 4 = 781 / 324 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [cSq] <;> norm_num

/-- Geometric sums of node tests: `∑_{s<N} (4/3)^s = 3 ((4/3)^N - 1)`. -/
theorem geom_sum_43 (N : ℕ) : ∑ s ∈ range N, (4 / 3 : ℝ) ^ s = 3 * ((4 / 3 : ℝ) ^ N - 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- The constants `175/27` (depth 1), `37/9` (depth 2), `7/3` (leaf) of the node tests. -/
theorem node_constants :
    ∑ s ∈ range 4, (4 / 3 : ℝ) ^ s = 175 / 27 ∧ ∑ s ∈ range 3, (4 / 3 : ℝ) ^ s = 37 / 9 ∧
    ∑ s ∈ range 2, (4 / 3 : ℝ) ^ s = 7 / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [geom_sum_43] <;> norm_num

/-- Test (ii) iterated: `D (i+1) ≥ (3/4) D i` gives `1 / D (r+s) ≤ (4/3)^s / D r`. -/
theorem tail_geom (D : ℕ → ℝ) (hpos : ∀ i, 0 < D i) (hstep : ∀ i, 3 / 4 * D i ≤ D (i + 1))
    (r : ℕ) : ∀ s : ℕ, 1 / D (r + s) ≤ (4 / 3 : ℝ) ^ s * (1 / D r) := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 : 1 / D (r + (s + 1)) ≤ 4 / 3 * (1 / D (r + s)) := by
      have hs := hstep (r + s)
      have a := hpos (r + s)
      have b := hpos (r + (s + 1))
      rw [show r + (s + 1) = r + s + 1 by ring]
      rw [div_le_iff₀ (hpos _)]
      rw [show 4 / 3 * (1 / D (r + s)) * D (r + s + 1) = 4 / 3 * D (r + s + 1) / D (r + s) by ring]
      rw [le_div_iff₀ a]
      nlinarith
    calc 1 / D (r + (s + 1)) ≤ 4 / 3 * (1 / D (r + s)) := h1
      _ ≤ 4 / 3 * ((4 / 3 : ℝ) ^ s * (1 / D r)) := by linarith
      _ = (4 / 3 : ℝ) ^ (s + 1) * (1 / D r) := by rw [pow_succ]; ring

/-- Tail sum for a node of rank `r`: `∑_{s<n} 1 / D (r+s) ≤ (∑_{s<n} (4/3)^s) / D r`. -/
theorem tail_sum (D : ℕ → ℝ) (hpos : ∀ i, 0 < D i) (hstep : ∀ i, 3 / 4 * D i ≤ D (i + 1))
    (r n : ℕ) :
    ∑ s ∈ range n, 1 / D (r + s) ≤ (∑ s ∈ range n, (4 / 3 : ℝ) ^ s) * (1 / D r) := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun s _ => tail_geom D hpos hstep r s

end L5S3
end LRSpectrumFull
