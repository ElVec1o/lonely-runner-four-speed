/-
# L4S5.FourSpeed : the four-speed spectrum theorem, no hypothesis

`four_speed_spectrum`: four distinct positive integer speeds with `ML v < 1/4` have `ML v = j/(4j+2)` with an
integer `j ≥ 2`, `j ≠ 3`.  `four_speed_attained`: every such `j` occurs.  `four_speed_spectrum_iff`: the part of the
spectrum below `1/4` is exactly `{j/(4j+2) : j ≥ 2, j ≠ 3}`.

Proof: `tree_complete4_real` (L4S5.AssembleB, kernel-checked certificate, no hypothesis) feeds
`four_speed_spectrum_of_tree` (L4S5.FinalSpectrum); the tails are in `L4Tail` and the sporadic value in
`L4Tail.Sporadic`.

Not covered: repeated speeds, zero speeds, non-integer speeds, fewer or more than four speeds.

Controls: the excluded values `1/6` (`j = 1`) and `3/14` (`j = 3`) are not values of `ML` on distinct positive speeds
below `1/4` (consequences of the theorem), and `ML (1,3,4,14) = 4/17` is not `1/5`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S5.AssembleB
import LRSpectrumFull.L4S5.FinalSpectrum

namespace LRSpectrumFull
namespace L4S5

open LRSpectrumFull.L4S3 LRSpectrumFull.L4S4

theorem treeThm_real : TreeThm := fun v hnt hd => tree_complete4_real v hnt hd

/-- **The four-speed spectrum below `1/4`.** -/
theorem four_speed_spectrum (v : Fin 4 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (hlt : ML v < 1 / 4) :
    ∃ j : ℤ, 2 ≤ j ∧ j ≠ 3 ∧ ML v = (j : ℝ) / (4 * (j : ℝ) + 2) :=
  four_speed_spectrum_of_tree treeThm_real v hpos hinj hlt

/-- The set of values `< 1/4` of `ML` on four distinct positive integer speeds is `{j/(4j+2) : j ≥ 2, j ≠ 3}`. -/
theorem four_speed_spectrum_iff (x : ℝ) :
    (∃ v : Fin 4 → ℤ, (∀ i, 0 < v i) ∧ Function.Injective v ∧ ML v = x ∧ x < 1 / 4) ↔
      ∃ j : ℤ, 2 ≤ j ∧ j ≠ 3 ∧ x = (j : ℝ) / (4 * (j : ℝ) + 2) := by
  constructor
  · rintro ⟨v, hp, hi, rfl, hx⟩
    exact four_speed_spectrum v hp hi hx
  · rintro ⟨j, hj, hj3, rfl⟩
    obtain ⟨v, h1, h2, h3⟩ := four_speed_attained j hj hj3
    refine ⟨v, h1, h2, h3, ?_⟩
    have hr : (2 : ℝ) ≤ j := by exact_mod_cast hj
    rw [div_lt_iff₀ (by linarith)]
    linarith

/-! ## Controls -/

theorem ctl_not_one_sixth (v : Fin 4 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) :
    ML v ≠ 1 / 6 := by
  intro h
  obtain ⟨j, hj, -, hv⟩ := four_speed_spectrum v hpos hinj (by rw [h]; norm_num)
  rw [h] at hv
  have hr : (2 : ℝ) ≤ j := by exact_mod_cast hj
  field_simp at hv
  linarith

theorem ctl_not_three_fourteenths (v : Fin 4 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) :
    ML v ≠ 3 / 14 := by
  intro h
  obtain ⟨j, hj, hj3, hv⟩ := four_speed_spectrum v hpos hinj (by rw [h]; norm_num)
  rw [h] at hv
  have hr : (2 : ℝ) ≤ j := by exact_mod_cast hj
  field_simp at hv
  have : (j : ℝ) = 3 := by linarith
  exact hj3 (by exact_mod_cast this)

theorem ctl_sporadic_not_fifth : ML (![1, 3, 4, 14] : Fin 4 → ℤ) ≠ 1 / 5 := by
  rw [L4Tail.ML_1_3_4_14]; norm_num

end L4S5
end LRSpectrumFull
