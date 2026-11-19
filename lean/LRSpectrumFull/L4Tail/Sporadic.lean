/-
# L4Tail / Sporadic: the exact value `ML (1, 3, 4, 14) = 4/17`

The sporadic residual tuple of the four-speed tree (`t5Data`, second entry) is not on a critical torus.
Its exact value is `4/17 = j/(4j+2)` with `j = 8`.

* lower bound: the witness time `t = 7/17` (`‖t‖ = 7/17`, `‖3t‖ = 4/17`, `‖4t‖ = 6/17`, `‖14t‖ = 4/17`);
* upper bound: the nine-interval cover of `[0, 1)` by the closed arcs `‖a s‖ ≤ 4/17` (`a ∈ {1, 3, 4, 14}`),
  proved by a chain of case splits on `s`, then lifted to all `t` through `t = ⌊t⌋ + s`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4Tail.U2Upper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

namespace LRSpectrumFull
namespace L4Tail

theorem nd_le_of (x : ℝ) (n : ℤ) (c : ℝ) (h1 : (n : ℝ) - c ≤ x) (h2 : x ≤ n + c) :
    nearestIntDist x ≤ c :=
  (nearestIntDist_le_dist x n).trans (abs_le.2 ⟨by linarith, by linarith⟩)

/-- Shifted evaluation lower bound: `x - n ∈ [c, 1 - c]` gives `c ≤ ‖x‖`. -/
theorem nd_ge_of (x : ℝ) (n : ℤ) (c : ℝ) (h0 : 0 < c) (h1 : c ≤ x - n) (h2 : x - n ≤ 1 - c) :
    c ≤ nearestIntDist x := by
  have e : nearestIntDist x = nearestIntDist (x - n) := by
    have := nearestIntDist_add_int (x - n) n
    rwa [sub_add_cancel] at this
  rw [e]
  apply nearestIntDist_ge
  · linarith
  · linarith
  · exact h1
  · linarith

/-- The nine-interval cover of `[0, 1)`. -/
theorem cover_1_3_4_14 (s : ℝ) (h0 : 0 ≤ s) (h1 : s < 1) :
    nearestIntDist s ≤ 4 / 17 ∨ nearestIntDist (3 * s) ≤ 4 / 17 ∨ nearestIntDist (4 * s) ≤ 4 / 17 ∨
      nearestIntDist (14 * s) ≤ 4 / 17 := by
  rcases le_or_gt s (4 / 17) with a1 | a1
  · exact Or.inl (nd_le_of s 0 _ (by push_cast; linarith) (by push_cast; linarith))
  rcases le_or_gt s (21 / 68) with a2 | a2
  · exact Or.inr (Or.inr (Or.inl (nd_le_of (4 * s) 1 _ (by push_cast; linarith) (by push_cast; linarith))))
  rcases le_or_gt s (7 / 17) with a3 | a3
  · exact Or.inr (Or.inl (nd_le_of (3 * s) 1 _ (by push_cast; linarith) (by push_cast; linarith)))
  rcases le_or_gt s (53 / 119) with a4 | a4
  · exact Or.inr (Or.inr (Or.inr (nd_le_of (14 * s) 6 _ (by push_cast; linarith) (by push_cast; linarith))))
  rcases le_or_gt s (19 / 34) with a5 | a5
  · exact Or.inr (Or.inr (Or.inl (nd_le_of (4 * s) 2 _ (by push_cast; linarith) (by push_cast; linarith))))
  rcases le_or_gt s (10 / 17) with a6 | a6
  · exact Or.inr (Or.inr (Or.inr (nd_le_of (14 * s) 8 _ (by push_cast; linarith) (by push_cast; linarith))))
  rcases le_or_gt s (38 / 51) with a7 | a7
  · exact Or.inr (Or.inl (nd_le_of (3 * s) 2 _ (by push_cast; linarith) (by push_cast; linarith)))
  rcases le_or_gt s (55 / 68) with a8 | a8
  · exact Or.inr (Or.inr (Or.inl (nd_le_of (4 * s) 3 _ (by push_cast; linarith) (by push_cast; linarith))))
  · exact Or.inl (nd_le_of s 1 _ (by push_cast; linarith) (by push_cast; linarith))

theorem nd_mul_fract (a : ℤ) (t : ℝ) :
    nearestIntDist ((a : ℝ) * t) = nearestIntDist ((a : ℝ) * (t - ⌊t⌋)) := by
  have e : (a : ℝ) * t = (a : ℝ) * (t - ⌊t⌋) + ((a * ⌊t⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [e, nearestIntDist_add_int]

theorem gap_1_3_4_14_le (t : ℝ) : gap (![1, 3, 4, 14] : Fin 4 → ℤ) t ≤ 4 / 17 := by
  have hs0 : 0 ≤ t - ⌊t⌋ := by linarith [Int.floor_le t]
  have hs1 : t - ⌊t⌋ < 1 := by linarith [Int.lt_floor_add_one t]
  rcases cover_1_3_4_14 _ hs0 hs1 with h | h | h | h
  · have h1 := gap_le (![1, 3, 4, 14] : Fin 4 → ℤ) t 0
    have e1 : (((![1, 3, 4, 14] : Fin 4 → ℤ) 0 : ℤ) : ℝ) = 1 := by simp
    have h2 := nd_mul_fract 1 t
    rw [e1] at h1
    push_cast at h2
    try simp only [one_mul] at h1 h2
    linarith
  · have h1 := gap_le (![1, 3, 4, 14] : Fin 4 → ℤ) t 1
    have e1 : (((![1, 3, 4, 14] : Fin 4 → ℤ) 1 : ℤ) : ℝ) = 3 := by simp
    have h2 := nd_mul_fract 3 t
    rw [e1] at h1
    push_cast at h2
    linarith
  · have h1 := gap_le (![1, 3, 4, 14] : Fin 4 → ℤ) t 2
    have e1 : (((![1, 3, 4, 14] : Fin 4 → ℤ) 2 : ℤ) : ℝ) = 4 := by simp
    have h2 := nd_mul_fract 4 t
    rw [e1] at h1
    push_cast at h2
    linarith
  · have h1 := gap_le (![1, 3, 4, 14] : Fin 4 → ℤ) t 3
    have e1 : (((![1, 3, 4, 14] : Fin 4 → ℤ) 3 : ℤ) : ℝ) = 14 := by simp
    have h2 := nd_mul_fract 14 t
    rw [e1] at h1
    push_cast at h2
    linarith

theorem ML_1_3_4_14_le : ML (![1, 3, 4, 14] : Fin 4 → ℤ) ≤ 4 / 17 :=
  gap_le_ML' _ _ gap_1_3_4_14_le

theorem ML_1_3_4_14_ge : (4 / 17 : ℝ) ≤ ML (![1, 3, 4, 14] : Fin 4 → ℤ) := by
  refine le_trans ?_ (gap_le_ML (![1, 3, 4, 14] : Fin 4 → ℤ) (7 / 17))
  apply le_gap
  intro i
  fin_cases i
  · simp
    exact nd_ge_of _ 0 _ (by norm_num) (by norm_num) (by norm_num)
  · simp
    exact nd_ge_of _ 1 _ (by norm_num) (by norm_num) (by norm_num)
  · simp
    exact nd_ge_of _ 1 _ (by norm_num) (by norm_num) (by norm_num)
  · simp
    exact nd_ge_of _ 5 _ (by norm_num) (by norm_num) (by norm_num)

/-- **The sporadic value**: `ML (1, 3, 4, 14) = 4/17 = j/(4j+2)` with `j = 8`. -/
theorem ML_1_3_4_14 : ML (![1, 3, 4, 14] : Fin 4 → ℤ) = 4 / 17 :=
  le_antisymm ML_1_3_4_14_le ML_1_3_4_14_ge

end L4Tail
end LRSpectrumFull
