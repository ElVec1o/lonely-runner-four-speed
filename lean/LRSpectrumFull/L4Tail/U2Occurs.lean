/-
# L4Tail / U2Occurs: occurrence of the odd spectrum values on the second critical torus

From `U2_exact`:  every odd `j ≥ 7` is attained by `(a, b) = (8, 4s+3)` (`j = 2s+7`, the Fan-Sun
family `(8, 4s+3, 4s+11, 4s+19)`), and `j = 5` by `(a, b) = (7, 1)`, i.e. the tuple `(7, 1, 8, 15)`.
All of these have four distinct positive speeds.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4Tail.U2Spectrum
import Mathlib.RingTheory.Coprime.Lemmas

namespace LRSpectrumFull
namespace L4Tail

theorem U2v_injective (a b : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≠ b) :
    Function.Injective (U2v a b) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [U2v] at h ⊢ <;> omega

theorem max3_eq (x y z w : ℝ) (h1 : x ≤ y) (h2 : z ≤ y) (hw : y = w) :
    max x (max y z) = w := by
  rw [← hw, max_eq_left h2]
  exact max_eq_right h1

theorem frac_le (K q K' q' : ℤ) (hq : 0 < q) (hq' : 0 < q') (h : K * q' ≤ K' * q) :
    (K : ℝ) / q ≤ (K' : ℝ) / q' := by
  have p : (0 : ℝ) < q := by exact_mod_cast hq
  have p' : (0 : ℝ) < q' := by exact_mod_cast hq'
  rw [div_le_div_iff₀ p p']
  exact_mod_cast h

/-- The Fan-Sun family: `ML (8, 4s+3, 4s+11, 4s+19) = (2s+7)/(4(2s+7)+2)`. -/
theorem U2_occ_odd (s : ℤ) (hs : 0 ≤ s) :
    ML (U2v 8 (4 * s + 3)) = ((2 * s + 7 : ℤ) : ℝ) / ((4 * (2 * s + 7) + 2 : ℤ) : ℝ) := by
  have hcop : IsCoprime (8 : ℤ) (4 * s + 3) := by
    have h2 : IsCoprime (2 : ℤ) (4 * s + 3) := ⟨-(2 * s + 1), 1, by ring⟩
    have h8 := IsCoprime.pow_left (m := 3) h2
    norm_num at h8
    exact h8
  rw [U2_exact 8 (4 * s + 3) (by norm_num) (by omega) hcop]
  have e1 : (8 + 2 * (4 * s + 3)) / 4 = 2 * s + 3 := by omega
  have e2 : (3 * 8 + 2 * (4 * s + 3)) / 4 = 2 * s + 7 := by omega
  have e4 : (3 * 8 + (4 * s + 3)) / 4 = s + 6 := by omega
  rw [e1, e2, e4]
  refine max3_eq _ _ _ _ ?_ ?_ ?_
  · apply frac_le <;> first | omega | nlinarith
  · apply frac_le <;> first | omega | nlinarith
  · congr 2
    ring

theorem U2_occ_five : ML (U2v 7 1) = ((5 : ℤ) : ℝ) / ((4 * 5 + 2 : ℤ) : ℝ) := by
  rw [U2_exact 7 1 (by norm_num) (by norm_num) isCoprime_one_right]
  have e1 : (7 + 2 * 1) / 4 = (2 : ℤ) := by norm_num
  have e2 : (3 * 7 + 2 * 1) / 4 = (5 : ℤ) := by norm_num
  have e4 : (3 * 7 + 1) / 4 = (5 : ℤ) := by norm_num
  rw [e1, e2, e4]
  norm_num [max_def]

/-- Every odd `j ≥ 5` is attained on a line `(a, b, a+b, 2a+b)` with four distinct positive speeds. -/
theorem U2_occurs_odd (j : ℤ) (hj : 5 ≤ j) (hodd : j % 2 = 1) :
    ∃ a b : ℤ, 1 ≤ a ∧ 1 ≤ b ∧ IsCoprime a b ∧ a ≠ b ∧
      ML (U2v a b) = (j : ℝ) / (4 * j + 2) := by
  by_cases h5 : j = 5
  · subst h5
    refine ⟨7, 1, by norm_num, by norm_num, isCoprime_one_right, by norm_num, ?_⟩
    rw [U2_occ_five]; push_cast; norm_num
  · have hj7 : 7 ≤ j := by omega
    refine ⟨8, 4 * ((j - 7) / 2) + 3, by norm_num, by omega, ?_, by omega, ?_⟩
    · have h2 : IsCoprime (2 : ℤ) (4 * ((j - 7) / 2) + 3) :=
        ⟨-(2 * ((j - 7) / 2) + 1), 1, by ring⟩
      have h8 := IsCoprime.pow_left (m := 3) h2
      norm_num at h8
      exact h8
    · have hs : 0 ≤ (j - 7) / 2 := by omega
      rw [U2_occ_odd _ hs]
      have e : 2 * ((j - 7) / 2) + 7 = j := by omega
      rw [e]
      push_cast
      ring

end L4Tail
end LRSpectrumFull
