/-
# L4Tail / U1Lower: lines `(A, 2A, 3A, B)` of the first critical torus have `ML ≥ 1/4` off one family

For coprime `A, B ≥ 1`: `ML (A, 2A, 3A, B) ≥ 1/4` unless `A = 1` and `4 ∣ B`.

Witness time `t = r/(4A)` with `r` odd: then `‖At‖ = ‖3At‖ = 1/4`, `‖2At‖ = 1/2`, and
`‖Bt‖ ≥ 1/4` as soon as `B r ≡ c (mod 4A)` with `A ≤ c ≤ 3A`.  Existence of such an odd `r` is a
Bezout argument in three cases: `B` odd, `B ≡ 2 (mod 4)`, `4 ∣ B` (then `A` is odd and `A ≥ 3`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4Tail.U2Upper
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace LRSpectrumFull
namespace L4Tail

/-- The four speeds of a line of the first critical torus. -/
abbrev U1v (A B : ℤ) : Fin 4 → ℤ := ![A, 2 * A, 3 * A, B]

theorem U1v_injective (j : ℤ) (hj : 1 ≤ j) : Function.Injective (U1v 1 (4 * j)) := by
  intro i k h
  fin_cases i <;> fin_cases k <;> simp [U1v] at h ⊢ <;> omega

theorem nd_ge_quarter_mod (X M m c : ℤ) (hM : 0 < M) (h : X = M * m + c) (h1 : M ≤ 4 * c)
    (h2 : 4 * c ≤ 3 * M) : (1 / 4 : ℝ) ≤ nearestIntDist ((X : ℝ) / ((M : ℤ) : ℝ)) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hc1 : (M : ℝ) ≤ 4 * c := by exact_mod_cast h1
  have hc2 : (4 : ℝ) * c ≤ 3 * M := by exact_mod_cast h2
  have e : (X : ℝ) / ((M : ℤ) : ℝ) = (c : ℝ) / M + (m : ℤ) := by
    rw [h]; push_cast; field_simp; ring
  rw [e, nearestIntDist_add_int]
  have hq : (c : ℝ) / M ≤ 3 / 4 := by rw [div_le_iff₀ hMr]; linarith
  apply nearestIntDist_ge
  · exact div_nonneg (by linarith) hMr.le
  · rw [div_lt_one hMr]; linarith
  · rw [le_div_iff₀ hMr]; linarith
  · linarith

theorem odd_of_mul (B r M c : ℤ) (hB : B % 2 = 1) (h : B * r = 2 * M + c) (hc : c % 2 = 1) :
    r % 2 = 1 := by
  by_contra hr
  obtain ⟨s, hs⟩ : ∃ s, r = 2 * s := ⟨r / 2, by omega⟩
  subst hs
  have e : B * (2 * s) = 2 * (B * s) := by ring
  rw [e] at h
  generalize B * s = u at h
  omega

theorem odd_of_coprime_even (A B : ℤ) (hab : IsCoprime A B) (hB : B % 2 = 0) : A % 2 = 1 := by
  by_contra hA
  have h2A : (2 : ℤ) ∣ A := by omega
  have h2B : (2 : ℤ) ∣ B := by omega
  have hu := hab.isUnit_of_dvd' h2A h2B
  rcases Int.isUnit_iff.mp hu with h | h <;> omega

theorem coprime_odd_two (B : ℤ) (hB : B % 2 = 1) : IsCoprime B 2 :=
  ⟨1, -(B / 2), by omega⟩

/-- Existence of an odd multiplier `r` with `B r ≡ c (mod 4A)`, `A ≤ c ≤ 3A`. -/
theorem U1_exists_r (A B : ℤ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hab : IsCoprime A B)
    (hex : ¬ (A = 1 ∧ 4 ∣ B)) :
    ∃ r m c : ℤ, r % 2 = 1 ∧ B * r = 4 * A * m + c ∧ A ≤ c ∧ c ≤ 3 * A := by
  by_cases hBo : B % 2 = 1
  · -- B odd
    have h4 : IsCoprime B 4 := by
      have := (coprime_odd_two B hBo).pow_right (n := 2)
      norm_num at this
      exact this
    have hc4 : IsCoprime B (4 * A) := h4.mul_right hab.symm
    obtain ⟨x, y, hxy⟩ := hc4
    refine ⟨(A + 1 - A % 2) * x, -((A + 1 - A % 2) * y), A + 1 - A % 2, ?_, ?_, by omega, by omega⟩
    · apply odd_of_mul B _ (2 * A * (-((A + 1 - A % 2) * y))) (A + 1 - A % 2) hBo _ (by omega)
      linear_combination (A + 1 - A % 2) * hxy
    · linear_combination (A + 1 - A % 2) * hxy
  · have hBe : B % 2 = 0 := by omega
    have hAo := odd_of_coprime_even A B hab hBe
    by_cases hB4 : B % 4 = 2
    · -- B = 2 B', B' odd
      obtain ⟨B', hB'⟩ : ∃ B', B = 2 * B' := ⟨B / 2, by omega⟩
      subst hB'
      have hB'o : B' % 2 = 1 := by omega
      have hcA : IsCoprime A B' := hab.of_mul_right_right
      have hcc : IsCoprime B' (2 * A) := (coprime_odd_two B' hB'o).mul_right hcA.symm
      obtain ⟨x, y, hxy⟩ := hcc
      refine ⟨A * x, -(A * y), 2 * A, ?_, ?_, by omega, by omega⟩
      · apply odd_of_mul B' _ (-(A * A * y)) A hB'o _ hAo
        linear_combination A * hxy
      · linear_combination (2 * A) * hxy
    · -- 4 ∣ B, A odd, A ≥ 3
      have hB4' : B % 4 = 0 := by omega
      have hA3 : 3 ≤ A := by
        by_contra hlt
        apply hex
        exact ⟨by omega, by omega⟩
      obtain ⟨B', hB'⟩ : ∃ B', B = 4 * B' := ⟨B / 4, by omega⟩
      subst hB'
      have hcA : IsCoprime A B' := hab.of_mul_right_right
      obtain ⟨x, y, hxy⟩ := hcA.symm
      -- r0 = (A/2) x, B' r0 = A (-(A/2) y) + A/2
      obtain ⟨P, hP⟩ : ∃ P, P = (A / 2) * x := ⟨_, rfl⟩
      have hr0 : B' * P = A * (-((A / 2) * y)) + A / 2 := by
        rw [hP]; linear_combination (A / 2) * hxy
      by_cases hodd : P % 2 = 1
      · refine ⟨P, -((A / 2) * y), 4 * (A / 2), hodd, ?_, by omega, by omega⟩
        linear_combination 4 * hr0
      · refine ⟨P + A, -((A / 2) * y) + B', 4 * (A / 2), by omega, ?_, by omega, by omega⟩
        linear_combination 4 * hr0

theorem U1_ge_quarter (A B : ℤ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hab : IsCoprime A B)
    (hex : ¬ (A = 1 ∧ 4 ∣ B)) : (1 / 4 : ℝ) ≤ ML (U1v A B) := by
  obtain ⟨r, m, c, hr, hrel, hc1, hc2⟩ := U1_exists_r A B hA hB hab hex
  have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast (by omega : A ≠ 0)
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (r : ℝ) / ((4 * A : ℤ) : ℝ) := ⟨_, rfl⟩
  refine le_trans ?_ (gap_le_ML (U1v A B) t)
  apply le_gap
  intro i
  fin_cases i
  · have e : ((A : ℤ) : ℝ) * t = (r : ℝ) / ((4 : ℤ) : ℝ) := by
      rw [ht]; push_cast; first | (field_simp; done) | (field_simp; ring)
    show (1 / 4 : ℝ) ≤ nearestIntDist (((A : ℤ) : ℝ) * t)
    rw [e]
    exact nd_ge_quarter_mod r 4 (r / 4) (r % 4) (by norm_num) (by omega) (by omega) (by omega)
  · have e : ((2 * A : ℤ) : ℝ) * t = ((2 * r : ℤ) : ℝ) / ((4 : ℤ) : ℝ) := by
      rw [ht]; push_cast; first | (field_simp; done) | (field_simp; ring)
    show (1 / 4 : ℝ) ≤ nearestIntDist (((2 * A : ℤ) : ℝ) * t)
    rw [e]
    exact nd_ge_quarter_mod (2 * r) 4 ((2 * r) / 4) ((2 * r) % 4) (by norm_num) (by omega)
      (by omega) (by omega)
  · have e : ((3 * A : ℤ) : ℝ) * t = ((3 * r : ℤ) : ℝ) / ((4 : ℤ) : ℝ) := by
      rw [ht]; push_cast; first | (field_simp; done) | (field_simp; ring)
    show (1 / 4 : ℝ) ≤ nearestIntDist (((3 * A : ℤ) : ℝ) * t)
    rw [e]
    exact nd_ge_quarter_mod (3 * r) 4 ((3 * r) / 4) ((3 * r) % 4) (by norm_num) (by omega)
      (by omega) (by omega)
  · have e : ((B : ℤ) : ℝ) * t = ((B * r : ℤ) : ℝ) / ((4 * A : ℤ) : ℝ) := by
      rw [ht]; push_cast; ring
    show (1 / 4 : ℝ) ≤ nearestIntDist (((B : ℤ) : ℝ) * t)
    rw [e]
    exact nd_ge_quarter_mod (B * r) (4 * A) m c (by omega) hrel (by omega)
      (by omega)

end L4Tail
end LRSpectrumFull
