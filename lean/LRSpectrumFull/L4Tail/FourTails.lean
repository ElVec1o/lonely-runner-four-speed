/-
# L4Tail / FourTails: the two critical tori together

For four speeds on a line of a critical torus (`U1`: `(A, 2A, 3A, B)`, `U2`: `(a, b, a+b, 2a+b)`,
coprime parameters `≥ 1`):

* `four_tails`: `ML v < 1/4` implies `ML v = j/(4j+2)` for an integer `j ≥ 2`, `j ≠ 3`;
* `four_occurs`: every integer `j ≥ 2`, `j ≠ 3` is attained by a line with four distinct positive
  speeds: even `j` on `U1` (`(1, 2, 3, 2j)`), odd `j` on `U2` (`(8, 4s+3, ...)`, `(7, 1, 8, 15)`).

The bookkeeping that puts an arbitrary primitive four-speed vector with `ML < 1/4` on such a line
(signs, permutation, scaling, the finite tree) is not part of this file.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4Tail.U1Exact
import LRSpectrumFull.L4Tail.U2Occurs

namespace LRSpectrumFull
namespace L4Tail

/-- `v` is a line of one of the two critical tori, in normal form, with coprime parameters. -/
def IsCritLine (v : Fin 4 → ℤ) : Prop :=
  ∃ A B : ℤ, 1 ≤ A ∧ 1 ≤ B ∧ IsCoprime A B ∧ (v = U1v A B ∨ v = U2v A B)

theorem four_tails (v : Fin 4 → ℤ) (hv : IsCritLine v) (hlt : ML v < 1 / 4) :
    ∃ j : ℤ, 2 ≤ j ∧ j ≠ 3 ∧ ML v = (j : ℝ) / (4 * (j : ℝ) + 2) := by
  obtain ⟨A, B, hA, hB, hab, h | h⟩ := hv
  · subst h
    exact U1_spectrum A B hA hB hab hlt
  · subst h
    obtain ⟨j, h2, h3, hj⟩ := U2_spectrum A B hA hB hab hlt
    exact ⟨j, h2, h3, hj⟩

theorem four_occurs (j : ℤ) (hj : 2 ≤ j) (hj3 : j ≠ 3) :
    ∃ v : Fin 4 → ℤ, (∀ i, 0 < v i) ∧ Function.Injective v ∧ IsCritLine v ∧
      ML v = (j : ℝ) / (4 * (j : ℝ) + 2) := by
  by_cases hev : j % 2 = 0
  · obtain ⟨j', hj'⟩ : ∃ j', j = 2 * j' := ⟨j / 2, by omega⟩
    subst hj'
    have hj1 : 1 ≤ j' := by omega
    refine ⟨U1v 1 (4 * j'), ?_, U1v_injective j' hj1, ⟨1, 4 * j', le_rfl, by omega,
      isCoprime_one_left, Or.inl rfl⟩, ?_⟩
    · intro i
      fin_cases i <;> simp [U1v] <;> omega
    · rw [U1_exc_exact j' hj1]
      have hr : (1 : ℝ) ≤ j' := by exact_mod_cast hj1
      have h1 : (4 * (j' : ℝ) + 1) ≠ 0 := (by linarith : (0 : ℝ) < 4 * (j' : ℝ) + 1).ne'
      have h2 : (4 * ((2 * j' : ℤ) : ℝ) + 2) ≠ 0 := by
        push_cast; exact (by linarith : (0 : ℝ) < 4 * (2 * (j' : ℝ)) + 2).ne'
      push_cast at h2 ⊢
      first | (field_simp; done) | (field_simp; ring)
  · obtain ⟨a, b, ha, hb, hab, hne, hml⟩ := U2_occurs_odd j (by omega) (by omega)
    exact ⟨U2v a b, by intro i; fin_cases i <;> simp [U2v] <;> omega,
      U2v_injective a b ha hb hne, ⟨a, b, ha, hb, hab, Or.inr rfl⟩, hml⟩

end L4Tail
end LRSpectrumFull
