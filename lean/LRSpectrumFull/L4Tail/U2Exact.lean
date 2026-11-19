/-
# L4Tail / U2Exact: the exact value of ML on the lines `(a, b, a+b, 2a+b)`

For coprime `a, b ≥ 1`:
`ML (a, b, a+b, 2a+b) = max (K₁/q₁) (K₂/q₂) (K₄/q₄)` with `q₁ = a+2b`, `q₂ = 3a+2b`, `q₄ = 3a+b`,
`K_i = ⌊q_i/4⌋`.  Lower bound: `U2Lower`; upper bound: `U2Upper` plus a residue-class domination
(`dom`) showing the fourth hypothesis (the family `t = (2m+1)/(2(a+b))`) is implied by the other three.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4Tail.U2Lower

namespace LRSpectrumFull
namespace L4Tail

/-- Residue-class domination (the 12-class table, here as 64 omega cases on three residues):
one of the three families beats the fourth hypothesis. -/
theorem dom_lin (a b : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a + b) * ((a + 2 * b) % 4) ≤ (4 - (3 * a + b) % 4) * (a + 2 * b) ∨
    (a + b) * ((3 * a + 2 * b) % 4) ≤ (4 - (3 * a + b) % 4) * (3 * a + 2 * b) ∨
    (a + b) * ((3 * a + b) % 4) ≤ (4 - (3 * a + b) % 4) * (3 * a + b) := by
  have hr : (3 * a + b) % 4 = 0 ∨ (3 * a + b) % 4 = 1 ∨ (3 * a + b) % 4 = 2 ∨ (3 * a + b) % 4 = 3 := by
    omega
  have h1 : (a + 2 * b) % 4 = 0 ∨ (a + 2 * b) % 4 = 1 ∨ (a + 2 * b) % 4 = 2 ∨ (a + 2 * b) % 4 = 3 := by
    omega
  have h2 : (3 * a + 2 * b) % 4 = 0 ∨ (3 * a + 2 * b) % 4 = 1 ∨ (3 * a + 2 * b) % 4 = 2 ∨
      (3 * a + 2 * b) % 4 = 3 := by omega
  rcases hr with hr | hr | hr | hr <;> rcases h1 with h1 | h1 | h1 | h1 <;>
    rcases h2 with h2 | h2 | h2 | h2 <;> rw [hr, h1, h2] <;> omega

/-- Integer form of the domination: `X q_i ≤ 2 (a+b) K_i` for some family `i`. -/
theorem dom_int (a b : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (2 * a + b - 2 * ((3 * a + b) / 4) - 2) * (a + 2 * b) ≤ 2 * (a + b) * ((a + 2 * b) / 4) ∨
    (2 * a + b - 2 * ((3 * a + b) / 4) - 2) * (3 * a + 2 * b) ≤ 2 * (a + b) * ((3 * a + 2 * b) / 4) ∨
    (2 * a + b - 2 * ((3 * a + b) / 4) - 2) * (3 * a + b) ≤ 2 * (a + b) * ((3 * a + b) / 4) := by
  obtain ⟨K1, hK1⟩ : ∃ K, K = (a + 2 * b) / 4 := ⟨_, rfl⟩
  obtain ⟨K2, hK2⟩ : ∃ K, K = (3 * a + 2 * b) / 4 := ⟨_, rfl⟩
  obtain ⟨K4, hK4⟩ : ∃ K, K = (3 * a + b) / 4 := ⟨_, rfl⟩
  obtain ⟨n1, hn1⟩ : ∃ n, n = (a + 2 * b) % 4 := ⟨_, rfl⟩
  obtain ⟨n2, hn2⟩ : ∃ n, n = (3 * a + 2 * b) % 4 := ⟨_, rfl⟩
  obtain ⟨n4, hn4⟩ : ∃ n, n = (3 * a + b) % 4 := ⟨_, rfl⟩
  have e1 : a + 2 * b = 4 * K1 + n1 := by omega
  have e2 : 3 * a + 2 * b = 4 * K2 + n2 := by omega
  have e4 : 3 * a + b = 4 * K4 + n4 := by omega
  have L := dom_lin a b ha hb
  rw [← hn1, ← hn2, ← hn4] at L
  rw [← hK1, ← hK2, ← hK4]
  rcases L with L | L | L
  · left
    have id : 2 * (2 * (a + b) * K1 - (2 * a + b - 2 * K4 - 2) * (a + 2 * b))
        = (4 - n4) * (a + 2 * b) - (a + b) * n1 := by
      linear_combination (-(a + b)) * e1 + (-(a + 2 * b)) * e4
    nlinarith [id, L]
  · right; left
    have id : 2 * (2 * (a + b) * K2 - (2 * a + b - 2 * K4 - 2) * (3 * a + 2 * b))
        = (4 - n4) * (3 * a + 2 * b) - (a + b) * n2 := by
      linear_combination (-(a + b)) * e2 + (-(3 * a + 2 * b)) * e4
    nlinarith [id, L]
  · right; right
    have id : 2 * (2 * (a + b) * K4 - (2 * a + b - 2 * K4 - 2) * (3 * a + b))
        = (4 - n4) * (3 * a + b) - (a + b) * n4 := by
      linear_combination (-(a + b)) * e4 + (-(3 * a + b)) * e4
    nlinarith [id, L]

/-- **Exact value** of `ML` on a line `(a, b, a+b, 2a+b)` of the second critical torus. -/
theorem U2_exact (a b : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : IsCoprime a b) :
    ML (U2v a b) =
      max ((((a + 2 * b) / 4 : ℤ) : ℝ) / ((a + 2 * b : ℤ) : ℝ))
        (max ((((3 * a + 2 * b) / 4 : ℤ) : ℝ) / ((3 * a + 2 * b : ℤ) : ℝ))
          ((((3 * a + b) / 4 : ℤ) : ℝ) / ((3 * a + b : ℤ) : ℝ))) := by
  apply le_antisymm
  · set c := max ((((a + 2 * b) / 4 : ℤ) : ℝ) / ((a + 2 * b : ℤ) : ℝ))
        (max ((((3 * a + 2 * b) / 4 : ℤ) : ℝ) / ((3 * a + 2 * b : ℤ) : ℝ))
          ((((3 * a + b) / 4 : ℤ) : ℝ) / ((3 * a + b : ℤ) : ℝ))) with hc
    have p1 : (0 : ℝ) < ((a + 2 * b : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < a + 2 * b)
    have p2 : (0 : ℝ) < ((3 * a + 2 * b : ℤ) : ℝ) := by
      exact_mod_cast (by omega : (0 : ℤ) < 3 * a + 2 * b)
    have p4 : (0 : ℝ) < ((3 * a + b : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < 3 * a + b)
    have c1 : (((a + 2 * b) / 4 : ℤ) : ℝ) / ((a + 2 * b : ℤ) : ℝ) ≤ c := le_max_left _ _
    have c2 : (((3 * a + 2 * b) / 4 : ℤ) : ℝ) / ((3 * a + 2 * b : ℤ) : ℝ) ≤ c :=
      (le_max_left _ _).trans (le_max_right _ _)
    have c4 : (((3 * a + b) / 4 : ℤ) : ℝ) / ((3 * a + b : ℤ) : ℝ) ≤ c :=
      (le_max_right _ _).trans (le_max_right _ _)
    have k1 : (((a + 2 * b) / 4 : ℤ) : ℝ) ≤ ((a + 2 * b : ℤ) : ℝ) * c := (div_le_iff₀ p1).mp c1 |>.trans (by rw [mul_comm])
    have k2 : (((3 * a + 2 * b) / 4 : ℤ) : ℝ) ≤ ((3 * a + 2 * b : ℤ) : ℝ) * c :=
      (div_le_iff₀ p2).mp c2 |>.trans (by rw [mul_comm])
    have k4 : (((3 * a + b) / 4 : ℤ) : ℝ) ≤ ((3 * a + b : ℤ) : ℝ) * c :=
      (div_le_iff₀ p4).mp c4 |>.trans (by rw [mul_comm])
    -- fourth hypothesis from the domination
    have h6 : (((2 * a + b - 2 * ((3 * a + b) / 4) - 2 : ℤ)) : ℝ) ≤ 2 * ((a : ℝ) + b) * c := by
      have hs : (0 : ℝ) < 2 * ((a : ℝ) + b) := by
        have : (0 : ℝ) < (a : ℝ) + b := by
          have h1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
          have h2 : (1 : ℝ) ≤ b := by exact_mod_cast hb
          linarith
        linarith
      rcases dom_int a b ha hb with D | D | D
      · have D' : ((2 * a + b - 2 * ((3 * a + b) / 4) - 2 : ℤ) : ℝ) * ((a + 2 * b : ℤ) : ℝ)
            ≤ 2 * ((a : ℝ) + b) * (((a + 2 * b) / 4 : ℤ) : ℝ) := by exact_mod_cast D
        by_contra hcon
        push_neg at hcon
        nlinarith [mul_lt_mul_of_pos_right hcon p1, mul_le_mul_of_nonneg_left k1 hs.le]
      · have D' : ((2 * a + b - 2 * ((3 * a + b) / 4) - 2 : ℤ) : ℝ) * ((3 * a + 2 * b : ℤ) : ℝ)
            ≤ 2 * ((a : ℝ) + b) * (((3 * a + 2 * b) / 4 : ℤ) : ℝ) := by exact_mod_cast D
        by_contra hcon
        push_neg at hcon
        nlinarith [mul_lt_mul_of_pos_right hcon p2, mul_le_mul_of_nonneg_left k2 hs.le]
      · have D' : ((2 * a + b - 2 * ((3 * a + b) / 4) - 2 : ℤ) : ℝ) * ((3 * a + b : ℤ) : ℝ)
            ≤ 2 * ((a : ℝ) + b) * (((3 * a + b) / 4 : ℤ) : ℝ) := by exact_mod_cast D
        by_contra hcon
        push_neg at hcon
        nlinarith [mul_lt_mul_of_pos_right hcon p4, mul_le_mul_of_nonneg_left k4 hs.le]
    refine ub_ML a b ha hb c ?_ ?_ ?_ h6
    · push_cast at k1; exact k1
    · push_cast at k2; exact k2
    · push_cast at k4; exact k4
  · exact max_le (lb_F1 a b ha hb hab) (max_le (lb_F2 a b ha hb hab) (lb_F4 a b ha hb hab))

end L4Tail
end LRSpectrumFull
