/-
# L4Tail / U2Spectrum: the spectrum on the lines `(a, b, a+b, 2a+b)`

For coprime `a, b ≥ 1` with `ML (a, b, a+b, 2a+b) < 1/4` there is an integer `j ≥ 2`, `j ≠ 3`,
with `ML = j / (4j+2)`.  Proof: `U2_exact` (a max of three terms `K_i/q_i`); the winning family
has `ν_i = q_i mod 4 ∈ {1,2}` (residue-class case split, `omega`), `q_i ∉ {6, 14}` (finite check,
`omega`), and `K_i/q_i = j/(4j+2)` with `j = 2K_i` (ν = 1) or `j = K_i` (ν = 2).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4Tail.U2Exact

namespace LRSpectrumFull
namespace L4Tail

theorem cmp_id (K1 q1 n1 K2 q2 n2 : ℤ) (e1 : q1 = 4 * K1 + n1) (e2 : q2 = 4 * K2 + n2) :
    4 * (K1 * q2 - K2 * q1) = n2 * q1 - n1 * q2 := by
  linear_combination (-q2) * e1 + q1 * e2

theorem ineq_of_le (K1 q1 n1 K2 q2 n2 : ℤ) (hq1 : 0 < q1) (hq2 : 0 < q2)
    (e1 : q1 = 4 * K1 + n1) (e2 : q2 = 4 * K2 + n2)
    (h : (K2 : ℝ) / q2 ≤ (K1 : ℝ) / q1) : n1 * q2 ≤ n2 * q1 := by
  have p1 : (0 : ℝ) < q1 := by exact_mod_cast hq1
  have p2 : (0 : ℝ) < q2 := by exact_mod_cast hq2
  have h' := (div_le_div_iff₀ p2 p1).mp h
  have h'' : K2 * q1 ≤ K1 * q2 := by exact_mod_cast h'
  have := cmp_id K1 q1 n1 K2 q2 n2 e1 e2
  nlinarith [this, h'']

theorem win1 (a b n1 n2 n4 : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : ¬ (a % 2 = 0 ∧ b % 2 = 0))
    (hn1 : n1 = (a + 2 * b) % 4) (hn2 : n2 = (3 * a + 2 * b) % 4) (hn4 : n4 = (3 * a + b) % 4)
    (h2 : n1 * (3 * a + 2 * b) ≤ n2 * (a + 2 * b)) (h4 : n1 * (3 * a + b) ≤ n4 * (a + 2 * b))
    (h0 : n1 ≠ 0) : (n1 = 1 ∨ n1 = 2) ∧ a + 2 * b ≠ 6 ∧ a + 2 * b ≠ 14 := by
  have c1 : n1 = 0 ∨ n1 = 1 ∨ n1 = 2 ∨ n1 = 3 := by omega
  have c2 : n2 = 0 ∨ n2 = 1 ∨ n2 = 2 ∨ n2 = 3 := by omega
  have c4 : n4 = 0 ∨ n4 = 1 ∨ n4 = 2 ∨ n4 = 3 := by omega
  rcases c1 with rfl | rfl | rfl | rfl <;> rcases c2 with rfl | rfl | rfl | rfl <;>
    rcases c4 with rfl | rfl | rfl | rfl <;> omega

theorem win2 (a b n1 n2 n4 : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : ¬ (a % 2 = 0 ∧ b % 2 = 0))
    (hn1 : n1 = (a + 2 * b) % 4) (hn2 : n2 = (3 * a + 2 * b) % 4) (hn4 : n4 = (3 * a + b) % 4)
    (h1 : n2 * (a + 2 * b) ≤ n1 * (3 * a + 2 * b)) (h4 : n2 * (3 * a + b) ≤ n4 * (3 * a + 2 * b))
    (h0 : n2 ≠ 0) : (n2 = 1 ∨ n2 = 2) ∧ 3 * a + 2 * b ≠ 6 ∧ 3 * a + 2 * b ≠ 14 := by
  have c1 : n1 = 0 ∨ n1 = 1 ∨ n1 = 2 ∨ n1 = 3 := by omega
  have c2 : n2 = 0 ∨ n2 = 1 ∨ n2 = 2 ∨ n2 = 3 := by omega
  have c4 : n4 = 0 ∨ n4 = 1 ∨ n4 = 2 ∨ n4 = 3 := by omega
  rcases c1 with rfl | rfl | rfl | rfl <;> rcases c2 with rfl | rfl | rfl | rfl <;>
    rcases c4 with rfl | rfl | rfl | rfl <;> omega

theorem win4 (a b n1 n2 n4 : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : ¬ (a % 2 = 0 ∧ b % 2 = 0))
    (hn1 : n1 = (a + 2 * b) % 4) (hn2 : n2 = (3 * a + 2 * b) % 4) (hn4 : n4 = (3 * a + b) % 4)
    (h1 : n4 * (a + 2 * b) ≤ n1 * (3 * a + b)) (h2 : n4 * (3 * a + 2 * b) ≤ n2 * (3 * a + b))
    (h0 : n4 ≠ 0) : (n4 = 1 ∨ n4 = 2) ∧ 3 * a + b ≠ 6 ∧ 3 * a + b ≠ 14 := by
  have c1 : n1 = 0 ∨ n1 = 1 ∨ n1 = 2 ∨ n1 = 3 := by omega
  have c2 : n2 = 0 ∨ n2 = 1 ∨ n2 = 2 ∨ n2 = 3 := by omega
  have c4 : n4 = 0 ∨ n4 = 1 ∨ n4 = 2 ∨ n4 = 3 := by omega
  rcases c1 with rfl | rfl | rfl | rfl <;> rcases c2 with rfl | rfl | rfl | rfl <;>
    rcases c4 with rfl | rfl | rfl | rfl <;> omega

theorem fin_step (q K ν : ℤ) (hq : q = 4 * K + ν) (hν : ν = 1 ∨ ν = 2) (hq3 : 3 ≤ q)
    (h6 : q ≠ 6) (h14 : q ≠ 14) :
    ∃ j : ℤ, 2 ≤ j ∧ j ≠ 3 ∧ (K : ℝ) / (q : ℝ) = (j : ℝ) / (4 * j + 2) := by
  rcases hν with rfl | rfl
  · refine ⟨2 * K, by omega, by omega, ?_⟩
    have e : (q : ℝ) = 4 * K + 1 := by exact_mod_cast hq
    rw [e]; push_cast
    have : (0 : ℝ) < K := by exact_mod_cast (by omega : (0 : ℤ) < K)
    field_simp
  · refine ⟨K, by omega, by omega, ?_⟩
    have e : (q : ℝ) = 4 * K + 2 := by exact_mod_cast hq
    rw [e]

theorem win_sel (r1 r2 r4 : ℝ) :
    (max r1 (max r2 r4) = r1 ∧ r2 ≤ r1 ∧ r4 ≤ r1) ∨ (max r1 (max r2 r4) = r2 ∧ r1 ≤ r2 ∧ r4 ≤ r2) ∨
    (max r1 (max r2 r4) = r4 ∧ r1 ≤ r4 ∧ r2 ≤ r4) := by
  rcases le_total r2 r4 with h24 | h42
  · rcases le_total r1 r4 with h14 | h41
    · right; right; exact ⟨by rw [max_eq_right h24, max_eq_right h14], h14, h24⟩
    · left; exact ⟨by rw [max_eq_right h24]; exact max_eq_left h41, h24.trans h41, h41⟩
  · rcases le_total r1 r2 with h12 | h21
    · right; left; exact ⟨by rw [max_eq_left h42]; exact max_eq_right h12, h12, h42⟩
    · left; exact ⟨by rw [max_eq_left h42]; exact max_eq_left h21, h21, h42.trans h21⟩

theorem lt_of_div (K q : ℤ) (hq : 0 < q) (h : (K : ℝ) / q < 1 / 4) : 4 * K < q := by
  have p : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_lt_iff₀ p] at h
  have : (4 * K : ℝ) < q := by linarith
  exact_mod_cast this

/-- **Spectrum on `U^2` lines**: `ML < 1/4` forces `ML = j/(4j+2)`, `j ≥ 2`, `j ≠ 3`. -/
theorem U2_spectrum (a b : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : IsCoprime a b)
    (hlt : ML (U2v a b) < 1 / 4) :
    ∃ j : ℤ, 2 ≤ j ∧ j ≠ 3 ∧ ML (U2v a b) = (j : ℝ) / (4 * j + 2) := by
  have hc : ¬ (a % 2 = 0 ∧ b % 2 = 0) := by
    rintro ⟨h1, h2⟩
    obtain ⟨x, y, hxy⟩ := hab
    have ha2 : a = 2 * (a / 2) := by omega
    have hb2 : b = 2 * (b / 2) := by omega
    rw [ha2, hb2] at hxy
    have h2 : (2 : ℤ) ∣ 1 := ⟨x * (a / 2) + y * (b / 2), by linarith⟩
    omega
  have hM := U2_exact a b ha hb hab
  have e1 : a + 2 * b = 4 * ((a + 2 * b) / 4) + (a + 2 * b) % 4 := by omega
  have e2 : 3 * a + 2 * b = 4 * ((3 * a + 2 * b) / 4) + (3 * a + 2 * b) % 4 := by omega
  have e4 : 3 * a + b = 4 * ((3 * a + b) / 4) + (3 * a + b) % 4 := by omega
  have q1 : (0 : ℤ) < a + 2 * b := by omega
  have q2 : (0 : ℤ) < 3 * a + 2 * b := by omega
  have q4 : (0 : ℤ) < 3 * a + b := by omega
  rw [hM] at hlt ⊢
  rcases win_sel ((((a + 2 * b) / 4 : ℤ) : ℝ) / ((a + 2 * b : ℤ) : ℝ))
      ((((3 * a + 2 * b) / 4 : ℤ) : ℝ) / ((3 * a + 2 * b : ℤ) : ℝ))
      ((((3 * a + b) / 4 : ℤ) : ℝ) / ((3 * a + b : ℤ) : ℝ)) with
    ⟨hm, h2, h4⟩ | ⟨hm, h1, h4⟩ | ⟨hm, h1, h2⟩
  · rw [hm] at hlt ⊢
    have l := lt_of_div _ _ q1 hlt
    have i2 := ineq_of_le _ _ _ _ _ _ q1 q2 e1 e2 h2
    have i4 := ineq_of_le _ _ _ _ _ _ q1 q4 e1 e4 h4
    obtain ⟨hn, h6, h14⟩ := win1 a b _ _ _ ha hb hc rfl rfl rfl i2 i4 (by omega)
    obtain ⟨j, hj1, hj2, hj3⟩ := fin_step (a + 2 * b) ((a + 2 * b) / 4) ((a + 2 * b) % 4) e1 hn
      (by omega) h6 h14
    exact ⟨j, hj1, hj2, hj3⟩
  · rw [hm] at hlt ⊢
    have l := lt_of_div _ _ q2 hlt
    have i1 := ineq_of_le _ _ _ _ _ _ q2 q1 e2 e1 h1
    have i4 := ineq_of_le _ _ _ _ _ _ q2 q4 e2 e4 h4
    obtain ⟨hn, h6, h14⟩ := win2 a b _ _ _ ha hb hc rfl rfl rfl i1 i4 (by omega)
    obtain ⟨j, hj1, hj2, hj3⟩ := fin_step (3 * a + 2 * b) ((3 * a + 2 * b) / 4)
      ((3 * a + 2 * b) % 4) e2 hn (by omega) h6 h14
    exact ⟨j, hj1, hj2, hj3⟩
  · rw [hm] at hlt ⊢
    have l := lt_of_div _ _ q4 hlt
    have i1 := ineq_of_le _ _ _ _ _ _ q4 q1 e4 e1 h1
    have i2 := ineq_of_le _ _ _ _ _ _ q4 q2 e4 e2 h2
    obtain ⟨hn, h6, h14⟩ := win4 a b _ _ _ ha hb hc rfl rfl rfl i1 i2 (by omega)
    obtain ⟨j, hj1, hj2, hj3⟩ := fin_step (3 * a + b) ((3 * a + b) / 4) ((3 * a + b) % 4) e4 hn
      (by omega) h6 h14
    exact ⟨j, hj1, hj2, hj3⟩

end L4Tail
end LRSpectrumFull
