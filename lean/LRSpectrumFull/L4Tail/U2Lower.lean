/-
# L4Tail / U2Lower: witness lower bounds for the lines `(a, b, a+b, 2a+b)`

For coprime `a, b ≥ 1` and each of the moduli `q ∈ {a+2b, 3a+2b, 3a+b}`:
`⌊q/4⌋ / q ≤ ML (a, b, a+b, 2a+b)`.  Witness time `t = j / q` with `j g ≡ ⌊q/4⌋ (mod q)` for the
pivot speed `g` (coprime to `q`); every speed is `±1, ±2, ±3` times `g` modulo `q`, and
`‖m r‖ ≥ r` for `r ≤ 1/4`, `|m| ≤ 3`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4Tail.U2Upper
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace LRSpectrumFull
namespace L4Tail

theorem ndr (r : ℝ) (hr0 : 0 ≤ r) (hr : 4 * r ≤ 1) (m : ℝ)
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = -1 ∨ m = -2 ∨ m = -3) :
    r ≤ nearestIntDist (m * r) := by
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact nearestIntDist_ge (by linarith) (by linarith) (by linarith) (by linarith)
  · exact nearestIntDist_ge (by linarith) (by linarith) (by linarith) (by linarith)
  · exact nearestIntDist_ge (by linarith) (by linarith) (by linarith) (by linarith)
  · have e : (-1 : ℝ) * r = -(1 * r) := by ring
    rw [e, nearestIntDist_neg]
    exact nearestIntDist_ge (by linarith) (by linarith) (by linarith) (by linarith)
  · have e : (-2 : ℝ) * r = -(2 * r) := by ring
    rw [e, nearestIntDist_neg]
    exact nearestIntDist_ge (by linarith) (by linarith) (by linarith) (by linarith)
  · have e : (-3 : ℝ) * r = -(3 * r) := by ring
    rw [e, nearestIntDist_neg]
    exact nearestIntDist_ge (by linarith) (by linarith) (by linarith) (by linarith)

/-- Generic witness: every speed is `m_i g + q ρ_i` with `|m_i| ∈ {1,2,3}`, `g` coprime to `q`. -/
theorem lb_witness (v : Fin 4 → ℤ) (q K g : ℤ) (hq : 0 < q) (hK0 : 0 ≤ K) (h4 : 4 * K ≤ q)
    (hcop : IsCoprime g q) (m ρ : Fin 4 → ℤ)
    (hm : ∀ i, m i = 1 ∨ m i = 2 ∨ m i = 3 ∨ m i = -1 ∨ m i = -2 ∨ m i = -3)
    (hv : ∀ i, v i = m i * g + q * ρ i) : (K : ℝ) / q ≤ ML v := by
  obtain ⟨x, y, hxy⟩ := hcop
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hr0 : 0 ≤ (K : ℝ) / q := div_nonneg (by exact_mod_cast hK0) hqr.le
  have hr4 : 4 * ((K : ℝ) / q) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hqr]; exact_mod_cast h4
  have hgj : g * (K * x) = K + q * (-(K * y)) := by linear_combination K * hxy
  refine le_trans ?_ (gap_le_ML v ((K * x : ℤ) / (q : ℝ)))
  apply le_gap
  intro i
  have key : v i * (K * x) = m i * K + q * (m i * (-(K * y)) + ρ i * (K * x)) := by
    rw [hv i]; linear_combination (m i) * hgj
  have e : ((v i : ℤ) : ℝ) * (((K * x : ℤ) : ℝ) / q)
      = (m i : ℝ) * ((K : ℝ) / q) + ((m i * (-(K * y)) + ρ i * (K * x) : ℤ) : ℝ) := by
    have key' : ((v i : ℤ) : ℝ) * ((K * x : ℤ) : ℝ)
        = (m i : ℝ) * K + q * ((m i * (-(K * y)) + ρ i * (K * x) : ℤ) : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) key
      simpa using this
    field_simp
    linear_combination key'
  rw [e, nearestIntDist_add_int]
  apply ndr _ hr0 hr4
  have := hm i
  rcases this with h | h | h | h | h | h <;> simp [h]

theorem lb_F2 (a b : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : IsCoprime a b) :
    (((3 * a + 2 * b) / 4 : ℤ) : ℝ) / ((3 * a + 2 * b : ℤ) : ℝ) ≤ ML (U2v a b) := by
  obtain ⟨x, y, h⟩ := hab
  apply lb_witness (U2v a b) (3 * a + 2 * b) ((3 * a + 2 * b) / 4) (a + b) (by omega) (by omega)
    (by omega) ⟨3 * y - 2 * x, x - y, by linear_combination h⟩ ![-2, 3, 1, -1] ![1, -1, 0, 1]
  · intro i; fin_cases i <;> simp
  · intro i; fin_cases i <;> simp <;> ring

theorem lb_F1 (a b : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : IsCoprime a b) :
    (((a + 2 * b) / 4 : ℤ) : ℝ) / ((a + 2 * b : ℤ) : ℝ) ≤ ML (U2v a b) := by
  obtain ⟨x, y, h⟩ := hab
  apply lb_witness (U2v a b) (a + 2 * b) ((a + 2 * b) / 4) b (by omega) (by omega)
    (by omega) ⟨y - 2 * x, x, by linear_combination h⟩ ![-2, 1, -1, -3] ![1, 0, 1, 2]
  · intro i; fin_cases i <;> simp
  · intro i; fin_cases i <;> simp <;> ring

theorem lb_F4 (a b : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : IsCoprime a b) :
    (((3 * a + b) / 4 : ℤ) : ℝ) / ((3 * a + b : ℤ) : ℝ) ≤ ML (U2v a b) := by
  obtain ⟨x, y, h⟩ := hab
  apply lb_witness (U2v a b) (3 * a + b) ((3 * a + b) / 4) a (by omega) (by omega)
    (by omega) ⟨x - 3 * y, y, by linear_combination h⟩ ![1, -3, -2, -1] ![0, 1, 1, 1]
  · intro i; fin_cases i <;> simp
  · intro i; fin_cases i <;> simp <;> ring

end L4Tail
end LRSpectrumFull
