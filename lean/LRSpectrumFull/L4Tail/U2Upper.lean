/-
# L4Tail / U2Upper: upper bound for the lines `(a, b, a+b, 2a+b)` of the second critical torus

For integers `a, b ≥ 1` (no coprimality needed here) and a real `c` with

* `⌊(a+2b)/4⌋ ≤ (a+2b) c`, `⌊(3a+2b)/4⌋ ≤ (3a+2b) c`, `⌊(3a+b)/4⌋ ≤ (3a+b) c`,
* `2a+b - 2⌊(3a+b)/4⌋ - 2 ≤ 2(a+b) c`,

every `t` has `gap (a,b,a+b,2a+b) t ≤ c`, hence `ML ≤ c`.

Idea.  With `u = (a+b) t`, `w = a t` the four distances are `‖u‖, ‖w‖, ‖u-w‖, ‖u+w‖`.  If all four
exceed `c`, the fractional parts `(p,q)` of `(u,w)` lie in one of four triangles (one per critical
point of the `B2` gap); eliminating `t` between two of the three active inequalities gives an
integer that must exceed `⌊q/4⌋`, and a second elimination gives a second integer; the two add up to a
fixed integer (`a+b` resp. `2a+b`), which is impossible.  No tent function in `t`, no tie-point
analysis.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.DValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace LRSpectrumFull
namespace L4Tail

/-- The four speeds of a line of the second critical torus. -/
abbrev U2v (a b : ℤ) : Fin 4 → ℤ := ![a, b, a + b, 2 * a + b]

theorem nd_eq_min (y : ℝ) (h0 : 0 ≤ y) (h1 : y < 1) : nearestIntDist y = min y (1 - y) := by
  have hf : Int.fract y = y := Int.fract_eq_self.mpr ⟨h0, h1⟩
  simp only [nearestIntDist, hf]

/-- If `x` is within `[n, n+1)` and `‖x‖ > c` then both `x - n` and `1 - (x - n)` exceed `c`. -/
theorem nd_gt_of (x : ℝ) (n : ℤ) (c : ℝ) (h0 : 0 ≤ x - n) (h1 : x - n < 1)
    (h : c < nearestIntDist x) : c < x - n ∧ c < 1 - (x - n) := by
  have e : nearestIntDist x = nearestIntDist (x - n) := by
    have := nearestIntDist_add_int (x - n) n
    rwa [sub_add_cancel] at this
  rw [e, nd_eq_min _ h0 h1, lt_min_iff] at h
  exact h

/-! ## Two arithmetic cores -/

/-- Triangle around the critical point `(1/4, 1/2)`: eliminating `t` between `p > c` and
`q - p > c`, and between `p > c` and `1 - p - q > c`, gives two integers adding up to `a + b`. -/
theorem core1 (a b : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (c p q : ℝ) (n1 n2 : ℤ)
    (hrel : (a : ℝ) * p - ((a : ℝ) + b) * q = ((a : ℝ) + b) * n2 - a * n1)
    (hi : c < p) (hii : c < q - p) (hiii : c < 1 - p - q)
    (h1 : (((a + 2 * b) / 4 : ℤ) : ℝ) ≤ ((a : ℝ) + 2 * b) * c)
    (h2 : (((3 * a + 2 * b) / 4 : ℤ) : ℝ) ≤ (3 * (a : ℝ) + 2 * b) * c) : False := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have habr : (0 : ℝ) < (a : ℝ) + b := by linarith
  have h2ab : (0 : ℝ) < 2 * (a : ℝ) + b := by linarith
  have e1 : (a : ℝ) * n1 - ((a : ℝ) + b) * n2 > ((a : ℝ) + 2 * b) * c := by
    nlinarith [mul_pos hbr (sub_pos.2 hi), mul_pos habr (sub_pos.2 hii)]
  have e2 : ((a : ℝ) + b) * (n2 + 1) - a * n1 > (3 * (a : ℝ) + 2 * b) * c := by
    nlinarith [mul_pos h2ab (sub_pos.2 hi), mul_pos habr (sub_pos.2 hiii)]
  obtain ⟨M1, hM1⟩ : ∃ M1 : ℤ, M1 = a * n1 - (a + b) * n2 := ⟨_, rfl⟩
  obtain ⟨M2, hM2⟩ : ∃ M2 : ℤ, M2 = (a + b) * (n2 + 1) - a * n1 := ⟨_, rfl⟩
  have hsum : M1 + M2 = a + b := by rw [hM1, hM2]; ring
  have hM1r : (M1 : ℝ) = (a : ℝ) * n1 - ((a : ℝ) + b) * n2 := by rw [hM1]; push_cast; ring
  have hM2r : (M2 : ℝ) = ((a : ℝ) + b) * (n2 + 1) - a * n1 := by rw [hM2]; push_cast; ring
  have l1 : (((a + 2 * b) / 4 : ℤ) : ℝ) < (M1 : ℝ) := by rw [hM1r]; linarith
  have l2 : (((3 * a + 2 * b) / 4 : ℤ) : ℝ) < (M2 : ℝ) := by rw [hM2r]; linarith
  have l1' : (a + 2 * b) / 4 < M1 := by exact_mod_cast l1
  have l2' : (3 * a + 2 * b) / 4 < M2 := by exact_mod_cast l2
  omega

/-- Triangle around the critical point `(1/2, 1/4)`. -/
theorem core3 (a b : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (c p q : ℝ) (n1 n2 : ℤ)
    (hrel : (a : ℝ) * p - ((a : ℝ) + b) * q = ((a : ℝ) + b) * n2 - a * n1)
    (hw : c < q) (hu : c < p - q) (hs : c < 1 - p - q)
    (h4 : (((3 * a + b) / 4 : ℤ) : ℝ) ≤ (3 * (a : ℝ) + b) * c)
    (h6 : (((2 * a + b - 2 * ((3 * a + b) / 4) - 2 : ℤ)) : ℝ) ≤ 2 * ((a : ℝ) + b) * c) :
    False := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have h2ab : (0 : ℝ) < 2 * (a : ℝ) + b := by linarith
  have e4 : (a : ℝ) * (n1 + 1) - ((a : ℝ) + b) * n2 > (3 * (a : ℝ) + b) * c := by
    nlinarith [mul_pos h2ab (sub_pos.2 hw), mul_pos har (sub_pos.2 hs)]
  have e6 : 2 * ((a : ℝ) + b) * n2 - 2 * a * n1 + b > 2 * ((a : ℝ) + b) * c := by
    nlinarith [mul_pos h2ab (sub_pos.2 hu), mul_pos hbr (sub_pos.2 hs)]
  obtain ⟨M4, hM4⟩ : ∃ M4 : ℤ, M4 = a * (n1 + 1) - (a + b) * n2 := ⟨_, rfl⟩
  obtain ⟨P6, hP6⟩ : ∃ P6 : ℤ, P6 = 2 * (a + b) * n2 - 2 * a * n1 + b := ⟨_, rfl⟩
  have hrelZ : P6 + 2 * M4 = 2 * a + b := by rw [hM4, hP6]; ring
  have hM4r : (M4 : ℝ) = (a : ℝ) * (n1 + 1) - ((a : ℝ) + b) * n2 := by rw [hM4]; push_cast; ring
  have hP6r : (P6 : ℝ) = 2 * ((a : ℝ) + b) * n2 - 2 * a * n1 + b := by rw [hP6]; push_cast; ring
  have l4 : (((3 * a + b) / 4 : ℤ) : ℝ) < (M4 : ℝ) := by rw [hM4r]; linarith
  have l6 : (((2 * a + b - 2 * ((3 * a + b) / 4) - 2 : ℤ)) : ℝ) < (P6 : ℝ) := by
    rw [hP6r]; linarith
  have l4' : (3 * a + b) / 4 < M4 := by exact_mod_cast l4
  have l6' : 2 * a + b - 2 * ((3 * a + b) / 4) - 2 < P6 := by exact_mod_cast l6
  omega

/-! ## The localisation -/

theorem gap_le_ML' (v : Fin 4 → ℤ) (c : ℝ) (h : ∀ t, gap v t ≤ c) : ML v ≤ c := by
  unfold ML
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨t, rfl⟩
  exact h t

/-- **Upper bound** for the lines `(a, b, a+b, 2a+b)`. -/
theorem ub_gap (a b : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (c : ℝ)
    (h1 : (((a + 2 * b) / 4 : ℤ) : ℝ) ≤ ((a : ℝ) + 2 * b) * c)
    (h2 : (((3 * a + 2 * b) / 4 : ℤ) : ℝ) ≤ (3 * (a : ℝ) + 2 * b) * c)
    (h4 : (((3 * a + b) / 4 : ℤ) : ℝ) ≤ (3 * (a : ℝ) + b) * c)
    (h6 : (((2 * a + b - 2 * ((3 * a + b) / 4) - 2 : ℤ)) : ℝ) ≤ 2 * ((a : ℝ) + b) * c)
    (t : ℝ) : gap (U2v a b) t ≤ c := by
  by_contra hlt
  push_neg at hlt
  have hA : c < nearestIntDist (((a : ℤ) : ℝ) * t) := lt_of_lt_of_le hlt (by simpa [U2v] using gap_le (U2v a b) t 0)
  have hB : c < nearestIntDist (((b : ℤ) : ℝ) * t) := lt_of_lt_of_le hlt (by simpa [U2v] using gap_le (U2v a b) t 1)
  have hC : c < nearestIntDist (((a + b : ℤ) : ℝ) * t) := lt_of_lt_of_le hlt (by simpa [U2v] using gap_le (U2v a b) t 2)
  have hD : c < nearestIntDist (((2 * a + b : ℤ) : ℝ) * t) :=
    lt_of_lt_of_le hlt (by simpa [U2v] using gap_le (U2v a b) t 3)
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = ((a : ℝ) + b) * t := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (a : ℝ) * t := ⟨_, rfl⟩
  have nu : c < nearestIntDist u := by rw [hu]; push_cast at hC; exact hC
  have nw : c < nearestIntDist w := by rw [hw]; exact hA
  have nd1 : c < nearestIntDist (u - w) := by
    have e : u - w = (b : ℝ) * t := by rw [hu, hw]; ring
    rw [e]; exact hB
  have nd2 : c < nearestIntDist (u + w) := by
    have e : u + w = ((2 * a + b : ℤ) : ℝ) * t := by push_cast; rw [hu, hw]; ring
    rw [e]; exact hD
  obtain ⟨n1, hn1⟩ : ∃ n1 : ℤ, n1 = ⌊u⌋ := ⟨_, rfl⟩
  obtain ⟨n2, hn2⟩ : ∃ n2 : ℤ, n2 = ⌊w⌋ := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = u - n1 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = w - n2 := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by rw [hp, hn1]; linarith [Int.floor_le u]
  have hp1 : p < 1 := by rw [hp, hn1]; linarith [Int.lt_floor_add_one u]
  have hq0 : 0 ≤ q := by rw [hq, hn2]; linarith [Int.floor_le w]
  have hq1 : q < 1 := by rw [hq, hn2]; linarith [Int.lt_floor_add_one w]
  have hrel : (a : ℝ) * p - ((a : ℝ) + b) * q = ((a : ℝ) + b) * n2 - a * n1 := by
    rw [hp, hq, hu, hw]; ring
  have hrel' : (a : ℝ) * (1 - p) - ((a : ℝ) + b) * (1 - q)
      = ((a : ℝ) + b) * ((-n2 - 1 : ℤ) : ℝ) - a * ((-n1 - 1 : ℤ) : ℝ) := by
    push_cast; linarith [hrel]
  -- facts from the four distances
  have fu := nd_gt_of u n1 c (by rw [← hp]; exact hp0) (by rw [← hp]; exact hp1) nu
  have fw := nd_gt_of w n2 c (by rw [← hq]; exact hq0) (by rw [← hq]; exact hq1) nw
  rw [← hp] at fu
  rw [← hq] at fw
  by_cases hpq : p < q
  · -- u - w = (n1 - n2 - 1) + (p - q + 1)
    have f1 := nd_gt_of (u - w) (n1 - n2 - 1) c
      (by push_cast; linarith [hp, hq])
      (by push_cast; linarith [hp, hq]) nd1
    have f1' : c < 1 - (p - q + 1) := by
      have := f1.2; push_cast at this; linarith [hp, hq]
    by_cases hps : p + q < 1
    · -- case A
      have f2 := nd_gt_of (u + w) (n1 + n2) c
        (by push_cast; linarith [hp, hq]) (by push_cast; linarith [hp, hq]) nd2
      have f2' : c < 1 - (p + q) := by
        have := f2.2; push_cast at this; linarith [hp, hq]
      exact core1 a b ha hb c p q n1 n2 hrel fu.1 (by linarith) (by linarith) h1 h2
    · -- case C (mirror of core3)
      have f2 := nd_gt_of (u + w) (n1 + n2 + 1) c
        (by push_cast; push_neg at hps; linarith [hp, hq]) (by push_cast; linarith [hp, hq]) nd2
      have f2' : c < p + q - 1 := by
        have := f2.1; push_cast at this; linarith [hp, hq]
      exact core3 a b ha hb c (1 - p) (1 - q) (-n1 - 1) (-n2 - 1) hrel'
        (by linarith [fw.2]) (by linarith) (by linarith) h4 h6
  · push_neg at hpq
    -- u - w = (n1 - n2) + (p - q)
    have f1 := nd_gt_of (u - w) (n1 - n2) c
      (by push_cast; linarith [hp, hq]) (by push_cast; linarith [hp, hq]) nd1
    have f1' : c < p - q := by
      have := f1.1; push_cast at this; linarith [hp, hq]
    by_cases hps : p + q < 1
    · -- case B
      have f2 := nd_gt_of (u + w) (n1 + n2) c
        (by push_cast; linarith [hp, hq]) (by push_cast; linarith [hp, hq]) nd2
      have f2' : c < 1 - (p + q) := by
        have := f2.2; push_cast at this; linarith [hp, hq]
      exact core3 a b ha hb c p q n1 n2 hrel fw.1 (by linarith) (by linarith) h4 h6
    · -- case D (mirror of core1)
      have f2 := nd_gt_of (u + w) (n1 + n2 + 1) c
        (by push_cast; push_neg at hps; linarith [hp, hq]) (by push_cast; linarith [hp, hq]) nd2
      have f2' : c < p + q - 1 := by
        have := f2.1; push_cast at this; linarith [hp, hq]
      exact core1 a b ha hb c (1 - p) (1 - q) (-n1 - 1) (-n2 - 1) hrel'
        (by linarith [fu.2]) (by linarith) (by linarith) h1 h2

/-- `ML ≤ c` for the lines `(a, b, a+b, 2a+b)`. -/
theorem ub_ML (a b : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (c : ℝ)
    (h1 : (((a + 2 * b) / 4 : ℤ) : ℝ) ≤ ((a : ℝ) + 2 * b) * c)
    (h2 : (((3 * a + 2 * b) / 4 : ℤ) : ℝ) ≤ (3 * (a : ℝ) + 2 * b) * c)
    (h4 : (((3 * a + b) / 4 : ℤ) : ℝ) ≤ (3 * (a : ℝ) + b) * c)
    (h6 : (((2 * a + b - 2 * ((3 * a + b) / 4) - 2 : ℤ)) : ℝ) ≤ 2 * ((a : ℝ) + b) * c) :
    ML (U2v a b) ≤ c :=
  gap_le_ML' _ c (ub_gap a b ha hb c h1 h2 h4 h6)

end L4Tail
end LRSpectrumFull
