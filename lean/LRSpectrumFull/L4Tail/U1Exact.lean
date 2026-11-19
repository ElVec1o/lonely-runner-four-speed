/-
# L4Tail / U1Exact: the exceptional lines `(1, 2, 3, 4j)` and the spectrum on the first critical torus

* `U1_exc_exact`: `ML (1, 2, 3, 4j) = j / (4j+1)` for every `j ≥ 1`.
  Lower bound: `t = j/(4j+1)`.  Upper bound: reduce to `t = p ∈ [0, 1/2]`; the four conditions
  `‖p‖, ‖2p‖, ‖3p‖, ‖4jp‖ > c` (`c = j/(4j+1)`) force `p < (1-c)/3` and then
  `j - 1 < ⌊4jp⌋ < j`, impossible.
* `U1_spectrum`: for coprime `A, B ≥ 1` with `ML (A, 2A, 3A, B) < 1/4` there is an integer `j ≥ 2`,
  `j ≠ 3` with `ML = j/(4j+2)` (here `j` is even: `j/(4j+1) = 2j/(4(2j)+2)`), by `U1_ge_quarter`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4Tail.U1Lower

namespace LRSpectrumFull
namespace L4Tail

theorem nd_red (k : ℤ) (t : ℝ) :
    nearestIntDist ((k : ℝ) * t) = nearestIntDist ((k : ℝ) * Int.fract t) := by
  have e : (k : ℝ) * t = (k : ℝ) * Int.fract t + ((k * ⌊t⌋ : ℤ) : ℝ) := by
    push_cast
    linear_combination (-(k : ℝ)) * Int.floor_add_fract t
  rw [e, nearestIntDist_add_int]

theorem nd_flip (k : ℤ) (s : ℝ) :
    nearestIntDist ((k : ℝ) * (1 - s)) = nearestIntDist ((k : ℝ) * s) := by
  have e : (k : ℝ) * (1 - s) = -((k : ℝ) * s) + ((k : ℤ) : ℝ) := by ring
  rw [e, nearestIntDist_add_int, nearestIntDist_neg]

theorem reduce_half (t : ℝ) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 / 2 ∧ ∀ k : ℤ,
      nearestIntDist ((k : ℝ) * t) = nearestIntDist ((k : ℝ) * p) := by
  by_cases hs : Int.fract t ≤ 1 / 2
  · exact ⟨Int.fract t, Int.fract_nonneg t, hs, fun k => nd_red k t⟩
  · refine ⟨1 - Int.fract t, by linarith [Int.fract_lt_one t], by linarith, fun k => ?_⟩
    rw [nd_flip, nd_red]

theorem c_bounds (J c : ℝ) (hJ1 : 1 ≤ J) (hc : c * (4 * J + 1) = J) : 1 / 5 ≤ c ∧ c < 1 / 4 := by
  have hc5 : 1 / 5 ≤ c := by
    by_contra h
    push_neg at h
    nlinarith [mul_pos (sub_pos.2 h) (by linarith : (0 : ℝ) < 4 * J + 1)]
  refine ⟨hc5, ?_⟩
  by_contra h
  push_neg at h
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ J) (sub_nonneg.2 h)]

theorem U1_core (j : ℤ) (J c p : ℝ) (hJ : (j : ℝ) = J) (hJ1 : 1 ≤ J) (hc : c * (4 * J + 1) = J)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (h1 : c < nearestIntDist p)
    (h2 : c < nearestIntDist (2 * p)) (h3 : c < nearestIntDist (3 * p))
    (h4 : c < nearestIntDist (4 * J * p)) : False := by
  obtain ⟨hc5, hc4⟩ := c_bounds J c hJ1 hc
  have f1 := nd_gt_of p 0 c (by push_cast; linarith) (by push_cast; linarith) h1
  have hpc : c < p := by have := f1.1; push_cast at this; linarith
  -- ‖2p‖
  obtain ⟨n2, f2⟩ : ∃ n2 : ℤ, c < 2 * p - n2 ∧ c < 1 - (2 * p - n2) :=
    ⟨⌊2 * p⌋, nd_gt_of (2 * p) ⌊2 * p⌋ c (by linarith [Int.floor_le (2 * p)])
      (by linarith [Int.lt_floor_add_one (2 * p)]) h2⟩
  have n2a : (n2 : ℝ) < 1 := by linarith [f2.1]
  have n2b : (-1 : ℝ) < n2 := by linarith [f2.2]
  have n2i : n2 = 0 := by
    have a : n2 < 1 := by exact_mod_cast n2a
    have b : -1 < n2 := by exact_mod_cast n2b
    omega
  subst n2i
  have g2 : 2 * p < 1 - c := by have := f2.2; push_cast at this; linarith
  -- ‖3p‖
  obtain ⟨n3, f3⟩ : ∃ n3 : ℤ, c < 3 * p - n3 ∧ c < 1 - (3 * p - n3) :=
    ⟨⌊3 * p⌋, nd_gt_of (3 * p) ⌊3 * p⌋ c (by linarith [Int.floor_le (3 * p)])
      (by linarith [Int.lt_floor_add_one (3 * p)]) h3⟩
  have n3a : (n3 : ℝ) < 2 := by linarith [f3.1]
  have n3b : (-1 : ℝ) < n3 := by linarith [f3.2]
  have n3i : n3 = 0 ∨ n3 = 1 := by
    have a : n3 < 2 := by exact_mod_cast n3a
    have b : -1 < n3 := by exact_mod_cast n3b
    omega
  rcases n3i with rfl | rfl
  swap
  · exfalso
    have := f3.1
    push_cast at this
    linarith
  have g3 : 3 * p < 1 - c := by have := f3.2; push_cast at this; linarith
  -- ‖4Jp‖
  obtain ⟨n4, f4⟩ : ∃ n4 : ℤ, c < 4 * J * p - n4 ∧ c < 1 - (4 * J * p - n4) :=
    ⟨⌊4 * J * p⌋, nd_gt_of (4 * J * p) ⌊4 * J * p⌋ c (by linarith [Int.floor_le (4 * J * p)])
      (by linarith [Int.lt_floor_add_one (4 * J * p)]) h4⟩
  have hplt : p < (1 - c) / 3 := by linarith
  have A1 : J - c < 4 * J * p := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 4 * J) (sub_pos.2 hpc), hc]
  have A2 : 4 * J * p < J + c / 3 := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 4 * J) (sub_pos.2 hplt), hc]
  have a : n4 < j := by
    have : (n4 : ℝ) < (j : ℝ) := by rw [hJ]; linarith [f4.1]
    exact_mod_cast this
  have b : j - 1 < n4 := by
    have : ((j - 1 : ℤ) : ℝ) < n4 := by push_cast; rw [hJ]; linarith [f4.2]
    exact_mod_cast this
  omega

theorem U1_ub_gap (j : ℤ) (hj : 1 ≤ j) (t : ℝ) :
    gap (U1v 1 (4 * j)) t ≤ (j : ℝ) / (4 * (j : ℝ) + 1) := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (j : ℝ) / (4 * (j : ℝ) + 1) := ⟨_, rfl⟩
  rw [← hcdef] at hlt
  have hJ1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hne : (4 * (j : ℝ) + 1) ≠ 0 := (by linarith : (0 : ℝ) < 4 * (j : ℝ) + 1).ne'
  have hc : c * (4 * (j : ℝ) + 1) = (j : ℝ) := by
    rw [hcdef]; field_simp
  have g0 : c < nearestIntDist t :=
    lt_of_lt_of_le hlt (by simpa [U1v] using gap_le (U1v 1 (4 * j)) t 0)
  have g1 : c < nearestIntDist (2 * t) :=
    lt_of_lt_of_le hlt (by simpa [U1v] using gap_le (U1v 1 (4 * j)) t 1)
  have g2 : c < nearestIntDist (3 * t) :=
    lt_of_lt_of_le hlt (by simpa [U1v] using gap_le (U1v 1 (4 * j)) t 2)
  have g3 : c < nearestIntDist (4 * (j : ℝ) * t) :=
    lt_of_lt_of_le hlt (by simpa [U1v] using gap_le (U1v 1 (4 * j)) t 3)
  obtain ⟨p, hp0, hp1, hk⟩ := reduce_half t
  have k1 := hk 1
  have k2 := hk 2
  have k3 := hk 3
  have k4 := hk (4 * j)
  simp only [Int.cast_one, one_mul] at k1
  push_cast at k2 k3 k4
  rw [k1] at g0
  rw [k2] at g1
  rw [k3] at g2
  rw [k4] at g3
  exact U1_core j (j : ℝ) c p rfl hJ1 hc hp0 hp1 g0 g1 g2 g3

theorem U1_exc_ub (j : ℤ) (hj : 1 ≤ j) :
    ML (U1v 1 (4 * j)) ≤ (j : ℝ) / (4 * (j : ℝ) + 1) :=
  gap_le_ML' _ _ (U1_ub_gap j hj)

theorem U1_exc_lb (j : ℤ) (hj : 1 ≤ j) :
    (j : ℝ) / (4 * (j : ℝ) + 1) ≤ ML (U1v 1 (4 * j)) := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (j : ℝ) / (4 * (j : ℝ) + 1) := ⟨_, rfl⟩
  rw [← hcdef]
  have hJ1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hne : (4 * (j : ℝ) + 1) ≠ 0 := (by linarith : (0 : ℝ) < 4 * (j : ℝ) + 1).ne'
  have hc : c * (4 * (j : ℝ) + 1) = (j : ℝ) := by
    rw [hcdef]; field_simp
  obtain ⟨hc5, hc4⟩ := c_bounds (j : ℝ) c hJ1 hc
  refine le_trans ?_ (gap_le_ML (U1v 1 (4 * j)) c)
  apply le_gap
  intro i
  fin_cases i
  · show c ≤ nearestIntDist (((1 : ℤ) : ℝ) * c)
    have e : ((1 : ℤ) : ℝ) * c = c := by norm_num
    rw [e]
    exact nearestIntDist_ge (by linarith) (by linarith) le_rfl (by linarith)
  · show c ≤ nearestIntDist (((2 * 1 : ℤ) : ℝ) * c)
    have e : ((2 * 1 : ℤ) : ℝ) * c = 2 * c := by push_cast; ring
    rw [e]
    exact nearestIntDist_ge (by linarith) (by linarith) (by linarith) (by linarith)
  · show c ≤ nearestIntDist (((3 * 1 : ℤ) : ℝ) * c)
    have e : ((3 * 1 : ℤ) : ℝ) * c = 3 * c := by push_cast; ring
    rw [e]
    exact nearestIntDist_ge (by linarith) (by linarith) (by linarith) (by linarith)
  · show c ≤ nearestIntDist (((4 * j : ℤ) : ℝ) * c)
    have e : ((4 * j : ℤ) : ℝ) * c = (1 - c) + ((j - 1 : ℤ) : ℝ) := by
      push_cast; linarith [hc]
    rw [e, nearestIntDist_add_int]
    exact nearestIntDist_ge (by linarith) (by linarith) (by linarith) (by linarith)

/-- **Exact value** on the exceptional lines of the first critical torus. -/
theorem U1_exc_exact (j : ℤ) (hj : 1 ≤ j) :
    ML (U1v 1 (4 * j)) = (j : ℝ) / (4 * (j : ℝ) + 1) :=
  le_antisymm (U1_exc_ub j hj) (U1_exc_lb j hj)

/-- **Spectrum on the first critical torus.** -/
theorem U1_spectrum (A B : ℤ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hab : IsCoprime A B)
    (hlt : ML (U1v A B) < 1 / 4) :
    ∃ j : ℤ, 2 ≤ j ∧ j ≠ 3 ∧ ML (U1v A B) = (j : ℝ) / (4 * (j : ℝ) + 2) := by
  by_cases hex : A = 1 ∧ 4 ∣ B
  · obtain ⟨hA1, j', hj'⟩ := hex
    subst hA1
    subst hj'
    have hj1 : 1 ≤ j' := by omega
    refine ⟨2 * j', by omega, by omega, ?_⟩
    rw [U1_exc_exact j' hj1]
    have hr : (1 : ℝ) ≤ j' := by exact_mod_cast hj1
    have h1 : (4 * (j' : ℝ) + 1) ≠ 0 := (by linarith : (0 : ℝ) < 4 * (j' : ℝ) + 1).ne'
    have h2 : (4 * (2 * (j' : ℝ)) + 2) ≠ 0 := (by linarith : (0 : ℝ) < 4 * (2 * (j' : ℝ)) + 2).ne'
    push_cast
    first | (field_simp; done) | (field_simp; ring)
  · exact absurd hlt (not_lt.2 (U1_ge_quarter A B hA hB hab hex))

end L4Tail
end LRSpectrumFull
