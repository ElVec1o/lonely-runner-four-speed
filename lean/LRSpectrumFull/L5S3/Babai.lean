/-
# L5S3.Babai : rounding in an LDL form (nearest plane), pure real arithmetic


No lattices, no inner-product spaces, no `GramSchmidtOrtho`: a nearest-plane statement about a unit
lower-triangular real array `Lm`, nonnegative weights `E` (the weights are `1/D_i` for the diagonal `D`
of an LDL decomposition `G = L D Lᵀ`), and the integer rounding `round`.  Indices are natural numbers
(`ℕ → ℕ → ℝ` arrays used below the diagonal), so no `Fin` recursion is needed; a `Fin 4` flag is
embedded by extension by zero when the lemma is used.

* `babai_exists_prefix` : forward form.  For every `d` there are integers `a i` and reals `w i`
  with `p i - a i = w i + ∑_{j<i} Lm i j * w j` (that is, `w = L⁻¹ (p - a)`), `|w i| ≤ 1/2`,
  and `w i = 0` for `i < k` when `p i` is an integer for `i < k`.
* `babai_round` : with weights, `∑ w i ^ 2 * E i ≤ (1/4) ∑_{k ≤ i < d} E i`.
* `babai_round_D` : the same with `E i = 1 / D i`, `D i > 0` (the form used for the flag).
* `nearest_plane_coords` / `nearest_plane_sq` : the same lemma in the usual orthogonal-basis
  presentation (basis `b_i = ∑_{j ≤ i} U i j b*_j`, coordinates `c_j` of a point in the orthogonal basis
  `b*_j`): integers `a` with every residual coordinate within `1/2`, hence squared distance
  `≤ (1/4) ∑ |b*_j|²`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace LRSpectrumFull
namespace L5S3

open Finset

/-- Forward (lower-triangular) nearest-plane existence, by induction on the dimension `d`. -/
theorem babai_exists_prefix (Lm : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (k : ℕ)
    (hp : ∀ i, i < k → ∃ n : ℤ, p i = n) :
    ∀ d : ℕ, ∃ (a : ℕ → ℤ) (w : ℕ → ℝ),
      (∀ i, i < d → p i - a i = w i + ∑ j ∈ range i, Lm i j * w j) ∧
      (∀ i, i < d → i < k → w i = 0) ∧
      (∀ i, i < d → |w i| ≤ 1 / 2) := by
  intro d
  induction d with
  | zero =>
    exact ⟨fun _ => 0, fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ d ih =>
    obtain ⟨a, w, hE, h0, hb⟩ := ih
    have key : ∃ (nd : ℤ) (wd : ℝ), p d - nd = wd + ∑ j ∈ range d, Lm d j * w j ∧
        |wd| ≤ 1 / 2 ∧ (d < k → wd = 0) := by
      by_cases hk : d < k
      · obtain ⟨n, hn⟩ := hp d hk
        have hsum : ∑ j ∈ range d, Lm d j * w j = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hjd : j < d := Finset.mem_range.mp hj
          rw [h0 j hjd (lt_trans hjd hk), mul_zero]
        refine ⟨n, 0, ?_, by norm_num, fun _ => rfl⟩
        rw [hsum, hn]; ring
      · refine ⟨round (p d - ∑ j ∈ range d, Lm d j * w j),
          (p d - ∑ j ∈ range d, Lm d j * w j) - round (p d - ∑ j ∈ range d, Lm d j * w j),
          ?_, abs_sub_round _, fun h => absurd h hk⟩
        ring
    obtain ⟨nd, wd, hEd, hbd, h0d⟩ := key
    refine ⟨fun i => if i = d then nd else a i, fun i => if i = d then wd else w i, ?_, ?_, ?_⟩
    · intro i hi
      by_cases hid : i = d
      · subst hid
        simp only [if_true]
        rw [hEd]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have hne : j ≠ i := ne_of_lt (Finset.mem_range.mp hj)
        simp [hne]
      · have hlt : i < d := by omega
        simp only [hid, if_false]
        rw [hE i hlt]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have hne : j ≠ d := ne_of_lt (lt_trans (Finset.mem_range.mp hj) hlt)
        simp [hne]
    · intro i hi hik
      by_cases hid : i = d
      · subst hid
        simp [h0d hik]
      · have hlt : i < d := by omega
        simp [hid, h0 i hlt hik]
    · intro i hi
      by_cases hid : i = d
      · subst hid
        simpa using hbd
      · have hlt : i < d := by omega
        simp only [hid, if_false]
        exact hb i hlt

/-- **Rounding in an LDL form** (Babai, nearest plane), weighted version.  With nonnegative weights `E`
(`E i = 1 / D i` for the diagonal `D` of the LDL decomposition), the weighted squared norm of the
residual `w = L⁻¹ (p - a)` is at most `1/4` of the total weight of the free coordinates `k ≤ i < d`. -/
theorem babai_round (Lm : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i) (p : ℕ → ℝ) (k d : ℕ)
    (hp : ∀ i, i < k → ∃ n : ℤ, p i = n) :
    ∃ (a : ℕ → ℤ) (w : ℕ → ℝ),
      (∀ i, i < d → p i - a i = w i + ∑ j ∈ range i, Lm i j * w j) ∧
      (∀ i, i < d → i < k → w i = 0) ∧
      (∀ i, i < d → |w i| ≤ 1 / 2) ∧
      ∑ i ∈ range d, w i ^ 2 * E i ≤ (1 / 4) * ∑ i ∈ (range d).filter (fun i => k ≤ i), E i := by
  obtain ⟨a, w, h1, h2, h3⟩ := babai_exists_prefix Lm p k hp d
  refine ⟨a, w, h1, h2, h3, ?_⟩
  have hterm : ∀ i ∈ range d, w i ^ 2 * E i ≤ if k ≤ i then (1 / 4) * E i else 0 := by
    intro i hi
    have hid : i < d := Finset.mem_range.mp hi
    by_cases hki : k ≤ i
    · rw [if_pos hki]
      have hw : w i ^ 2 ≤ 1 / 4 := by
        have h := h3 i hid
        have hsq : |w i| ^ 2 ≤ (1 / 2) ^ 2 := by
          apply pow_le_pow_left₀ (abs_nonneg _) h
        rw [sq_abs] at hsq
        linarith
      nlinarith [hE i]
    · rw [if_neg hki]
      have hz : w i = 0 := h2 i hid (by omega)
      rw [hz]; simp
  calc ∑ i ∈ range d, w i ^ 2 * E i
      ≤ ∑ i ∈ range d, (if k ≤ i then (1 / 4) * E i else 0) := Finset.sum_le_sum hterm
    _ = ∑ i ∈ (range d).filter (fun i => k ≤ i), (1 / 4) * E i := by
        rw [Finset.sum_filter]
    _ = (1 / 4) * ∑ i ∈ (range d).filter (fun i => k ≤ i), E i := by
        rw [Finset.mul_sum]

/-- Rounding in an LDL form with the diagonal `D` itself: the residual `w = L⁻¹ (p - a)` satisfies
`∑ w i ^ 2 / D i ≤ (1/4) ∑_{k ≤ i < d} 1 / D i`.  This is the statement used for the flag of
`Λ = ℤ⁵ ∩ v^⊥`: `D i = μ_i²`. -/
theorem babai_round_D (Lm : ℕ → ℕ → ℝ) (D : ℕ → ℝ) (hD : ∀ i, 0 < D i) (p : ℕ → ℝ) (k d : ℕ)
    (hp : ∀ i, i < k → ∃ n : ℤ, p i = n) :
    ∃ (a : ℕ → ℤ) (w : ℕ → ℝ),
      (∀ i, i < d → p i - a i = w i + ∑ j ∈ range i, Lm i j * w j) ∧
      (∀ i, i < d → i < k → w i = 0) ∧
      (∀ i, i < d → |w i| ≤ 1 / 2) ∧
      ∑ i ∈ range d, w i ^ 2 / D i ≤ (1 / 4) * ∑ i ∈ (range d).filter (fun i => k ≤ i), 1 / D i := by
  obtain ⟨a, w, h1, h2, h3, h4⟩ :=
    babai_round Lm (fun i => 1 / D i) (fun i => by have := hD i; positivity) p k d hp
  refine ⟨a, w, h1, h2, h3, ?_⟩
  have e : ∀ i, w i ^ 2 / D i = w i ^ 2 * (1 / D i) := fun i => by ring
  simpa only [e] using h4

/-- Nearest plane in the orthogonal-basis presentation.  Let `b*_0, …, b*_{d-1}` be orthogonal,
`b_i = ∑_{j ≤ i} U i j b*_j` with `U i i = 1`.  A point has coordinates `c_j` in the basis `b*`; the
integer combination `∑ a_i b_i` has `b*_j`-coordinate `∑_{i ≥ j} a_i U i j`.  There are integers `a`
(chosen from the top index down) with every residual coordinate within `1/2`. -/
theorem nearest_plane_coords (U : ℕ → ℕ → ℝ) (hU : ∀ i, U i i = 1) :
    ∀ (d : ℕ) (c : ℕ → ℝ), ∃ a : ℕ → ℤ,
      ∀ j, j < d → |c j - ∑ i ∈ Ico j d, (a i : ℝ) * U i j| ≤ 1 / 2 := by
  intro d
  induction d with
  | zero => intro c; exact ⟨fun _ => 0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ d ih =>
    intro c
    obtain ⟨a0, ha0⟩ := ih (fun j => c j - (round (c d) : ℝ) * U d j)
    refine ⟨fun i => if i = d then round (c d) else a0 i, ?_⟩
    intro j hj
    by_cases hjd : j = d
    · subst hjd
      have hico : Ico j (j + 1) = {j} := by simp
      rw [hico, Finset.sum_singleton]
      simp only [if_true, hU j, mul_one]
      exact abs_sub_round (c j)
    · have hjlt : j < d := by omega
      rw [Finset.sum_Ico_succ_top (by omega : j ≤ d)]
      have hsum : ∑ i ∈ Ico j d, ((if i = d then round (c d) else a0 i : ℤ) : ℝ) * U i j
          = ∑ i ∈ Ico j d, (a0 i : ℝ) * U i j := by
        apply Finset.sum_congr rfl
        intro i hi
        have hid : i ≠ d := ne_of_lt (Finset.mem_Ico.mp hi).2
        simp [hid]
      rw [hsum]
      simp only [if_true]
      have := ha0 j hjlt
      have e : c j - (∑ i ∈ Ico j d, (a0 i : ℝ) * U i j + (round (c d) : ℝ) * U d j)
          = (c j - (round (c d) : ℝ) * U d j) - ∑ i ∈ Ico j d, (a0 i : ℝ) * U i j := by ring
      rw [e]
      exact this

/-- Squared-distance form: `∑_j r_j² |b*_j|² ≤ (1/4) ∑_j |b*_j|²` for the residual coordinates `r_j`
of `nearest_plane_coords` and any nonnegative weights `E j = |b*_j|²`. -/
theorem nearest_plane_sq (U : ℕ → ℕ → ℝ) (hU : ∀ i, U i i = 1) (E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i)
    (d : ℕ) (c : ℕ → ℝ) :
    ∃ a : ℕ → ℤ, (∀ j, j < d → |c j - ∑ i ∈ Ico j d, (a i : ℝ) * U i j| ≤ 1 / 2) ∧
      ∑ j ∈ range d, (c j - ∑ i ∈ Ico j d, (a i : ℝ) * U i j) ^ 2 * E j
        ≤ (1 / 4) * ∑ j ∈ range d, E j := by
  obtain ⟨a, ha⟩ := nearest_plane_coords U hU d c
  refine ⟨a, ha, ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjd : j < d := Finset.mem_range.mp hj
  have h := ha j hjd
  have hsq : |c j - ∑ i ∈ Ico j d, (a i : ℝ) * U i j| ^ 2 ≤ (1 / 2) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at hsq
  nlinarith [hE j]

end L5S3
end LRSpectrumFull
