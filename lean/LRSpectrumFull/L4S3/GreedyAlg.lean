/-
# L4S3.GreedyAlg : prefix-span and Gram-determinant calculus for the greedy chain

`ℕ`-indexed forms of the prefix span (`InQN`), prefix independence (`IndN`) and the shear identity
`gF (h_0..h_{j-1}, u) = t² gF (h_0..h_{j-1}, w)` when `u = ∑ a_n h_n + t w`.  Positivity of
`gF (h_0..h_{j-1}, u)` when the prefix is independent and `u` is outside its rational span.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.GramQ
import LRSpectrumFull.L4S3.Ratio34

namespace LRSpectrumFull
namespace L4S3

open Finset Matrix

/-- `u` lies in the rational span of `h_0..h_{j-1}` (`ℕ`-indexed form). -/
def InQN (j : ℕ) (h : Fin 3 → V4) (u : V4) : Prop :=
  ∃ a : ℕ → ℚ, ∀ k, (u k : ℚ) = ∑ n ∈ range j, a n * (hN h n k : ℚ)

/-- `h_0..h_{j-1}` are `ℚ`-independent. -/
def IndN (j : ℕ) (h : Fin 3 → V4) : Prop :=
  ∀ a : ℕ → ℚ, (∀ k, ∑ n ∈ range j, a n * (hN h n k : ℚ) = 0) → ∀ n < j, a n = 0

theorem hN_lt (h : Fin 3 → V4) (i : Fin 3) : hN h i.val = h i := by
  simp [hN, i.2]

theorem prefix_sum_key (h : Fin 3 → V4) (j : ℕ) (hj : j ≤ 3) (a : ℕ → ℚ) (k : Fin 4) :
    (∑ i : Fin 3, if i.val < j then a i.val * (h i k : ℚ) else 0)
      = ∑ n ∈ range j, a n * (hN h n k : ℚ) := by
  have e1 : (∑ i : Fin 3, if i.val < j then a i.val * (h i k : ℚ) else 0)
      = ∑ i : Fin 3, (fun n : ℕ => if n < j then a n * (hN h n k : ℚ) else 0) i.val := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [hN_lt]
  rw [e1, Fin.sum_univ_eq_sum_range (fun n : ℕ => if n < j then a n * (hN h n k : ℚ) else 0) 3,
    ← Finset.sum_filter]
  have : (range 3).filter (· < j) = range j := by
    ext n; simp; omega
  rw [this]

theorem inQSpanPrefix_iff (h : Fin 3 → V4) (j : ℕ) (hj : j ≤ 3) (u : V4) :
    InQSpanPrefix h j u ↔ InQN j h u := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun n => if hn : n < 3 then c ⟨n, hn⟩ else 0, fun k => ?_⟩
    rw [hc k, ← prefix_sum_key h j hj]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [i.2]
  · rintro ⟨a, ha⟩
    refine ⟨fun i => a i.val, fun k => ?_⟩
    rw [ha k, ← prefix_sum_key h j hj]

/-! ## Shear identity -/

theorem gF_Ef_shear (j : ℕ) (h : Fin 3 → V4) (u w : V4) (a : ℕ → ℚ) (t : ℚ)
    (hu : ∀ k, (u k : ℚ) = (∑ n ∈ range j, a n * (hN h n k : ℚ)) + t * (w k : ℚ)) :
    ((gF (Ef j h u) : ℤ) : ℚ) = t ^ 2 * ((gF (Ef j h w) : ℤ) : ℚ) := by
  rw [gF_cast, gF_cast]
  let A : Matrix (Fin (j + 1)) (Fin (j + 1)) ℚ := Matrix.of fun r c =>
    if r.val < j then (if r = c then 1 else 0)
    else (if c.val < j then a c.val else if c.val = j then t else 0)
  have hA : A.det = t := by
    rw [Matrix.det_of_lowerTriangular]
    · rw [Fin.prod_univ_castSucc]
      have h1 : ∀ i : Fin j, A (Fin.castSucc i) (Fin.castSucc i) = 1 := by
        intro i; simp [A]
      have h2 : A (Fin.last j) (Fin.last j) = t := by simp [A]
      rw [h2]
      simp [h1]
    · intro r c hrc
      have hrc' : r < c := OrderDual.toDual_lt_toDual.mp hrc
      have hr : r.val < j := by
        have := c.2; have := hrc'.le; omega
      have hrc'' : r ≠ c := ne_of_lt hrc'
      simp [A, hr, hrc'']
  have hq := GmQ_shear (fun i => castV (Ef j h w i)) (fun i => castV (Ef j h u i)) A (by
    intro r
    funext k
    by_cases hr : r.val < j
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp [A, hr, Ef, castV]
    · have hrj : r.val = j := by have := r.2; omega
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have e1 : (∑ c : Fin (j + 1), A r c * castV (Ef j h w c) k)
          = ∑ n ∈ range (j + 1),
              (fun n : ℕ => (if n < j then a n else if n = j then t else 0) *
                (if n < j then (hN h n k : ℚ) else (w k : ℚ))) n := by
        rw [← Fin.sum_univ_eq_sum_range (fun n : ℕ =>
          (if n < j then a n else if n = j then t else 0) *
            (if n < j then (hN h n k : ℚ) else (w k : ℚ))) (j + 1)]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        by_cases hc : c.val < j
        · simp [A, hr, Ef, castV, hc]
        · simp [A, hr, Ef, castV, hc]
      rw [e1, Finset.sum_range_succ]
      have e2 : (∑ n ∈ range j,
          (fun n : ℕ => (if n < j then a n else if n = j then t else 0) *
            (if n < j then (hN h n k : ℚ) else (w k : ℚ))) n)
          = ∑ n ∈ range j, a n * (hN h n k : ℚ) := by
        refine Finset.sum_congr rfl (fun n hn => ?_)
        have := Finset.mem_range.mp hn
        simp [this]
      rw [e2]
      simp only [lt_irrefl, if_false, if_true]
      have := hu k
      simp [Ef, castV, hr, this])
  rw [hq, hA]

/-! ## Nonnegativity and positivity -/

theorem gF_Ef_nonneg (j : ℕ) (h : Fin 3 → V4) (u : V4) : 0 ≤ gF (Ef j h u) := by
  have h1 := GmQ_det_nonneg (fun a => castV (Ef j h u a))
  rw [← gF_cast] at h1
  exact_mod_cast h1

theorem gF_Ef_pos (j : ℕ) (h : Fin 3 → V4) (u : V4) (hI : IndN j h) (hu : ¬ InQN j h u) :
    0 < gF (Ef j h u) := by
  have hne : gF (Ef j h u) ≠ 0 := by
    intro h0
    have h1 : (GmQ (fun a => castV (Ef j h u a))).det = 0 := by
      rw [← gF_cast, h0]; simp
    refine GmQ_det_ne_zero (fun a => castV (Ef j h u a)) ?_ h1
    intro c hc
    set c' : ℕ → ℚ := fun n => if hn : n < j + 1 then c ⟨n, hn⟩ else 0 with hc'
    have hc'a : ∀ a : Fin (j + 1), c' a.val = c a := fun a => by
      show (if hn : a.val < j + 1 then c ⟨a.val, hn⟩ else 0) = c a
      rw [dif_pos a.2]
    have hk : ∀ k : Fin 4, (∑ n ∈ range j, c' n * (hN h n k : ℚ)) + c' j * (u k : ℚ) = 0 := by
      intro k
      have h2 := congr_fun hc k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h2
      have h3 : (∑ a : Fin (j + 1), c a * castV (Ef j h u a) k)
          = ∑ n ∈ range (j + 1), (fun n : ℕ => c' n * (if n < j then (hN h n k : ℚ) else (u k : ℚ))) n := by
        rw [← Fin.sum_univ_eq_sum_range (fun n : ℕ =>
          c' n * (if n < j then (hN h n k : ℚ) else (u k : ℚ))) (j + 1)]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [hc'a a]
        simp only [Ef, castV]
        split_ifs <;> rfl
      rw [h3, Finset.sum_range_succ] at h2
      have h4 : (∑ n ∈ range j, (fun n : ℕ => c' n * (if n < j then (hN h n k : ℚ) else (u k : ℚ))) n)
          = ∑ n ∈ range j, c' n * (hN h n k : ℚ) := by
        refine Finset.sum_congr rfl (fun n hn => ?_)
        simp [Finset.mem_range.mp hn]
      rw [h4] at h2
      simpa using h2
    by_cases hj : c' j = 0
    · have hz : ∀ k, ∑ n ∈ range j, c' n * (hN h n k : ℚ) = 0 := by
        intro k; have := hk k; rw [hj] at this; simpa using this
      have hzero := hI c' hz
      intro a
      by_cases ha : a.val < j
      · have h5 := hzero a.val ha
        rw [hc'a a] at h5; exact h5
      · have haj : a.val = j := by have := a.2; omega
        have h5 := hc'a a
        rw [haj] at h5
        rw [← h5, hj]
    · exfalso
      apply hu
      refine ⟨fun n => - c' n / c' j, fun k => ?_⟩
      have := hk k
      have e2 : (∑ n ∈ range j, (-c' n / c' j) * (hN h n k : ℚ))
          = (-1 / c' j) * ∑ n ∈ range j, c' n * (hN h n k : ℚ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun n _ => ?_); ring
      rw [e2]
      field_simp
      linarith
  exact lt_of_le_of_ne (gF_Ef_nonneg j h u) (Ne.symm hne)

end L4S3
end LRSpectrumFull
