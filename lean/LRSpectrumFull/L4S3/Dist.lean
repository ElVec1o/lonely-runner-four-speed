/-
# L4S3.Dist : discharge of the `stage_dist` field of `FlagGeometry`

Instantiation of the nearest-plane rounding
`babai_round_D` (`Babai.lean`) to the flag of a primitive `v ∈ ℤ⁴`:

* `ker_eq_span`          : `ker H = ℝ v` when `H R = I₄` (rank-nullity) and `v ≠ 0`, `H v = 0`.
* `stage_dist_core`      : pure real statement.  `H` a real `3 × 4` matrix with right inverse `R`,
  `v ∈ ker H` nonzero, `H Hᵀ = L D Lᵀ` with `L` unit lower triangular and `D > 0`, a point `x` with
  `(H x)_i ∈ ℤ` for `i < k`.  Then there are integers `a` and a real `t` with
  `‖x - R a - t v‖² ≤ (1/4) ∑_{i ≥ k} 1 / D_i`.
* `stage_dist_thm`       : the same for `FlagData v` (the exact statement of the field `stage_dist`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.Skeleton
import LRSpectrumFull.L5S3.Babai
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Fin

namespace LRSpectrumFull
namespace L4S3

open Finset Matrix LRSpectrumFull.L5S3

/-! ## The kernel of `H` is the line `ℝ v` -/

theorem ker_eq_span (Hr : Matrix (Fin 3) (Fin 4) ℝ) (Rr : Matrix (Fin 4) (Fin 3) ℝ)
    (hHR : Hr * Rr = 1) (vr : Fin 4 → ℝ) (hv0 : vr ≠ 0) (hHv : Hr *ᵥ vr = 0)
    (r : Fin 4 → ℝ) (hr : Hr *ᵥ r = 0) : ∃ t : ℝ, r = t • vr := by
  let f : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.mulVecLin Hr
  have hsurj : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨Rr *ᵥ y, ?_⟩
    simp [f, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hHR]
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [hsurj, finrank_top] at hrank
  simp only [Module.finrank_fin_fun] at hrank
  have hker : Module.finrank ℝ (LinearMap.ker f) = 1 := by omega
  have hvk : vr ∈ LinearMap.ker f := by
    simp [f, Matrix.mulVecLin_apply, hHv]
  have hrk : r ∈ LinearMap.ker f := by
    simp [f, Matrix.mulVecLin_apply, hr]
  have hnz : (⟨vr, hvk⟩ : LinearMap.ker f) ≠ 0 := by
    intro h
    apply hv0
    exact congrArg Subtype.val h
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨vr, hvk⟩ : LinearMap.ker f) hnz).mp hker
    ⟨r, hrk⟩
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simpa using this.symm

/-! ## Extension by a constant and the nearest-plane step -/

/-- Extension of a `Fin 3` array to `ℕ` by a constant. -/
def ext3 (f : Fin 3 → ℝ) (d : ℝ) : ℕ → ℝ := fun i => if h : i < 3 then f ⟨i, h⟩ else d

theorem ext3_val (f : Fin 3 → ℝ) (d : ℝ) (i : Fin 3) : ext3 f d i.val = f i := by
  simp [ext3, i.isLt]

/-- Extension of a `Fin 3 × Fin 3` array to `ℕ × ℕ` by zero. -/
def ext33 (L : Matrix (Fin 3) (Fin 3) ℝ) : ℕ → ℕ → ℝ :=
  fun i j => if h : i < 3 ∧ j < 3 then L ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

theorem ext33_val (L : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) : ext33 L i.val j.val = L i j := by
  simp [ext33, i.isLt, j.isLt]

/-- Core of `stage_dist`, pure real statement. -/
theorem stage_dist_core
    (Hr : Matrix (Fin 3) (Fin 4) ℝ) (Rr : Matrix (Fin 4) (Fin 3) ℝ) (hHR : Hr * Rr = 1)
    (vr : Fin 4 → ℝ) (hv0 : vr ≠ 0) (hHv : Hr *ᵥ vr = 0)
    (Lr : Matrix (Fin 3) (Fin 3) ℝ) (Dr : Fin 3 → ℝ)
    (hL1 : ∀ i, Lr i i = 1) (hL0 : ∀ i j, i < j → Lr i j = 0) (hD : ∀ i, 0 < Dr i)
    (hG : Hr * Hrᵀ = Lr * Matrix.diagonal Dr * Lrᵀ)
    (x : Fin 4 → ℝ) (k : ℕ) (hx : ∀ i : Fin 3, i.val < k → ∃ n : ℤ, (Hr *ᵥ x) i = n) :
    ∃ (a : Fin 3 → ℤ) (t : ℝ),
      ∑ j, (x j - (Rr *ᵥ (fun l => (a l : ℝ))) j - t * vr j) ^ 2
        ≤ 1 / 4 * ∑ i : Fin 3, (if k ≤ i.val then 1 / Dr i else 0) := by
  -- Babai step
  have hD' : ∀ i, 0 < ext3 Dr 1 i := by
    intro i
    by_cases hi : i < 3
    · have := hD ⟨i, hi⟩
      simpa [ext3, hi] using this
    · simp [ext3, hi]
  have hp : ∀ i, i < k → ∃ n : ℤ, ext3 (Hr *ᵥ x) 0 i = n := by
    intro i hik
    by_cases hi : i < 3
    · obtain ⟨n, hn⟩ := hx ⟨i, hi⟩ hik
      exact ⟨n, by simpa [ext3, hi] using hn⟩
    · exact ⟨0, by simp [ext3, hi]⟩
  obtain ⟨a, w, hE, h0, hb, hsum⟩ :=
    babai_round_D (ext33 Lr) (ext3 Dr 1) hD' (ext3 (Hr *ᵥ x) 0) k 3 hp
  set wf : Fin 3 → ℝ := fun i => w i.val with hwf
  set a' : Fin 3 → ℤ := fun i => a i.val with ha'
  -- relation q = L w
  have hq : ∀ m : Fin 3, (Hr *ᵥ x) m - (a' m : ℝ) = (Lr *ᵥ wf) m := by
    intro m
    have h1 := hE m.val m.isLt
    rw [ext3_val] at h1
    have h01 : Lr 0 1 = 0 := hL0 0 1 (by decide)
    have h02 : Lr 0 2 = 0 := hL0 0 2 (by decide)
    have h12 : Lr 1 2 = 0 := hL0 1 2 (by decide)
    have e10 : ext33 Lr 1 0 = Lr 1 0 := ext33_val Lr 1 0
    have e20 : ext33 Lr 2 0 = Lr 2 0 := ext33_val Lr 2 0
    have e21 : ext33 Lr 2 1 = Lr 2 1 := ext33_val Lr 2 1
    fin_cases m
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hL1, h01, h02, hwf, ha'] at h1 ⊢
      linarith
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hL1, h12, hwf, ha',
        Finset.sum_range_succ, e10] at h1 ⊢
      linarith
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hL1, hwf, ha',
        Finset.sum_range_succ, e20, e21] at h1 ⊢
      linarith
  -- invertibility of Lr
  have hdetL : Lr.det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · simp [hL1]
    · intro i j hij
      exact hL0 i j hij
  have hdetLt : IsUnit (Lrᵀ).det := by
    rw [Matrix.det_transpose, hdetL]; exact isUnit_one
  set c : Fin 3 → ℝ := (Lrᵀ)⁻¹ *ᵥ (fun m => wf m / Dr m) with hc
  have hLtc : Lrᵀ *ᵥ c = fun m => wf m / Dr m := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetLt, Matrix.one_mulVec]
  set s : Fin 4 → ℝ := Hrᵀ *ᵥ c with hs
  have hHs : Hr *ᵥ s = Lr *ᵥ wf := by
    have hd : Matrix.diagonal Dr *ᵥ (fun m => wf m / Dr m) = wf := by
      funext m
      have := hD m
      simp [Matrix.mulVec_diagonal]
      field_simp
    rw [hs, Matrix.mulVec_mulVec, hG, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hLtc, hd]
  -- the point y = x - R a
  set y : Fin 4 → ℝ := fun j => x j - (Rr *ᵥ (fun l => (a' l : ℝ))) j with hy
  have hHy : Hr *ᵥ y = Lr *ᵥ wf := by
    have : y = x - Rr *ᵥ (fun l => (a' l : ℝ)) := by funext j; simp [hy]
    rw [this, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hHR, Matrix.one_mulVec]
    funext m
    simp only [Pi.sub_apply]
    exact hq m
  have hker : Hr *ᵥ (y - s) = 0 := by
    rw [Matrix.mulVec_sub, hHy, hHs, sub_self]
  obtain ⟨t, ht⟩ := ker_eq_span Hr Rr hHR vr hv0 hHv (y - s) hker
  refine ⟨a', t, ?_⟩
  have hsj : ∀ j, x j - (Rr *ᵥ (fun l => (a' l : ℝ))) j - t * vr j = s j := by
    intro j
    have := congrFun ht j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [hy] at this
    linarith
  have hss : ∑ j, (x j - (Rr *ᵥ (fun l => (a' l : ℝ))) j - t * vr j) ^ 2 = s ⬝ᵥ s := by
    simp only [dotProduct, hsj, sq]
  -- s · s = ∑ w² / D
  have hsq : s ⬝ᵥ s = ∑ m : Fin 3, wf m ^ 2 / Dr m := by
    have e1 : c ᵥ* Hr = s := by rw [hs, Matrix.mulVec_transpose]
    have h1 : s ⬝ᵥ s = c ⬝ᵥ (Hr *ᵥ s) := by
      rw [Matrix.dotProduct_mulVec c Hr s, e1]
    have e2 : c ᵥ* Lr = fun m => wf m / Dr m := by rw [← hLtc, Matrix.mulVec_transpose]
    rw [h1, hHs, Matrix.dotProduct_mulVec c Lr wf, e2]
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hss, hsq]
  -- convert the Babai bound
  have hL : ∑ i ∈ range 3, w i ^ 2 / ext3 Dr 1 i = ∑ m : Fin 3, wf m ^ 2 / Dr m := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro m _
    rw [ext3_val]
  have hR : ∑ i ∈ (range 3).filter (fun i => k ≤ i), 1 / ext3 Dr 1 i
      = ∑ i : Fin 3, (if k ≤ i.val then 1 / Dr i else 0) := by
    rw [Finset.sum_filter, Finset.sum_range]
    apply Finset.sum_congr rfl
    intro m _
    rw [ext3_val]
  rw [hL, hR] at hsum
  exact hsum

/-- The field `stage_dist` of `FlagGeometry`, as a theorem. -/
theorem stage_dist_thm (v : V4) (F : FlagData v) (k : ℕ) (x : Fin 4 → ℝ) (hv : Primitive v)
    (hx : StageWitness F k x) :
    ∃ (z : V4) (t : ℝ), ∑ j, (x j - z j - t * v j) ^ 2 ≤ 1 / 4 * Sk F k := by
  have hne : ∃ j, v j ≠ 0 := by
    by_contra h
    push_neg at h
    have := hv 2 (fun i => by rw [h i]; exact dvd_zero _)
    omega
  set Hr : Matrix (Fin 3) (Fin 4) ℝ := Matrix.of fun i j => (F.h i j : ℝ) with hHr
  set Rr : Matrix (Fin 4) (Fin 3) ℝ := Matrix.of fun i j => (F.R i j : ℝ) with hRr
  set vr : Fin 4 → ℝ := fun j => (v j : ℝ) with hvr
  set Lr : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => (F.Lq i j : ℝ) with hLr
  set Dr : Fin 3 → ℝ := fun i => (F.Dq i : ℝ) with hDr
  have hHR : Hr * Rr = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have := F.hR i j
    have h2 : ((∑ k : Fin 4, F.h i k * F.R k j : ℤ) : ℝ) = ((if i = j then 1 else 0 : ℤ) : ℝ) := by
      rw [this]
    push_cast at h2
    simp only [hHr, hRr, Matrix.of_apply]
    rw [h2]
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have hv0 : vr ≠ 0 := by
    obtain ⟨j, hj⟩ := hne
    intro h
    apply hj
    have := congrFun h j
    simpa [hvr] using this
  have hHv : Hr *ᵥ vr = 0 := by
    funext i
    have := F.hv i
    have h2 : ((dot (F.h i) v : ℤ) : ℝ) = 0 := by rw [this]; simp
    simp only [dot] at h2
    push_cast at h2
    simpa [Matrix.mulVec, dotProduct, hHr, hvr] using h2
  have hG : Hr * Hrᵀ = Lr * Matrix.diagonal Dr * Lrᵀ := by
    ext i j
    have := F.hLDL i j
    have h2 : ((dot (F.h i) (F.h j) : ℤ) : ℝ) = ((∑ k, F.Lq i k * F.Dq k * F.Lq j k : ℚ) : ℝ) := by
      rw [← this]; simp
    simp only [dot] at h2
    push_cast at h2
    simp only [Matrix.mul_apply, Matrix.mul_diagonal, Matrix.transpose_apply, hHr, hLr, hDr,
      Matrix.of_apply]
    rw [h2]
    apply Finset.sum_congr rfl
    intro x _
    simp [Matrix.diagonal_apply]
  obtain ⟨a, t, hbound⟩ := stage_dist_core Hr Rr hHR vr hv0 hHv Lr Dr
    (fun i => by simp [hLr, F.hLunit])
    (fun i j hij => by simp [hLr, F.hLlow i j hij])
    (fun i => by simpa [hDr] using F.hDpos i) hG x k
    (fun i hi => by
      obtain ⟨n, hn⟩ := hx i hi
      exact ⟨n, by simpa [Matrix.mulVec, dotProduct, hHr] using hn⟩)
  refine ⟨fun j => ∑ l, F.R j l * a l, t, ?_⟩
  have hSk : Sk F k = ∑ i : Fin 3, (if k ≤ i.val then 1 / Dr i else 0) := rfl
  rw [hSk]
  refine le_trans (le_of_eq ?_) hbound
  apply Finset.sum_congr rfl
  intro j _
  congr 3
  simp [Matrix.mulVec, dotProduct, hRr]

end L4S3
end LRSpectrumFull
