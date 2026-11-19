/-
# L4S3.GramQ : Gram determinants of rational families (nonnegativity, nondegeneracy, shear)

Generic facts about `GmQ p = (p_a · p_b)_{a b}` for `p : Fin n → ℚ⁵`, and their transport to the integer
Gram determinant `gF` (and to `gramDetList`) of a family `Fin n → ℤ⁴`:

* `GmQ_det_nonneg`  : `0 ≤ det (GmQ p)` (via `PosSemidef` over `ℝ`);
* `GmQ_det_ne_zero` : `ℚ`-independence of `p` gives `det (GmQ p) ≠ 0` (quadratic form argument);
* `GmQ_shear`       : if `q_r = ∑_c A_{rc} p_c` then `det (GmQ q) = (det A)² det (GmQ p)`;
* `gramDetList_ofFn`, `gramDetList_take_append` : the bridge between the list form used in `Greedy`
  and the `Fin n` form (`E j h u` is the family `h_0, …, h_{j-1}, u`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.FlagBasis
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

namespace LRSpectrumFull
namespace L4S3

open Finset Matrix

/-- Gram matrix of a finite family of rational vectors in `ℚ⁵`. -/
def GmQ {n : ℕ} (p : Fin n → Fin 4 → ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => dotProduct (p a) (p b)

theorem GmQ_det_nonneg {n : ℕ} (p : Fin n → Fin 4 → ℚ) : 0 ≤ (GmQ p).det := by
  set M : Matrix (Fin n) (Fin 4) ℝ := Matrix.of fun a k => ((p a k : ℚ) : ℝ) with hM
  have h1 : (Rat.castHom ℝ).mapMatrix (GmQ p) = M * Mᴴ := by
    ext a b
    simp [GmQ, hM, Matrix.mul_apply, dotProduct, conjTranspose_apply]
  have h2 : (((GmQ p).det : ℚ) : ℝ) = (M * Mᴴ).det := by
    rw [← h1]; exact RingHom.map_det (Rat.castHom ℝ) (GmQ p)
  have h3 : 0 ≤ (M * Mᴴ).det := (posSemidef_self_mul_conjTranspose M).det_nonneg
  have h4 : (0 : ℝ) ≤ (((GmQ p).det : ℚ) : ℝ) := by rw [h2]; exact h3
  exact_mod_cast h4

theorem GmQ_det_ne_zero {n : ℕ} (p : Fin n → Fin 4 → ℚ)
    (hp : ∀ c : Fin n → ℚ, ∑ a, c a • p a = 0 → ∀ a, c a = 0) : (GmQ p).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc, hGc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hq : dotProduct (∑ a, c a • p a) (∑ a, c a • p a) = 0 := by
    have e : dotProduct (∑ a, c a • p a) (∑ a, c a • p a) = dotProduct c ((GmQ p) *ᵥ c) := by
      simp only [GmQ, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      ring
    rw [e, hGc]; simp
  have hz : ∑ a, c a • p a = 0 := dotProduct_self_eq_zero.mp hq
  exact hc (funext fun a => hp c hz a)

theorem GmQ_shear {n : ℕ} (p q : Fin n → Fin 4 → ℚ) (A : Matrix (Fin n) (Fin n) ℚ)
    (h : ∀ r, q r = ∑ c, A r c • p c) : (GmQ q).det = A.det ^ 2 * (GmQ p).det := by
  have e : GmQ q = A * GmQ p * Aᵀ := by
    ext r s
    simp only [GmQ, Matrix.of_apply, h r, h s, Matrix.mul_apply, Matrix.transpose_apply]
    simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    ring
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring

/-! ## Integer families -/

/-- Integer Gram determinant of a family of integer vectors. -/
def gF {n : ℕ} (f : Fin n → V4) : ℤ := (Matrix.of fun a b => dot (f a) (f b)).det

theorem gF_cast {n : ℕ} (f : Fin n → V4) :
    ((gF f : ℤ) : ℚ) = (GmQ (fun a => castV (f a))).det := by
  have h1 : (Int.castRingHom ℚ).mapMatrix (Matrix.of fun a b => dot (f a) (f b))
      = GmQ (fun a => castV (f a)) := by
    ext a b
    simp [GmQ, dot_cast]
  have h2 := RingHom.map_det (Int.castRingHom ℚ) (Matrix.of fun a b => dot (f a) (f b))
  rw [h1] at h2
  simpa [gF] using h2

/-- Extension of a `Fin 3`-family to `ℕ` by zero. -/
def hN (h : Fin 3 → V4) (n : ℕ) : V4 := if hn : n < 3 then h ⟨n, hn⟩ else fun _ => 0

/-- The family `h_0, …, h_{j-1}, u`. -/
def Ef (j : ℕ) (h : Fin 3 → V4) (u : V4) : Fin (j + 1) → V4 :=
  fun i => if i.val < j then hN h i.val else u

theorem gramDetList_ofFn {n : ℕ} (f : Fin n → V4) : gramDetList (List.ofFn f) = gF f := by
  unfold gramDetList gF
  rw [← Matrix.det_submatrix_equiv_self (finCongr (List.length_ofFn (f := f)).symm)]
  congr 1
  ext a b
  simp [Matrix.submatrix_apply, List.get_ofFn, finCongr_apply]

theorem take_append_eq (j : ℕ) (hj : j ≤ 3) (h : Fin 3 → V4) (u : V4) :
    (List.ofFn h).take j ++ [u] = List.ofFn (Ef j h u) := by
  have hl : (List.take j (List.ofFn h)).length = j := by simp [List.length_take, hj]
  apply List.ext_getElem
  · simp [hl]; exact hj
  · intro i h1 h2
    have h1' : i < j + 1 := by simp at h1; omega
    rw [List.getElem_append]
    by_cases hij : i < j
    · have hij' : i < (List.take j (List.ofFn h)).length := by omega
      rw [dif_pos hij', List.getElem_take, List.getElem_ofFn, List.getElem_ofFn]
      simp [Ef, hN, hij, show i < 3 by omega]
    · have hi : i = j := by omega
      subst hi
      have hij' : ¬ i < (List.take i (List.ofFn h)).length := by omega
      rw [dif_neg hij', List.getElem_ofFn]
      simp [Ef]

theorem take_succ_eq (j : ℕ) (hj : j < 3) (h : Fin 3 → V4) :
    (List.ofFn h).take (j + 1) = List.ofFn (Ef j h (h ⟨j, hj⟩)) := by
  have e := take_append_eq j hj.le h (h ⟨j, hj⟩)
  rw [← e]
  have hl : (List.take j (List.ofFn h)).length = j := by simp [List.length_take, hj.le]
  apply List.ext_getElem
  · simp [hl]; omega
  · intro i h1 h2
    rw [List.getElem_append]
    simp only [List.length_take, List.length_ofFn] at h1
    by_cases hij : i < j
    · have hij' : i < (List.take j (List.ofFn h)).length := by omega
      rw [dif_pos hij', List.getElem_take, List.getElem_take]
    · have hi : i = j := by omega
      subst hi
      have hij' : ¬ i < (List.take i (List.ofFn h)).length := by omega
      rw [dif_neg hij', List.getElem_take, List.getElem_ofFn]
      simp

end L4S3
end LRSpectrumFull
