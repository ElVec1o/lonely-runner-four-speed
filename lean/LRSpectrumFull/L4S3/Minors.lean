/-
# L4S3.Minors : discharge of `Dq_minors` and `covolume`

* `leadMinor_cast_prod` : `(leadMinor (gram F) j : ℚ) = ∏_k (if k < j then Dq k else 1)`
  (determinant of the padded leading block of `L D Lᵀ`).
* `Dq_minors_thm`       : `Dq i = G_{i+1} / G_i`  (exact statement of the field `Dq_minors`).
* `gram_det_eq_normsq`  : `det (gram F) = v·v` for a primitive `v` (integer; unimodular completion,
  `det H_ext · det W = v·v` with `W = [R | v]` of determinant `±1`, `H_ext = [H ; v]`).
* `covolume_thm`        : `∏ Dq = v·v` (exact statement of the field `covolume`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.Skeleton
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.EuclideanDomain.Int

namespace LRSpectrumFull
namespace L4S3

open Finset Matrix

/-! ## Part 1: `Dq_minors` -/

theorem leadMinor_cast (M : Matrix (Fin 3) (Fin 3) ℤ) (j : ℕ) :
    ((leadMinor M j : ℤ) : ℚ) =
      (Matrix.of fun a b : Fin 3 =>
        if a.val < j ∧ b.val < j then (M a b : ℚ) else if a = b then (1 : ℚ) else 0).det := by
  unfold leadMinor
  rw [show (((Matrix.of fun a b : Fin 3 =>
      if a.val < j ∧ b.val < j then M a b else if a = b then 1 else 0).det : ℤ) : ℚ)
      = (Int.castRingHom ℚ) (Matrix.of fun a b : Fin 3 =>
      if a.val < j ∧ b.val < j then M a b else if a = b then 1 else 0).det from rfl]
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem leadMinor_cast_prod {v : V4} (F : FlagData v) (j : ℕ) :
    ((leadMinor (gram F) j : ℤ) : ℚ) = ∏ k : Fin 3, (if k.val < j then F.Dq k else 1) := by
  rw [leadMinor_cast]
  set Lp : Matrix (Fin 3) (Fin 3) ℚ :=
    Matrix.of fun a b => if a.val < j then F.Lq a b else if a = b then 1 else 0 with hLp
  set Dp : Fin 3 → ℚ := fun k => if k.val < j then F.Dq k else 1 with hDp
  have hfac : (Matrix.of fun a b : Fin 3 =>
        if a.val < j ∧ b.val < j then ((gram F a b : ℤ) : ℚ) else if a = b then (1 : ℚ) else 0)
      = Lp * Matrix.diagonal Dp * Lpᵀ := by
    ext a b
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply, hLp]
    by_cases ha : a.val < j
    · by_cases hb : b.val < j
      · simp only [ha, hb, and_self, if_true]
        have : ((gram F a b : ℤ) : ℚ) = ∑ k, F.Lq a k * F.Dq k * F.Lq b k := by
          simpa [gram] using F.hLDL a b
        rw [this]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k.val < j
        · simp [hDp, hk]
        · have hak : a < k := by
            rw [Fin.lt_def]; omega
          simp [F.hLlow a k hak]
      · simp only [ha, hb, and_false, if_true, if_false]
        have hab : a ≠ b := fun h => hb (h ▸ ha)
        simp only [hab, if_false]
        apply (Finset.sum_eq_zero _).symm
        intro k _
        by_cases hkb : b = k
        · subst hkb
          have : a < b := by rw [Fin.lt_def]; omega
          simp [F.hLlow a b this]
        · simp [hkb]
    · by_cases hb : b.val < j
      · simp only [ha, hb, and_false, false_and, if_true, if_false]
        have hab : a ≠ b := fun h => ha (h ▸ hb)
        simp only [hab, if_false]
        apply (Finset.sum_eq_zero _).symm
        intro k _
        by_cases hka : a = k
        · subst hka
          have : b < a := by rw [Fin.lt_def]; omega
          simp [F.hLlow b a this]
        · simp [hka]
      · simp only [ha, hb, false_and, if_false]
        have hDa : Dp a = 1 := by simp [hDp, ha]
        by_cases hab : a = b
        · subst hab
          simp only [if_true]
          rw [Finset.sum_eq_single a]
          · simp [hDa]
          · intro k _ hk; simp [Ne.symm hk]
          · simp
        · simp only [hab, if_false]
          apply (Finset.sum_eq_zero _).symm
          intro k _
          by_cases hka : a = k
          · subst hka
            simp [hab, Ne.symm hab]
          · simp [hka]
  rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
  have hdetL : Lp.det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · apply Finset.prod_eq_one
      intro a _
      by_cases ha : a.val < j
      · simp [hLp, ha, F.hLunit]
      · simp [hLp, ha]
    · intro a b hab
      have hab' : a < b := hab
      by_cases ha : a.val < j
      · simp [hLp, ha, F.hLlow a b hab']
      · simp [hLp, ha, ne_of_lt hab']
  rw [hdetL]
  simp

theorem prod_pos_aux {v : V4} (F : FlagData v) (j : ℕ) :
    0 < ∏ k : Fin 3, (if k.val < j then F.Dq k else (1 : ℚ)) := by
  apply Finset.prod_pos
  intro k _
  split_ifs
  · exact F.hDpos k
  · exact one_pos

theorem Dq_minors_thm (v : V4) (F : FlagData v) (i : Fin 3) :
    F.Dq i = (leadMinor (gram F) (i.val + 1) : ℚ) / (leadMinor (gram F) i.val : ℚ) := by
  rw [leadMinor_cast_prod, leadMinor_cast_prod]
  have hp := prod_pos_aux F i.val
  rw [eq_div_iff (ne_of_gt hp)]
  fin_cases i <;> simp [Fin.prod_univ_three] <;> ring

/-! ## Part 2: `covolume` -/

/-- Bezout for a primitive vector. -/
theorem exists_dual (v : V4) (hv : Primitive v) : ∃ u : V4, dot u v = 1 := by
  set I : Ideal ℤ := Ideal.span (Set.range v) with hI
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal I)
  have hdvd : ∀ i, g ∣ v i := by
    intro i
    have : v i ∈ I := Ideal.subset_span (Set.mem_range_self i)
    rw [hg, Submodule.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by rw [← hc]; ring⟩
  have hg1 : g = 1 ∨ g = -1 := hv g hdvd
  have hone : (1 : ℤ) ∈ I := by
    rw [hg, Submodule.mem_span_singleton]
    rcases hg1 with h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
  have := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (by simpa [hI, Ideal.span] using hone)
  obtain ⟨c, hc⟩ := this
  exact ⟨c, by simpa [dot, mul_comm] using hc⟩

theorem primitive_ne_zero {v : V4} (hv : Primitive v) : ∃ j, v j ≠ 0 := by
  by_contra h
  push_neg at h
  have := hv 2 (fun i => by rw [h i]; exact dvd_zero _)
  omega

theorem dot_self_pos {v : V4} (hv : Primitive v) : 0 < dot v v := by
  obtain ⟨j, hj⟩ := primitive_ne_zero hv
  unfold dot
  have h1 : 0 < v j * v j := mul_self_pos.mpr hj
  have h2 : v j * v j ≤ ∑ i, v i * v i :=
    Finset.single_le_sum (f := fun i => v i * v i) (fun i _ => mul_self_nonneg _) (Finset.mem_univ j)
  omega

theorem det_lower4 (A : Matrix (Fin 4) (Fin 4) ℤ) (h : ∀ a c, a < c → A a c = 0) :
    A.det = ∏ a, A a a := by
  rw [Matrix.det_of_lowerTriangular]
  intro a c hac
  exact h a c hac

/-- Rows `h_0..h_3, r`. -/
def rowsExt {v : V4} (F : FlagData v) (r : V4) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun a b => (Fin.snoc (α := fun _ => V4) F.h r : Fin 4 → V4) a b

/-- Columns `R_0..R_3, v`. -/
def colsExt {v : V4} (F : FlagData v) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun b c => (Fin.snoc (α := fun _ => V4) (fun l : Fin 3 => fun b' => F.R b' l) v :
    Fin 4 → V4) c b

theorem rows_last {v : V4} (F : FlagData v) (r : V4) (b : Fin 4) :
    rowsExt F r (Fin.last 3) b = r b := by
  simp only [rowsExt, Matrix.of_apply, Fin.snoc_last]

theorem rows_cast {v : V4} (F : FlagData v) (r : V4) (i : Fin 3) (b : Fin 4) :
    rowsExt F r i.castSucc b = F.h i b := by
  simp only [rowsExt, Matrix.of_apply, Fin.snoc_castSucc]

theorem cols_last {v : V4} (F : FlagData v) (b : Fin 4) :
    colsExt F b (Fin.last 3) = v b := by
  simp only [colsExt, Matrix.of_apply, Fin.snoc_last]

theorem cols_cast {v : V4} (F : FlagData v) (i : Fin 3) (b : Fin 4) :
    colsExt F b i.castSucc = F.R b i := by
  simp only [colsExt, Matrix.of_apply, Fin.snoc_castSucc]

theorem rowsExt_mul_colsExt {v : V4} (F : FlagData v) (r : V4) :
    (rowsExt F r * colsExt F).det = dot r v := by
  have hcc : ∀ i j : Fin 3, (rowsExt F r * colsExt F) i.castSucc j.castSucc
      = if i = j then 1 else 0 := by
    intro i j
    simp only [Matrix.mul_apply, rows_cast, cols_cast]
    exact F.hR i j
  have hcl : ∀ i : Fin 3, (rowsExt F r * colsExt F) i.castSucc (Fin.last 3) = 0 := by
    intro i
    simp only [Matrix.mul_apply, rows_cast, cols_last]
    have := F.hv i
    simpa [dot] using this
  have hll : (rowsExt F r * colsExt F) (Fin.last 3) (Fin.last 3) = dot r v := by
    simp only [Matrix.mul_apply, rows_last, cols_last, dot]
  rw [det_lower4]
  · rw [Fin.prod_univ_castSucc, hll]
    have h1 : ∀ i : Fin 3, (rowsExt F r * colsExt F) i.castSucc i.castSucc = 1 := by
      intro i; rw [hcc]; simp
    simp only [h1, Finset.prod_const_one, one_mul]
  · intro a c hac
    induction c using Fin.lastCases with
    | last =>
      induction a using Fin.lastCases with
      | last => exact absurd hac (lt_irrefl _)
      | cast j => exact hcl j
    | cast i =>
      induction a using Fin.lastCases with
      | last => exact absurd hac (not_lt.mpr (Fin.le_last _))
      | cast j =>
        have hji : j ≠ i := (Fin.castSucc_lt_castSucc_iff.mp hac).ne
        rw [hcc]; simp [hji]

theorem gram_det_eq_normsq {v : V4} (F : FlagData v) (hv : Primitive v) :
    (gram F).det = dot v v := by
  obtain ⟨u, hu⟩ := exists_dual v hv
  have hU := rowsExt_mul_colsExt F u
  have hV := rowsExt_mul_colsExt F v
  rw [hu, Matrix.det_mul] at hU
  rw [Matrix.det_mul] at hV
  have hw : (colsExt F).det = 1 ∨ (colsExt F).det = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hU with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hz : ∀ j : Fin 3, (rowsExt F v * (rowsExt F v)ᵀ) (Fin.last 3) j.castSucc = 0 := by
    intro j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, rows_last, rows_cast]
    have := F.hv j
    simpa [dot, mul_comm] using this
  have hll : (rowsExt F v * (rowsExt F v)ᵀ) (Fin.last 3) (Fin.last 3) = dot v v := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, rows_last, dot]
  have hsub : ((rowsExt F v * (rowsExt F v)ᵀ).submatrix Fin.castSucc Fin.castSucc) = gram F := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, rows_cast, gram,
      Matrix.of_apply, dot]
  have hblock : (rowsExt F v * (rowsExt F v)ᵀ).det = (gram F).det * dot v v := by
    rw [Matrix.det_succ_row _ (Fin.last 3), Fin.sum_univ_castSucc]
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last,
      Fin.succAbove_last, hsub, hll]
    simp
    ring
  rw [Matrix.det_mul, Matrix.det_transpose] at hblock
  have hn : dot v v ≠ 0 := ne_of_gt (dot_self_pos hv)
  have hsq : (rowsExt F v).det * (rowsExt F v).det = dot v v * dot v v := by
    rcases hw with h | h
    · rw [h] at hV; simp at hV; rw [hV]
    · rw [h] at hV
      have : (rowsExt F v).det = -dot v v := by linarith
      rw [this]; ring
  have : (gram F).det * dot v v = dot v v * dot v v := by linarith
  exact mul_right_cancel₀ hn this

theorem covolume_thm (v : V4) (F : FlagData v) (hv : Primitive v) :
    (∏ i, F.Dq i) = (dot v v : ℚ) := by
  have h := leadMinor_cast_prod F 3
  have e : leadMinor (gram F) 3 = (gram F).det := by
    unfold leadMinor
    congr 1
    ext a b
    simp
  rw [e, gram_det_eq_normsq F hv] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro k _
  simp [k.isLt]

end L4S3
end LRSpectrumFull
