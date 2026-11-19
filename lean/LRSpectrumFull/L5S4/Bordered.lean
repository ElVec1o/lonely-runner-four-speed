/-
# L5S4.Bordered : the integer norm formula of a child, `det Gram(L, y) = tᵀ adj(Gram K) t`

Same generic setting as `Compl`:
`H` rows of a saturated lattice `L` (`H S = 1`), `B` rows of its orthogonal complement `K` (`B Rr = 1`,
`H Bᵀ = 0`), `e : n ≃ p ⊕ q`.  For an integer vector `y` and `t = B y` (the node coordinates
`t_i = b_i · y` of the Rust generator),

  `det Gram(rows of H, y) = tᵀ adj(B Bᵀ) t`.

Reading: `|π_K y|² = tᵀ adj(a) t / G` with `a = B Bᵀ`, `G = det a = det Gram L`, and the Gram determinant of the
child lattice `L + ℤ y` is `G_j · μ²`.  This is the exact integer identity the generator evaluates
(`q = Σ t_i adj_ij t_j`, accept iff `q · bound.d < bound.n · g`).

Also the Cauchy-Schwarz form used by the box lemma: `t_i² · G ≤ a_ii · (tᵀ adj(a) t)` (core estimate).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.Compl

namespace LRSpectrumFull
namespace L5S4

open Matrix

variable {p q n : Type} [Fintype p] [Fintype q] [Fintype n]
  [DecidableEq p] [DecidableEq q] [DecidableEq n]

theorem dot_BtB (B : Matrix q n ℚ) (x : q → ℚ) :
    (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ x) = x ⬝ᵥ ((B * Bᵀ) *ᵥ x) := by
  have e1 : x ⬝ᵥ ((B * Bᵀ) *ᵥ x) = (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose]
  exact e1.symm

/-- The projection data of a vector `y` onto `K`: `c = g⁻¹ adj(a) t`, `yK = Bᵀ c`. -/
theorem projection_data (e : n ≃ p ⊕ q) (H : Matrix p n ℚ) (B : Matrix q n ℚ)
    (S : Matrix n p ℚ) (Rr : Matrix n q ℚ)
    (hS : H * S = 1) (hR : B * Rr = 1) (hHB : H * Bᵀ = 0) (y : n → ℚ) :
    ∃ (c : q → ℚ) (w : p → ℚ),
      (B * Bᵀ) *ᵥ c = B *ᵥ y ∧ y = Bᵀ *ᵥ c + Hᵀ *ᵥ w ∧
      c ⬝ᵥ (B *ᵥ y) = ((B * Bᵀ).det)⁻¹ * ((B *ᵥ y) ⬝ᵥ (adjugate (B * Bᵀ) *ᵥ (B *ᵥ y))) := by
  have hg0 : (B * Bᵀ).det ≠ 0 := det_gram_ne_zero B Rr hR
  set a : Matrix q q ℚ := B * Bᵀ with ha
  set t : q → ℚ := B *ᵥ y with ht
  refine ⟨(a.det)⁻¹ • (adjugate a *ᵥ t), (Sᵀ - Sᵀ * Rr * B) *ᵥ (y - Bᵀ *ᵥ ((a.det)⁻¹ • (adjugate a *ᵥ t))), ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hg0, one_smul]
  · set c : q → ℚ := (a.det)⁻¹ • (adjugate a *ᵥ t) with hc
    have hac : a *ᵥ c = t := by
      rw [hc, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hg0, one_smul]
    have hBu : B *ᵥ (y - Bᵀ *ᵥ c) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← ha, hac, ← ht]; simp
    have hid := compl_id e H B S Rr hS hR hHB
    set u : n → ℚ := y - Bᵀ *ᵥ c with hu
    have h1 : u = (Hᵀ * (Sᵀ - Sᵀ * Rr * B) + Rr * B) *ᵥ u := by rw [hid]; simp
    have h2 : (Hᵀ * (Sᵀ - Sᵀ * Rr * B) + Rr * B) *ᵥ u = Hᵀ *ᵥ ((Sᵀ - Sᵀ * Rr * B) *ᵥ u) := by
      rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec u Rr B, hBu]; simp
    have h3 : u = Hᵀ *ᵥ ((Sᵀ - Sᵀ * Rr * B) *ᵥ u) := h1.trans h2
    rw [hu] at h3
    rw [← h3]; abel
  · set c : q → ℚ := (a.det)⁻¹ • (adjugate a *ᵥ t) with hc
    rw [hc, smul_dotProduct, dotProduct_comm (adjugate a *ᵥ t) t]
    simp [smul_eq_mul]

/-- The integer norm formula. -/
theorem bordered_gram_Q (e : n ≃ p ⊕ q) (H : Matrix p n ℚ) (B : Matrix q n ℚ)
    (S : Matrix n p ℚ) (Rr : Matrix n q ℚ)
    (hS : H * S = 1) (hR : B * Rr = 1) (hHB : H * Bᵀ = 0)
    (hg : (B * Bᵀ).det = (H * Hᵀ).det) (y : n → ℚ) :
    (fromRows H (Matrix.of fun (_ : Fin 1) c => y c) *
        (fromRows H (Matrix.of fun (_ : Fin 1) c => y c))ᵀ).det
      = (B *ᵥ y) ⬝ᵥ (adjugate (B * Bᵀ) *ᵥ (B *ᵥ y)) := by
  have hg0 : (B * Bᵀ).det ≠ 0 := det_gram_ne_zero B Rr hR
  obtain ⟨c, w, hac, hy, hct⟩ := projection_data e H B S Rr hS hR hHB y
  set yK : n → ℚ := Bᵀ *ᵥ c with hyK
  set YK : Matrix (Fin 1) n ℚ := Matrix.of fun _ c' => yK c' with hYK
  set W : Matrix (Fin 1) p ℚ := Matrix.of fun _ a' => w a' with hW
  set a : Matrix q q ℚ := B * Bᵀ with ha
  set A : Matrix (p ⊕ Fin 1) (p ⊕ Fin 1) ℚ := fromBlocks 1 0 W 1 with hA
  have hrow : fromRows H (Matrix.of fun (_ : Fin 1) c' => y c') = A * fromRows H YK := by
    rw [hA, fromBlocks_mul_fromRows]
    ext (i | i) c'
    · simp
    · have hyc : y c' = yK c' + ∑ a', w a' * H a' c' := by
        have := congrFun hy c'
        rw [Pi.add_apply] at this
        rw [this]; congr 1; simp [Matrix.mulVec, dotProduct, mul_comm]
      simpa [hW, hYK, Matrix.mul_apply, add_comm] using hyc
  have hdetA : A.det = 1 := by rw [hA, det_fromBlocks_zero₁₂]; simp
  have hHy : H *ᵥ yK = 0 := by
    rw [hyK, Matrix.mulVec_mulVec, hHB]; simp
  have hHYt : H * YKᵀ = 0 := by
    ext a' i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hYK, Matrix.of_apply, Matrix.zero_apply]
    have := congrFun hHy a'
    simpa [Matrix.mulVec, dotProduct] using this
  have hYHt : YK * Hᵀ = 0 := by
    have := congrArg Matrix.transpose hHYt
    simpa [Matrix.transpose_mul] using this
  have hgram : (fromRows H YK * (fromRows H YK)ᵀ).det = (H * Hᵀ).det * (yK ⬝ᵥ yK) := by
    rw [transpose_fromRows, fromRows_mul_fromCols, hHYt, hYHt, det_fromBlocks_zero₁₂,
      Matrix.det_fin_one]
    simp [dotProduct, hYK, Matrix.mul_apply]
  have hfac : (A * fromRows H YK) * (A * fromRows H YK)ᵀ
      = A * (fromRows H YK * (fromRows H YK)ᵀ) * Aᵀ := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hyy : yK ⬝ᵥ yK = (a.det)⁻¹ * ((B *ᵥ y) ⬝ᵥ (adjugate a *ᵥ (B *ᵥ y))) := by
    rw [hyK, dot_BtB, hac, hct]
  rw [hrow, hfac, det_mul, det_mul, Matrix.det_transpose, hdetA, hgram, ← hg, hyy]
  field_simp

/-- Core estimate (Cauchy-Schwarz form): every coordinate of `t = B y` satisfies
`t_i² ≤ a_ii · (tᵀ adj(a) t / det a)`. -/
theorem bordered_cs_Q (e : n ≃ p ⊕ q) (H : Matrix p n ℚ) (B : Matrix q n ℚ)
    (S : Matrix n p ℚ) (Rr : Matrix n q ℚ)
    (hS : H * S = 1) (hR : B * Rr = 1) (hHB : H * Bᵀ = 0) (y : n → ℚ) (i : q) :
    ((B *ᵥ y) i) ^ 2 ≤ (B * Bᵀ) i i *
      (((B * Bᵀ).det)⁻¹ * ((B *ᵥ y) ⬝ᵥ (adjugate (B * Bᵀ) *ᵥ (B *ᵥ y)))) := by
  obtain ⟨c, w, hac, hy, hct⟩ := projection_data e H B S Rr hS hR hHB y
  set yK : n → ℚ := Bᵀ *ᵥ c with hyK
  have hBH : B * Hᵀ = 0 := by
    have := congrArg Matrix.transpose hHB
    simpa [Matrix.transpose_mul] using this
  have hBy : B *ᵥ y = B *ᵥ yK := by
    conv_lhs => rw [hy]
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec w B Hᵀ, hBH]; simp
  have hyy : yK ⬝ᵥ yK = ((B * Bᵀ).det)⁻¹ * ((B *ᵥ y) ⬝ᵥ (adjugate (B * Bᵀ) *ᵥ (B *ᵥ y))) := by
    rw [hyK, dot_BtB, hac, hct]
  rw [← hyy, hBy]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => B i k) (fun k => yK k)
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
  simpa [pow_two] using hcs

end L5S4
end LRSpectrumFull
