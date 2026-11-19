/-
# L5S4.Compl : Gram determinant of a saturated lattice and of its orthogonal complement

Generic matrix statements over a
column index type `n` split as `p ⊕ q` (`e : n ≃ p ⊕ q`):

* `H : Matrix p n ℤ` rows of a lattice `L`, `S` an integer right inverse (`H S = 1`: `L` saturated);
* `B : Matrix q n ℤ` rows of a lattice `K`, `Rr` an integer right inverse (`B Rr = 1`), `H Bᵀ = 0`.

Result `det_gram_compl`: `det (B Bᵀ) = det (H Hᵀ)`.  Also `compl_id` (the `5 × 5` splitting identity used for the
norm formula) and `det_gram_ne_zero`.  Proofs by the four block products
`[H;B]·[S|Bᵀ]`, `[H;Rrᵀ]·[S|Bᵀ]`, `[H;B]·[Hᵀ|Rr]`, `[Sᵀ;B]·[Hᵀ|Rr]` (all block triangular) and the
nonnegativity of Gram determinants.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

namespace LRSpectrumFull
namespace L5S4

open Matrix

section Gen

variable {p q n : Type} [Fintype p] [Fintype q] [Fintype n]
  [DecidableEq p] [DecidableEq q] [DecidableEq n]

/-- Gram determinants of integer matrices are nonnegative. -/
theorem det_mul_transpose_nonneg {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    (M : Matrix a b ℤ) : 0 ≤ (M * Mᵀ).det := by
  set Mr : Matrix a b ℝ := M.map (Int.cast : ℤ → ℝ) with hMr
  have h1 : (Int.castRingHom ℝ).mapMatrix (M * Mᵀ) = Mr * Mrᴴ := by
    ext i k
    simp [hMr, Matrix.mul_apply]
  have h2 : (((M * Mᵀ).det : ℤ) : ℝ) = (Mr * Mrᴴ).det := by
    rw [← h1]; exact RingHom.map_det (Int.castRingHom ℝ) (M * Mᵀ)
  have h3 : 0 ≤ (Mr * Mrᴴ).det := (posSemidef_self_mul_conjTranspose Mr).det_nonneg
  have h4 : (0 : ℝ) ≤ (((M * Mᵀ).det : ℤ) : ℝ) := by rw [h2]; exact h3
  exact_mod_cast h4

/-- Square-ification of a row-partitioned matrix. -/
def sqR (e : n ≃ p ⊕ q) (A : Matrix (p ⊕ q) n ℤ) : Matrix (p ⊕ q) (p ⊕ q) ℤ :=
  A.submatrix id e.symm

/-- Square-ification of a column-partitioned matrix. -/
def sqC (e : n ≃ p ⊕ q) (C : Matrix n (p ⊕ q) ℤ) : Matrix (p ⊕ q) (p ⊕ q) ℤ :=
  C.submatrix e.symm id

theorem sqR_mul_sqC (e : n ≃ p ⊕ q) (A : Matrix (p ⊕ q) n ℤ) (C : Matrix n (p ⊕ q) ℤ) :
    sqR e A * sqC e C = A * C := by
  unfold sqR sqC
  have := Matrix.submatrix_mul_equiv A C (id : p ⊕ q → p ⊕ q) e.symm (id : p ⊕ q → p ⊕ q)
  simpa using this

theorem det_sq_mul (e : n ≃ p ⊕ q) (A : Matrix (p ⊕ q) n ℤ) (C : Matrix n (p ⊕ q) ℤ) :
    (sqR e A).det * (sqC e C).det = (A * C).det := by
  rw [← det_mul, sqR_mul_sqC]

/-- The orthogonal complement of a saturated lattice has the same Gram determinant. -/
theorem det_gram_compl (e : n ≃ p ⊕ q) (H : Matrix p n ℤ) (B : Matrix q n ℤ)
    (S : Matrix n p ℤ) (Rr : Matrix n q ℤ)
    (hS : H * S = 1) (hR : B * Rr = 1) (hHB : H * Bᵀ = 0) :
    (B * Bᵀ).det = (H * Hᵀ).det := by
  have hBH : B * Hᵀ = 0 := by
    have := congrArg Matrix.transpose hHB
    simpa [Matrix.transpose_mul] using this
  have hRB : Rrᵀ * Bᵀ = 1 := by
    have := congrArg Matrix.transpose hR
    simpa [Matrix.transpose_mul] using this
  have hSH : Sᵀ * Hᵀ = 1 := by
    have := congrArg Matrix.transpose hS
    simpa [Matrix.transpose_mul] using this
  -- products
  have p1 : (fromRows H B * fromCols S Bᵀ).det = (B * Bᵀ).det := by
    rw [fromRows_mul_fromCols, hS, hHB, det_fromBlocks_zero₁₂]; simp
  have p2 : (fromRows H Rrᵀ * fromCols S Bᵀ).det = 1 := by
    rw [fromRows_mul_fromCols, hS, hHB, hRB, det_fromBlocks_zero₁₂]; simp
  have p3 : (fromRows H B * fromCols Hᵀ Rr).det = (H * Hᵀ).det := by
    rw [fromRows_mul_fromCols, hBH, hR, det_fromBlocks_zero₂₁]; simp
  have p4 : (fromRows Sᵀ B * fromCols Hᵀ Rr).det = 1 := by
    rw [fromRows_mul_fromCols, hSH, hBH, hR, det_fromBlocks_zero₂₁]; simp
  rw [← det_sq_mul e] at p1 p3
  have p2' : (sqR e (fromRows H Rrᵀ)).det * (sqC e (fromCols S Bᵀ)).det = 1 := by
    rw [det_sq_mul]; exact p2
  have p4' : (sqR e (fromRows Sᵀ B)).det * (sqC e (fromCols Hᵀ Rr)).det = 1 := by
    rw [det_sq_mul]; exact p4
  have u1 : (sqC e (fromCols S Bᵀ)).det = 1 ∨ (sqC e (fromCols S Bᵀ)).det = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' p2' with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have u2 : (sqC e (fromCols Hᵀ Rr)).det = 1 ∨ (sqC e (fromCols Hᵀ Rr)).det = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' p4' with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have n1 := det_mul_transpose_nonneg B
  have n2 := det_mul_transpose_nonneg H
  have hsq : ((B * Bᵀ).det) ^ 2 = ((H * Hᵀ).det) ^ 2 := by
    rw [← p1, ← p3]
    rcases u1 with h | h <;> rcases u2 with h' | h' <;> rw [h, h'] <;> ring
  exact (sq_eq_sq₀ n1 n2).1 hsq

/-- Gram determinants of rows with an integer right inverse are nonzero (over `ℚ`). -/
theorem det_gram_ne_zero (B : Matrix q n ℚ) (Rr : Matrix n q ℚ) (hR : B * Rr = 1) :
    (B * Bᵀ).det ≠ 0 := by
  intro h0
  obtain ⟨x, hx, hxz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hq : (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ x) = 0 := by
    have e1 : x ⬝ᵥ ((B * Bᵀ) *ᵥ x) = (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ x) := by
      rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [← e1, hxz]; simp
  have hz : Bᵀ *ᵥ x = 0 := dotProduct_self_eq_zero.mp hq
  have hRB : Rrᵀ * Bᵀ = 1 := by
    have := congrArg Matrix.transpose hR
    simpa [Matrix.transpose_mul] using this
  apply hx
  have : x = (Rrᵀ * Bᵀ) *ᵥ x := by rw [hRB]; simp
  rw [this, ← Matrix.mulVec_mulVec, hz]; simp

end Gen

section Id

variable {p q n : Type} [Fintype p] [Fintype q] [Fintype n]
  [DecidableEq p] [DecidableEq q] [DecidableEq n]

/-- The splitting identity `Hᵀ (Sᵀ - Sᵀ Rr B) + Rr B = 1` (columns `n`, `n ≃ p ⊕ q`). -/
theorem compl_id {R : Type} [CommRing R] (e : n ≃ p ⊕ q) (H : Matrix p n R) (B : Matrix q n R)
    (S : Matrix n p R) (Rr : Matrix n q R)
    (hS : H * S = 1) (hR : B * Rr = 1) (hHB : H * Bᵀ = 0) :
    Hᵀ * (Sᵀ - Sᵀ * Rr * B) + Rr * B = 1 := by
  have hBH : B * Hᵀ = 0 := by
    have := congrArg Matrix.transpose hHB
    simpa [Matrix.transpose_mul] using this
  have hSH : Sᵀ * Hᵀ = 1 := by
    have := congrArg Matrix.transpose hS
    simpa [Matrix.transpose_mul] using this
  have h1 : fromRows (Sᵀ - Sᵀ * Rr * B) B * fromCols Hᵀ Rr = 1 := by
    rw [fromRows_mul_fromCols]
    have a1 : (Sᵀ - Sᵀ * Rr * B) * Hᵀ = 1 := by
      rw [Matrix.sub_mul, hSH, Matrix.mul_assoc, Matrix.mul_assoc, hBH]; simp
    have a2 : (Sᵀ - Sᵀ * Rr * B) * Rr = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc (Sᵀ * Rr) B Rr, hR]; simp
    rw [a1, a2, hBH, hR]
    exact fromBlocks_one
  have h2 := (fromCols_mul_fromRows_eq_one_comm e Hᵀ Rr (Sᵀ - Sᵀ * Rr * B) B).2 h1
  rwa [fromCols_mul_fromRows] at h2

end Id

end L5S4
end LRSpectrumFull
