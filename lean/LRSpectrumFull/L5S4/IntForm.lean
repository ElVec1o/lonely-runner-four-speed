/-
# L5S4.IntForm : the integer forms of the Gram-determinant formulas (generic index types, `ℤ` matrices)

Casts the `ℚ` statements of `Bordered` to `ℤ` matrices:

* `det_gram_compl_Z`  = `Compl.det_gram_compl` (already over `ℤ`);
* `bordered_gram_Z`   : `det Gram(rows of H, y) = tᵀ adj(B Bᵀ) t` with `t = B y`, all over `ℤ`;
* `bordered_cs_Z`     : `t_i² · det(B Bᵀ) ≤ (B Bᵀ)_ii · (tᵀ adj(B Bᵀ) t)`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.Bordered

namespace LRSpectrumFull
namespace L5S4

open Matrix

variable {p q n : Type} [Fintype p] [Fintype q] [Fintype n]
  [DecidableEq p] [DecidableEq q] [DecidableEq n]

/-- Cast of an integer matrix to `ℚ`. -/
def cq {a b : Type} (M : Matrix a b ℤ) : Matrix a b ℚ := M.map (Int.castRingHom ℚ)

theorem cq_mul {a b c : Type} [Fintype b] (M : Matrix a b ℤ) (N : Matrix b c ℤ) :
    cq (M * N) = cq M * cq N := by
  unfold cq; exact Matrix.map_mul

theorem cq_transpose {a b : Type} (M : Matrix a b ℤ) : cq Mᵀ = (cq M)ᵀ := by
  simp [cq, Matrix.transpose_map]

theorem cq_one {a : Type} [DecidableEq a] : cq (1 : Matrix a a ℤ) = 1 := by
  simp [cq, Matrix.map_one]

theorem cq_zero {a b : Type} : cq (0 : Matrix a b ℤ) = 0 := by
  simp [cq]

theorem cq_det {a : Type} [Fintype a] [DecidableEq a] (M : Matrix a a ℤ) :
    ((M.det : ℤ) : ℚ) = (cq M).det := by
  have := RingHom.map_det (Int.castRingHom ℚ) M
  simpa [cq, RingHom.mapMatrix_apply] using this

theorem cq_fromRows {a b c : Type} (A : Matrix a c ℤ) (B : Matrix b c ℤ) :
    cq (fromRows A B) = fromRows (cq A) (cq B) := by
  ext (i | i) k <;> simp [cq]

theorem cq_adjugate {a : Type} [Fintype a] [DecidableEq a] (M : Matrix a a ℤ) :
    cq (adjugate M) = adjugate (cq M) := by
  have := RingHom.map_adjugate (Int.castRingHom ℚ) M
  simpa [cq, RingHom.mapMatrix_apply] using this

theorem cq_mulVec {a b : Type} [Fintype b] (M : Matrix a b ℤ) (v : b → ℤ) (i : a) :
    (((M *ᵥ v) i : ℤ) : ℚ) = (cq M *ᵥ (fun k => (v k : ℚ))) i := by
  simp [cq, Matrix.mulVec, dotProduct]

theorem cq_dot {a : Type} [Fintype a] (u v : a → ℤ) :
    (((u ⬝ᵥ v : ℤ)) : ℚ) = (fun k => (u k : ℚ)) ⬝ᵥ (fun k => (v k : ℚ)) := by
  simp [dotProduct]

/-- Gram determinants of rows with an integer right inverse are positive. -/
theorem det_gram_pos_Z (B : Matrix q n ℤ) (Rr : Matrix n q ℤ) (hR : B * Rr = 1) :
    0 < (B * Bᵀ).det := by
  have hRq : cq B * cq Rr = 1 := by rw [← cq_mul, hR, cq_one]
  have hBB : cq (B * Bᵀ) = cq B * (cq B)ᵀ := by rw [cq_mul, cq_transpose]
  have h1 : (0 : ℤ) ≤ (B * Bᵀ).det := det_mul_transpose_nonneg B
  have h2 : (B * Bᵀ).det ≠ 0 := by
    intro h0
    have := det_gram_ne_zero (cq B) (cq Rr) hRq
    rw [← hBB, ← cq_det, h0] at this
    simp at this
  exact lt_of_le_of_ne h1 (Ne.symm h2)

/-- The Gram matrix of the rows of `H` together with one more row `y`. -/
def borderGram (H : Matrix p n ℤ) (y : n → ℤ) : Matrix (p ⊕ Fin 1) (p ⊕ Fin 1) ℤ :=
  fromRows H (Matrix.of fun (_ : Fin 1) c => y c) *
    (fromRows H (Matrix.of fun (_ : Fin 1) c => y c))ᵀ

/-- The bordered-determinant formula over `ℤ`. -/
theorem bordered_gram_Z (e : n ≃ p ⊕ q) (H : Matrix p n ℤ) (B : Matrix q n ℤ)
    (S : Matrix n p ℤ) (Rr : Matrix n q ℤ)
    (hS : H * S = 1) (hR : B * Rr = 1) (hHB : H * Bᵀ = 0) (y : n → ℤ) :
    (borderGram H y).det = (B *ᵥ y) ⬝ᵥ (adjugate (B * Bᵀ) *ᵥ (B *ᵥ y)) := by
  have hg : (B * Bᵀ).det = (H * Hᵀ).det := det_gram_compl e H B S Rr hS hR hHB
  have hSq : cq H * cq S = 1 := by rw [← cq_mul, hS, cq_one]
  have hRq : cq B * cq Rr = 1 := by rw [← cq_mul, hR, cq_one]
  have hHBq : cq H * (cq B)ᵀ = 0 := by rw [← cq_transpose, ← cq_mul, hHB, cq_zero]
  have hgq : (cq B * (cq B)ᵀ).det = (cq H * (cq H)ᵀ).det := by
    have h1 : cq (B * Bᵀ) = cq B * (cq B)ᵀ := by rw [cq_mul, cq_transpose]
    have h2 : cq (H * Hᵀ) = cq H * (cq H)ᵀ := by rw [cq_mul, cq_transpose]
    rw [← h1, ← h2, ← cq_det, ← cq_det, hg]
  have key := bordered_gram_Q e (cq H) (cq B) (cq S) (cq Rr) hSq hRq hHBq hgq (fun k => (y k : ℚ))
  apply Int.cast_injective (α := ℚ)
  rw [cq_det]
  have hY : cq (Matrix.of fun (_ : Fin 1) c => y c) = Matrix.of fun (_ : Fin 1) c => (y c : ℚ) := by
    ext i k; simp [cq]
  have e1 : cq (borderGram H y) = fromRows (cq H) (Matrix.of fun (_ : Fin 1) c => (y c : ℚ)) *
      (fromRows (cq H) (Matrix.of fun (_ : Fin 1) c => (y c : ℚ)))ᵀ := by
    unfold borderGram
    rw [cq_mul, cq_transpose, cq_fromRows, hY]
  have t1 : (fun k => (((B *ᵥ y) k : ℤ) : ℚ)) = cq B *ᵥ (fun k => (y k : ℚ)) :=
    funext (cq_mulVec B y)
  have t2 : (fun k => (((adjugate (B * Bᵀ) *ᵥ (B *ᵥ y)) k : ℤ) : ℚ))
      = adjugate (cq B * (cq B)ᵀ) *ᵥ (cq B *ᵥ (fun k => (y k : ℚ))) := by
    funext k
    rw [cq_mulVec, t1, cq_adjugate, cq_mul, cq_transpose]
  rw [e1, key, cq_dot, t1, t2]

/-- The core estimate over `ℤ`: `t_i² · det a ≤ a_ii · (tᵀ adj(a) t)` for `a = B Bᵀ`, `t = B y`. -/
theorem bordered_cs_Z (e : n ≃ p ⊕ q) (H : Matrix p n ℤ) (B : Matrix q n ℤ)
    (S : Matrix n p ℤ) (Rr : Matrix n q ℤ)
    (hS : H * S = 1) (hR : B * Rr = 1) (hHB : H * Bᵀ = 0) (y : n → ℤ) (i : q) :
    ((B *ᵥ y) i) ^ 2 * (B * Bᵀ).det ≤
      (B * Bᵀ) i i * ((B *ᵥ y) ⬝ᵥ (adjugate (B * Bᵀ) *ᵥ (B *ᵥ y))) := by
  have hSq : cq H * cq S = 1 := by rw [← cq_mul, hS, cq_one]
  have hRq : cq B * cq Rr = 1 := by rw [← cq_mul, hR, cq_one]
  have hHBq : cq H * (cq B)ᵀ = 0 := by rw [← cq_transpose, ← cq_mul, hHB, cq_zero]
  have key := bordered_cs_Q e (cq H) (cq B) (cq S) (cq Rr) hSq hRq hHBq (fun k => (y k : ℚ)) i
  have hBB : cq (B * Bᵀ) = cq B * (cq B)ᵀ := by rw [cq_mul, cq_transpose]
  have hgpos : (0 : ℚ) < (cq B * (cq B)ᵀ).det := by
    rw [← hBB, ← cq_det]
    have h1 : (0 : ℤ) ≤ (B * Bᵀ).det := det_mul_transpose_nonneg B
    have h2 : (B * Bᵀ).det ≠ 0 := by
      intro h0
      have := det_gram_ne_zero (cq B) (cq Rr) hRq
      rw [← hBB, ← cq_det, h0] at this
      simp at this
    exact_mod_cast lt_of_le_of_ne h1 (Ne.symm h2)
  have t1 : (fun k => (((B *ᵥ y) k : ℤ) : ℚ)) = cq B *ᵥ (fun k => (y k : ℚ)) :=
    funext (cq_mulVec B y)
  have t2 : (fun k => (((adjugate (B * Bᵀ) *ᵥ (B *ᵥ y)) k : ℤ) : ℚ))
      = adjugate (cq B * (cq B)ᵀ) *ᵥ (cq B *ᵥ (fun k => (y k : ℚ))) := by
    funext k
    rw [cq_mulVec, t1, cq_adjugate, cq_mul, cq_transpose]
  have hq : (((B *ᵥ y) ⬝ᵥ (adjugate (B * Bᵀ) *ᵥ (B *ᵥ y)) : ℤ) : ℚ)
      = (cq B *ᵥ (fun k => (y k : ℚ))) ⬝ᵥ (adjugate (cq B * (cq B)ᵀ) *ᵥ (cq B *ᵥ (fun k => (y k : ℚ)))) := by
    rw [cq_dot, t1, t2]
  have hcast : (((B * Bᵀ) i i : ℤ) : ℚ) = (cq B * (cq B)ᵀ) i i := by
    rw [← cq_transpose, ← cq_mul]; simp [cq]
  have hdet : (((B * Bᵀ).det : ℤ) : ℚ) = (cq B * (cq B)ᵀ).det := by
    rw [cq_det, cq_mul, cq_transpose]
  have hti : ((((B *ᵥ y) i : ℤ) : ℚ)) = (cq B *ᵥ (fun k => (y k : ℚ))) i := cq_mulVec B y i
  have hfin : ((((B *ᵥ y) i) ^ 2 * (B * Bᵀ).det : ℤ) : ℚ)
      ≤ ((((B * Bᵀ) i i * ((B *ᵥ y) ⬝ᵥ (adjugate (B * Bᵀ) *ᵥ (B *ᵥ y))) : ℤ)) : ℚ) := by
    rw [Int.cast_mul, Int.cast_pow, Int.cast_mul, hti, hdet, hcast, hq]
    calc _ ≤ ((cq B * (cq B)ᵀ) i i * (((cq B * (cq B)ᵀ).det)⁻¹ *
          ((cq B *ᵥ (fun k => (y k : ℚ))) ⬝ᵥ (adjugate (cq B * (cq B)ᵀ) *ᵥ (cq B *ᵥ (fun k => (y k : ℚ))))))) *
          (cq B * (cq B)ᵀ).det := mul_le_mul_of_nonneg_right key hgpos.le
      _ = _ := by field_simp
  exact_mod_cast hfin

end L5S4
end LRSpectrumFull
