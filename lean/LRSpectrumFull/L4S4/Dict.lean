/-
# L4S4.Dict : the node dictionary at the level of `V4 = Fin 4 → ℤ`

A *node* of the pruned tree at depth `j` (`d = 5 - j`) carries the integer data of
the generator's `Node`:  rows `l : Fin j → V4` (chain `h_1..h_j`), rows `b : Fin d → V4` (basis of `K_j = L_j^⊥ ∩ ℤ⁴`),
right inverse `r : Fin d → V4` (`b_i · r_k = δ`) and, for the saturation of `L_j`, a right inverse `s : Fin j → V4`
(`l_i · s_k = δ`, which in the flag of a real `v` is the first `j` columns of `FlagData.R`).
`NodeId` collects the three families of integer identities a kernel checker verifies.

* `gF_compl`   : `Gram det K = Gram det L`, i.e. `gs[j]` of the generator is the true minor `G_j`.
* `gF_snoc`    : `Gram det (l_0..l_{j-1}, y) = tᵀ adj(a) t` with `t_i = b_i · y`, `a = Gram(b)`.
* `box_covers` : ball `q·bd < bn·g` implies `|t_i| ≤ isqrtI (bn a_ii / bd)` (the `tmax` of `children`).
* `lat_of_orth`/`lat_of_same_coords` (lattice form) : an integer vector orthogonal to all `b_i` is an INTEGER
  combination of the rows `l_k` (coefficients `s_k · u`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.IntForm
import LRSpectrumFull.L4S3.GramQ

namespace LRSpectrumFull
namespace L4S4

open Matrix LRSpectrumFull.L4S3 LRSpectrumFull.L5S4

/-- Column index split `Fin 4 ≃ Fin j ⊕ Fin d`. -/
def eqv {j d : ℕ} (h : j + d = 4) : Fin 4 ≃ Fin j ⊕ Fin d :=
  (finCongr h.symm).trans finSumFinEquiv.symm

/-- The three families of integer identities of a node (`b ⊥ l`, `l` saturated, `b` has a right inverse). -/
structure NodeId {j d : ℕ} (l : Fin j → V4) (b : Fin d → V4) (s : Fin j → V4) (r : Fin d → V4) :
    Prop where
  bl : ∀ i k, dot (b i) (l k) = 0
  ls : ∀ i k, dot (l i) (s k) = if i = k then 1 else 0
  br : ∀ i k, dot (b i) (r k) = if i = k then 1 else 0

/-- Rows as a matrix. -/
def mR {a : ℕ} (f : Fin a → V4) : Matrix (Fin a) (Fin 4) ℤ := Matrix.of fun i c => f i c

/-- Columns as a matrix. -/
def mC {a : ℕ} (f : Fin a → V4) : Matrix (Fin 4) (Fin a) ℤ := Matrix.of fun c i => f i c

theorem mR_mul_mC {a b : ℕ} (f : Fin a → V4) (g : Fin b → V4) :
    mR f * mC g = Matrix.of fun i k => dot (f i) (g k) := by
  ext i k; simp [mR, mC, Matrix.mul_apply, dot]

theorem mR_mul_mR_T {a b : ℕ} (f : Fin a → V4) (g : Fin b → V4) :
    mR f * (mR g)ᵀ = Matrix.of fun i k => dot (f i) (g k) := by
  ext i k; simp [mR, Matrix.mul_apply, dot]

theorem dot_comm' (x y : V4) : dot x y = dot y x := by
  unfold dot; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

section Node

variable {j d : ℕ} {l b s r : _}

theorem NodeId.hS (hN : NodeId (j := j) (d := d) l b s r) : mR l * mC s = 1 := by
  rw [mR_mul_mC]; ext i k; simp [hN.ls, Matrix.one_apply]

theorem NodeId.hR (hN : NodeId (j := j) (d := d) l b s r) : mR b * mC r = 1 := by
  rw [mR_mul_mC]; ext i k; simp [hN.br, Matrix.one_apply]

theorem NodeId.hHB (hN : NodeId (j := j) (d := d) l b s r) : mR l * (mR b)ᵀ = 0 := by
  rw [mR_mul_mR_T]; ext i k; simp [dot_comm' (l i) (b k), hN.bl]

end Node

/-- The Gram determinant of the basis of `K_j = L_j^⊥ ∩ ℤ⁴` equals the Gram determinant of `L_j`. -/
theorem gF_compl {j d : ℕ} (hjd : j + d = 4) {l : Fin j → V4} {b : Fin d → V4}
    {s : Fin j → V4} {r : Fin d → V4} (hN : NodeId l b s r) : gF b = gF l := by
  have h := det_gram_compl (eqv hjd) (mR l) (mR b) (mC s) (mC r) hN.hS hN.hR hN.hHB
  have e1 : (mR b * (mR b)ᵀ) = Matrix.of fun i k => dot (b i) (b k) := mR_mul_mR_T b b
  have e2 : (mR l * (mR l)ᵀ) = Matrix.of fun i k => dot (l i) (l k) := mR_mul_mR_T l l
  rw [e1, e2] at h
  exact h

/-- Gram matrix of the `K` basis (the matrix `a` of the generator's `Node`). -/
def gramK {d : ℕ} (b : Fin d → V4) : Matrix (Fin d) (Fin d) ℤ :=
  Matrix.of fun i k => dot (b i) (b k)

/-- Node coordinates `t_i = b_i · y`. -/
def tvec {d : ℕ} (b : Fin d → V4) (y : V4) : Fin d → ℤ := fun i => dot (b i) y

/-- The quadratic form `q = tᵀ adj(a) t` evaluated by the generator. -/
def qform {d : ℕ} (b : Fin d → V4) (y : V4) : ℤ :=
  tvec b y ⬝ᵥ (adjugate (gramK b) *ᵥ tvec b y)

/-- `det Gram(l_0..l_{j-1}, y) = tᵀ adj(a) t`. -/
theorem gF_snoc {j d : ℕ} (hjd : j + d = 4) {l : Fin j → V4} {b : Fin d → V4}
    {s : Fin j → V4} {r : Fin d → V4} (hN : NodeId l b s r) (y : V4) :
    gF (Fin.snoc (α := fun _ => V4) l y : Fin (j + 1) → V4) = qform b y := by
  have h := bordered_gram_Z (eqv hjd) (mR l) (mR b) (mC s) (mC r) hN.hS hN.hR hN.hHB y
  have e1 : (mR b * (mR b)ᵀ) = gramK b := mR_mul_mR_T b b
  have hty : mR b *ᵥ y = tvec b y := by
    funext i; simp [mR, tvec, Matrix.mulVec, dotProduct, dot]
  rw [e1, hty] at h
  have hb : borderGram (mR l) y = (Matrix.of fun a c : Fin (j + 1) =>
      dot (Fin.snoc (α := fun _ => V4) l y a) (Fin.snoc (α := fun _ => V4) l y c)).submatrix
        finSumFinEquiv finSumFinEquiv := by
    ext (a | a) (c | c)
    · simp [borderGram, mR, Matrix.mul_apply, dot, Fin.snoc]
    · simp [borderGram, mR, Matrix.mul_apply, dot, Fin.snoc]
    · simp [borderGram, mR, Matrix.mul_apply, dot, Fin.snoc]
    · simp [borderGram, mR, Matrix.mul_apply, dot, Fin.snoc]
  rw [hb, Matrix.det_submatrix_equiv_self] at h
  exact h

/-- Core estimate: `t_i² · det a ≤ a_ii · q`. -/
theorem cs_inequality {j d : ℕ} (hjd : j + d = 4) {l : Fin j → V4} {b : Fin d → V4}
    {s : Fin j → V4} {r : Fin d → V4} (hN : NodeId l b s r) (y : V4) (i : Fin d) :
    (tvec b y i) ^ 2 * (gramK b).det ≤ (gramK b i i) * qform b y := by
  have h := bordered_cs_Z (eqv hjd) (mR l) (mR b) (mC s) (mC r) hN.hS hN.hR hN.hHB y i
  have e1 : (mR b * (mR b)ᵀ) = gramK b := mR_mul_mR_T b b
  have hty : mR b *ᵥ y = tvec b y := by
    funext i; simp [mR, tvec, Matrix.mulVec, dotProduct, dot]
  rw [e1, hty] at h
  exact h

/-- Lattice form: an integer vector orthogonal to all `b_i` is an integer combination of the rows `l_k`. -/
theorem lat_of_orth {j d : ℕ} (hjd : j + d = 4) {l : Fin j → V4} {b : Fin d → V4}
    {s : Fin j → V4} {r : Fin d → V4} (hN : NodeId l b s r) (u : V4)
    (hu : ∀ i, dot (b i) u = 0) :
    ∀ a : Fin 4, u a = ∑ k : Fin j, (dot (s k) u) * l k a := by
  have hid := compl_id (eqv hjd) (mR l) (mR b) (mC s) (mC r) hN.hS hN.hR hN.hHB
  have hBu : mR b *ᵥ u = 0 := by
    funext i; simpa [mR, Matrix.mulVec, dotProduct, dot] using hu i
  have h1 : u = (((mR l)ᵀ * ((mC s)ᵀ - (mC s)ᵀ * mC r * mR b) + mC r * mR b) *ᵥ u) := by
    rw [hid]; simp
  have h2 : (((mR l)ᵀ * ((mC s)ᵀ - (mC s)ᵀ * mC r * mR b) + mC r * mR b) *ᵥ u)
      = (mR l)ᵀ *ᵥ (((mC s)ᵀ - (mC s)ᵀ * mC r * mR b) *ᵥ u) := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec u (mC r) (mR b), hBu, ← Matrix.mulVec_mulVec]
    simp
  have h3 : (((mC s)ᵀ - (mC s)ᵀ * mC r * mR b) *ᵥ u) = (mC s)ᵀ *ᵥ u := by
    rw [Matrix.sub_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec u ((mC s)ᵀ) (mC r * mR b),
      ← Matrix.mulVec_mulVec u (mC r) (mR b), hBu]; simp
  intro a
  have := congrFun (h1.trans h2) a
  rw [h3] at this
  rw [this]
  simp [Matrix.mulVec, dotProduct, mR, mC, dot, mul_comm]

/-- Two integer vectors with the same node coordinates differ by an integer combination of `l`. -/
theorem lat_of_same_coords {j d : ℕ} (hjd : j + d = 4) {l : Fin j → V4} {b : Fin d → V4}
    {s : Fin j → V4} {r : Fin d → V4} (hN : NodeId l b s r) (y y' : V4)
    (h : ∀ i, dot (b i) y = dot (b i) y') :
    ∀ a : Fin 4, y' a = y a + ∑ k : Fin j, (dot (s k) (fun c => y' c - y c)) * l k a := by
  intro a
  have hu : ∀ i, dot (b i) (fun c => y' c - y c) = 0 := by
    intro i
    have : dot (b i) (fun c => y' c - y c) = dot (b i) y' - dot (b i) y := by
      unfold dot; simp [mul_sub, Finset.sum_sub_distrib]
    rw [this, h i]; ring
  have := lat_of_orth hjd hN _ hu a
  linarith

/-! ## The box -/

/-- Integer square root as in the generator's `isqrt` (`0` for `n ≤ 0`). -/
def isqrtI (n : ℤ) : ℤ := (Nat.sqrt n.toNat : ℤ)

theorem le_isqrtI {t n : ℤ} (h : t ^ 2 ≤ n) : |t| ≤ isqrtI n := by
  have hn : 0 ≤ n := le_trans (sq_nonneg t) h
  unfold isqrtI
  have h1 : t.natAbs * t.natAbs ≤ n.toNat := by
    have e : ((t.natAbs * t.natAbs : ℕ) : ℤ) = t ^ 2 := by
      rw [Nat.cast_mul, Int.natAbs_mul_self' t, pow_two]
    have : ((t.natAbs * t.natAbs : ℕ) : ℤ) ≤ ((n.toNat : ℕ) : ℤ) := by
      rw [e, Int.toNat_of_nonneg hn]; exact h
    exact_mod_cast this
  have h2 := (Nat.le_sqrt.2 h1)
  have : |t| = (t.natAbs : ℤ) := (Int.abs_eq_natAbs t)
  rw [this]; exact_mod_cast h2

/-- The ball `q · bd < bn · g` (`bd > 0`) lies in the box `|t_i| ≤ isqrt(⌊bn a_ii / bd⌋)`.
Hypotheses: `g = det a > 0`, `a_ii > 0`, and the Cauchy-Schwarz inequality `cs_inequality`. -/
theorem ball_sq_aux (g aii q t bn bd : ℤ) (hg : 0 < g) (hbd : 0 < bd) (ha : 0 < aii)
    (hcs : t ^ 2 * g ≤ aii * q) (hq : q * bd < bn * g) : t ^ 2 * bd < aii * bn := by
  have h1 : t ^ 2 * g * bd ≤ aii * q * bd := mul_le_mul_of_nonneg_right hcs hbd.le
  have h2 : aii * q * bd < aii * (bn * g) := by
    have := mul_lt_mul_of_pos_left hq ha
    nlinarith
  have h3 : (t ^ 2 * bd) * g < (aii * bn) * g := by nlinarith
  exact lt_of_mul_lt_mul_right h3 hg.le

theorem box_covers_aux (g aii q t bn bd : ℤ) (hg : 0 < g) (hbd : 0 < bd) (ha : 0 < aii)
    (hcs : t ^ 2 * g ≤ aii * q) (hq : q * bd < bn * g) : |t| ≤ isqrtI (bn * aii / bd) := by
  have h4 := ball_sq_aux g aii q t bn bd hg hbd ha hcs hq
  have h5 : t ^ 2 ≤ bn * aii / bd := by
    apply (Int.le_ediv_iff_mul_le hbd).2
    nlinarith
  exact le_isqrtI h5

theorem box_covers {j d : ℕ} (hjd : j + d = 4) {l : Fin j → V4} {b : Fin d → V4}
    {s : Fin j → V4} {r : Fin d → V4} (hN : NodeId l b s r) (y : V4) (i : Fin d)
    (bn bd : ℤ) (hbd : 0 < bd) (hq : qform b y * bd < bn * (gramK b).det) :
    |tvec b y i| ≤ isqrtI (bn * gramK b i i / bd) := by
  have hg : 0 < (gramK b).det := by
    have := det_gram_pos_Z (mR b) (mC r) hN.hR
    rwa [mR_mul_mR_T] at this
  have ha : 0 < gramK b i i := by
    have h2 : dot (b i) (r i) = 1 := by simpa using hN.br i i
    have h3 : 0 ≤ dot (b i) (b i) := Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
    rcases h3.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : ∀ k ∈ Finset.univ, b i k * b i k = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => mul_self_nonneg _)).1 h.symm
      have hz : ∀ k, b i k = 0 := fun k => mul_self_eq_zero.1 (h0 k (Finset.mem_univ k))
      have : dot (b i) (r i) = 0 := by simp [dot, hz]
      rw [h2] at this; exact one_ne_zero this
  exact box_covers_aux _ _ _ _ _ _ hg hbd ha (cs_inequality hjd hN y i) hq

end L4S4
end LRSpectrumFull
