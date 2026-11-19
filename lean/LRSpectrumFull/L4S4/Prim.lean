/-
# L4S4.Prim : `gcd t = 1` and the saturation (`ls`) of the extended lattice

In the generator's `child` the new node is built from a node `(l, b, r)` and a coordinate vector `t`
(`t_i = b_i · y`, `y = lift(nd, t)`), after the filter `gg = gcd(t_i) = 1` of `children`.  The `NodeId.ls` field
(a right inverse `s` of the chain rows, i.e. `L_j` saturated in `ℤ⁴`) is the hypothesis of `gF_compl` and is
NOT carried by the generator.  This module proves that it is a consequence of `gcd t = 1`, and conversely:

* `bezout_of_gcd`, `gcdOne_of_bezout`       `Finset.univ.gcd t = 1 ↔ ∃ u, ∑ t_i u_i = 1`.
* `NodeId.swap`, `lat_of_orth_dual`        the dual lattice statement: an integer `u ⊥ l_k` is an integer combination of the `b_i`.
* `ext_ls`   (forward)  `NodeId l b s r`, `gcd (tvec b y) = 1`  ==>  `snoc l y` has an integer right inverse.
* `prim_of_ext_ls` (converse)  a right inverse of `snoc l y` ==> `gcd (tvec b y) = 1`.
* `ext_ls_iff`, `child_nodeId`              the equivalence, and the assembly of `NodeId` for the child from checked `b', r'`.
* `tvec_lift0`, `tvec_lift`                `b_i · (∑ t_k r_k + ∑ c_k l_k) = t_i` (the correctness of the generator's `lift`).
* `gcd_of_primChild`                       link to `PrimChild` of a flag: its `t` is primitive.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S4.Link
import LRSpectrumFull.L4S3.Accepted
import Mathlib.RingTheory.PrincipalIdealDomain

namespace LRSpectrumFull
namespace L4S4

open Matrix Finset LRSpectrumFull.L4S3

/-! ## dot-product bookkeeping -/

theorem dot_comb_right {k : ℕ} (x : V4) (u : Fin k → ℤ) (f : Fin k → V4) :
    dot x (fun a => ∑ i, u i * f i a) = ∑ i, u i * dot x (f i) := by
  unfold dot
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ => by ring))

theorem dot_sub_smul (x p q : V4) (c : ℤ) :
    dot x (fun a => p a - c * q a) = dot x p - c * dot x q := by
  unfold dot
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun a _ => by ring)

/-! ## gcd and Bezout -/

/-- The generator's primitivity test: `gcd` of the entries of `t` is `1`. -/
def GcdOne {d : ℕ} (t : Fin d → ℤ) : Prop := Finset.univ.gcd t = 1

theorem bezout_of_gcd {d : ℕ} (t : Fin d → ℤ) (h : GcdOne t) : ∃ u : Fin d → ℤ, ∑ i, t i * u i = 1 := by
  obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset (Fin d)) t
  exact ⟨g, by rw [← hg]; exact h⟩

theorem gcdOne_of_bezout {d : ℕ} (t u : Fin d → ℤ) (h : ∑ i, t i * u i = 1) : GcdOne t := by
  unfold GcdOne
  have hd : ∀ i, Finset.univ.gcd t ∣ t i := fun i => Finset.gcd_dvd (Finset.mem_univ i)
  have h1 : Finset.univ.gcd t ∣ 1 := by
    rw [← h]
    exact Finset.dvd_sum (fun i _ => Dvd.dvd.mul_right (hd i) _)
  have h2 : (Finset.univ.gcd t : ℤ) = 1 ∨ (Finset.univ.gcd t : ℤ) = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one h1)
  rcases h2 with h2 | h2
  · exact h2
  · exfalso
    have : (0 : ℤ) ≤ Finset.univ.gcd t := Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
    omega

/-! ## the dual lattice statement -/

theorem NodeId.swap {j d : ℕ} {l : Fin j → V4} {b : Fin d → V4} {s : Fin j → V4} {r : Fin d → V4}
    (hN : NodeId l b s r) : NodeId b l r s where
  bl i k := by rw [dot_comm']; exact hN.bl k i
  ls := hN.br
  br := hN.ls

/-- An integer vector orthogonal to all `l_k` is an integer combination of the `b_i`, with coefficients `r_i · u`. -/
theorem lat_of_orth_dual {j d : ℕ} (hjd : j + d = 4) {l : Fin j → V4} {b : Fin d → V4}
    {s : Fin j → V4} {r : Fin d → V4} (hN : NodeId l b s r) (u : V4)
    (hu : ∀ k, dot (l k) u = 0) :
    ∀ a : Fin 4, u a = ∑ i : Fin d, (dot (r i) u) * b i a :=
  lat_of_orth (by omega) hN.swap u hu

/-! ## Saturation and `gcd t = 1` -/

/-- Forward: if `gcd (b_i · y) = 1` then `l_0, …, l_{j-1}, y` has an integer right inverse
(the extended lattice is saturated: the `ls` field of `NodeId` for the child). -/
theorem ext_ls {j d : ℕ} {l : Fin j → V4} {b : Fin d → V4} {s : Fin j → V4} {r : Fin d → V4}
    (hN : NodeId l b s r) (y : V4) (hg : GcdOne (tvec b y)) :
    ∃ s' : Fin (j + 1) → V4, ∀ i k,
      dot (Fin.snoc (α := fun _ => V4) l y i) (s' k) = if i = k then 1 else 0 := by
  obtain ⟨u, hu⟩ := bezout_of_gcd _ hg
  set w : V4 := fun a => ∑ i, u i * b i a with hw
  have hlw : ∀ k, dot (l k) w = 0 := by
    intro k
    rw [hw, dot_comb_right]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [dot_comm' (l k) (b i), hN.bl i k, mul_zero]
  have hyw : dot y w = 1 := by
    rw [hw, dot_comb_right, ← hu]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dot_comm' y (b i)]; unfold tvec; ring
  refine ⟨Fin.snoc (α := fun _ => V4) (fun k a => s k a - dot y (s k) * w a) w, fun i k => ?_⟩
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [hyw]
    · simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [dot_sub_smul, hyw, if_neg (Fin.castSucc_lt_last k).ne']
      ring
  · refine Fin.lastCases ?_ (fun k => ?_) k
    · simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [hlw]
      simp [Fin.castSucc_ne_last]
    · simp only [Fin.snoc_castSucc]
      rw [dot_sub_smul, hlw, hN.ls]
      simp [Fin.castSucc_inj]

/-- Converse: a right inverse of `snoc l y` forces `gcd (b_i · y) = 1`. -/
theorem prim_of_ext_ls {j d : ℕ} (hjd : j + d = 4) {l : Fin j → V4} {b : Fin d → V4} {s : Fin j → V4}
    {r : Fin d → V4} (hN : NodeId l b s r) (y : V4) (s' : Fin (j + 1) → V4)
    (hs' : ∀ i k, dot (Fin.snoc (α := fun _ => V4) l y i) (s' k) = if i = k then 1 else 0) :
    GcdOne (tvec b y) := by
  set u : V4 := s' (Fin.last j) with hu
  have horth : ∀ k, dot (l k) u = 0 := by
    intro k
    have := hs' (Fin.castSucc k) (Fin.last j)
    simpa [Fin.snoc_castSucc, Fin.castSucc_ne_last] using this
  have hy : dot y u = 1 := by
    have := hs' (Fin.last j) (Fin.last j)
    simpa using this
  have hexp := lat_of_orth_dual hjd hN u horth
  have h1 : dot y u = ∑ i, (dot (r i) u) * dot y (b i) := by
    have : u = fun a => ∑ i, (dot (r i) u) * b i a := funext hexp
    conv_lhs => rw [this]
    exact dot_comb_right y _ b
  refine gcdOne_of_bezout (tvec b y) (fun i => dot (r i) u) ?_
  rw [← hy, h1]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dot_comm' y (b i)]; unfold tvec; ring

theorem ext_ls_iff {j d : ℕ} (hjd : j + d = 4) {l : Fin j → V4} {b : Fin d → V4} {s : Fin j → V4}
    {r : Fin d → V4} (hN : NodeId l b s r) (y : V4) :
    GcdOne (tvec b y) ↔ ∃ s' : Fin (j + 1) → V4, ∀ i k,
      dot (Fin.snoc (α := fun _ => V4) l y i) (s' k) = if i = k then 1 else 0 :=
  ⟨ext_ls hN y, fun ⟨s', h⟩ => prim_of_ext_ls hjd hN y s' h⟩

/-- Assembly of `NodeId` for the child: the identities `b'·l' = 0`, `b'·r' = I` are checked by the kernel
for the generator's `b', r'`; the saturation field comes from `gcd t = 1`. -/
theorem child_nodeId {j d d' : ℕ} {l : Fin j → V4} {b : Fin d → V4} {s : Fin j → V4} {r : Fin d → V4}
    (hN : NodeId l b s r) (y : V4) (hg : GcdOne (tvec b y)) (b' r' : Fin d' → V4)
    (hbl : ∀ i k, dot (b' i) (Fin.snoc (α := fun _ => V4) l y k) = 0)
    (hbr : ∀ i k, dot (b' i) (r' k) = if i = k then 1 else 0) :
    ∃ s' : Fin (j + 1) → V4, NodeId (Fin.snoc (α := fun _ => V4) l y) b' s' r' := by
  obtain ⟨s', hs'⟩ := ext_ls hN y hg
  exact ⟨s', ⟨hbl, hs', hbr⟩⟩

/-- The generator's `lift` returns `y = ∑ t_k r_k` reduced by integer multiples of the `l_i`; its node coordinates are `t`. -/
theorem tvec_lift0 {j d : ℕ} {l : Fin j → V4} {b : Fin d → V4} {s : Fin j → V4} {r : Fin d → V4}
    (hN : NodeId l b s r) (t : Fin d → ℤ) : tvec b (fun a => ∑ k, t k * r k a) = t := by
  funext i
  unfold tvec
  rw [dot_comb_right]
  simp [hN.br]

theorem tvec_lift {j d : ℕ} {l : Fin j → V4} {b : Fin d → V4} {s : Fin j → V4} {r : Fin d → V4}
    (hN : NodeId l b s r) (t : Fin d → ℤ) (c : Fin j → ℤ) :
    tvec b (fun a => (∑ k, t k * r k a) + ∑ k, c k * l k a) = t := by
  rw [tvec_of_lat hN (fun a => ∑ k, t k * r k a) c, tvec_lift0 hN]

/-- `PrimChild` of a flag (saturation of `L_{j+1}`) makes the node coordinates of `h_j` primitive. -/
theorem gcd_of_primChild {v : V4} (F : FlagData v) {j d : ℕ} (hjd : j + d = 4) (hj : j < 3)
    {b : Fin d → V4} {s : Fin j → V4} {r : Fin d → V4}
    (hnode : NodeId (fun i : Fin j => hN F.h i.val) b s r) (hp : PrimChild F) :
    GcdOne (tvec b (F.h ⟨j, hj⟩)) := by
  obtain ⟨ρ, hρ⟩ := hp (j + 1) (by omega)
  refine prim_of_ext_ls hjd hnode (F.h ⟨j, hj⟩) (fun c k => ρ k c.val) (fun i k => ?_)
  rw [snoc_eq_hN F j hj]
  have := hρ i.val i.2 k.val k.2
  unfold dot
  rw [this]
  simp [Fin.ext_iff]

end L4S4
end LRSpectrumFull
