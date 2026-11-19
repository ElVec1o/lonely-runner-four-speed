/-
# L4S4.Records4 : certificate records of the four-speed tree ("cert4 v1") and the critical-torus link

The n = 4 tree has ONE child step (depth 1 -> leaf `L_2`), no depth-2 internal node, no leaf-class map.

* Records (Rust files = little-endian `i32` fields): `T1Rec4` (37 fields), `LeafRec4` (46 fields; the signed
  permutation `(sigma, eps)` is the structure `SP`, its decoding from the integer fields is a checker obligation),
  `T5Rec4` (9 fields), `Certificate4`.
* Depth-1 cover: `exists_sort_abs4`, `T1Ok4` (sorted, entries `≤ 4`, primitive, `2 ≤ |h|² ≤ 16`), `depth1_cover4`.
* Critical tori: `CritEq k u` (`E_0 u = 0`: `u = (A,2A,3A,B)`; `E_1 u = 0`: `u = (a,b,a+b,2a+b)`),
  `onCritTorus_of_act` : `CritEq k (g v)` gives `L4Tail.OnCritTorus v` (the bridge to `L4Tail`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S4.ChainRep
import LRSpectrumFull.L4Tail.NormalForm
import Mathlib.Data.Fin.Tuple.Sort

namespace LRSpectrumFull
namespace L4S4

open Matrix Finset LRSpectrumFull.L4S3

/-! ## 1. Records -/

/-- Depth-1 record (`T1`): row `h`, witness `x1 / W1` for `M(L_1)`, basis `b` of `h^⊥` with right inverse `r`, and `s`
with `h · s = 1`. -/
structure T1Rec4 where
  h : V4
  x1 : V4
  W1 : ℤ
  b : Fin 3 → V4
  r : Fin 3 → V4
  s : V4

/-- Leaf record (`kind = 0` noncritical, `kind = 1` critical): coordinates `t`, lift `y`, witness `x2 / W2` of `M(L_2)`
(noncritical only), the `K_2` certificate (`k` basis, `q` left inverse, `p`), the critical lattice index `ck` and the
signed permutation `g` of the critical identification. -/
structure LeafRec4 where
  t : Fin 3 → ℤ
  y : V4
  kind : ℕ
  x2 : V4
  W2 : ℤ
  k : Fin 2 → V4
  q : Fin 2 → V4
  p : Fin 4 → Fin 2 → ℤ
  ck : Fin 2
  g : SP

/-- Residual tuple (`T5`): a line with no witness in the time list (`kind 0`) or an extra time `a/q` (`kind 1`). -/
structure T5Rec4 where
  v : V4
  kind : ℕ
  a : ℤ
  q : ℤ
  mln : ℤ
  mld : ℤ

/-- The certificate: depth-1 records, leaf records (all nodes, in loop order), residual tuples. -/
structure Certificate4 where
  t1 : List T1Rec4
  leaves : List LeafRec4
  t5 : List T5Rec4

/-! ## 2. Depth-1 cover by sorting -/

theorem exists_sort_abs4 (h : V4) :
    ∃ g : SP, ∀ i j : Fin 4, i ≤ j → 0 ≤ g.act h i ∧ g.act h i ≤ g.act h j := by
  let a : Fin 4 → ℤ := fun i => |h i|
  let σ := Tuple.sort a
  have hm : Monotone (a ∘ σ) := Tuple.monotone_sort a
  let ε : Fin 4 → ℤ := fun i => if 0 ≤ h (σ i) then 1 else -1
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := fun i => by
    by_cases hh : 0 ≤ h (σ i) <;> simp [ε, hh]
  have key : ∀ i, (SP.act ⟨σ, ε, hε⟩ h) i = |h (σ i)| := by
    intro i
    by_cases hh : 0 ≤ h (σ i)
    · simp [SP.act, ε, hh, abs_of_nonneg hh]
    · simp [SP.act, ε, hh, abs_of_neg (not_le.mp hh)]
  refine ⟨⟨σ, ε, hε⟩, fun i j hij => ?_⟩
  rw [key, key]
  exact ⟨abs_nonneg _, hm hij⟩

/-- The depth-1 reps: sorted nonnegative primitive vectors with entries `≤ 4` and `2 ≤ |h|² ≤ 16`
(`9 |h|² < 148` is equivalent to `|h|² ≤ 16`). -/
def T1Ok4 (h : V4) : Prop :=
  (∀ i j : Fin 4, i ≤ j → 0 ≤ h i ∧ h i ≤ h j) ∧ (∀ i, h i ≤ 4) ∧ Primitive h ∧ 2 ≤ dot h h ∧ dot h h ≤ 16

theorem sq_le_dot4 (h : V4) (i : Fin 4) : h i * h i ≤ dot h h := by
  unfold dot
  exact Finset.single_le_sum (f := fun k => h k * h k) (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)

theorem depth1_cover4 (h : V4) (hp : Primitive h) (h2 : 2 ≤ dot h h) (h16 : dot h h ≤ 16) :
    ∃ g : SP, T1Ok4 (g.act h) := by
  obtain ⟨g, hg⟩ := exists_sort_abs4 h
  refine ⟨g, hg, fun i => ?_, primitive_act hp g, by rw [dot_act]; exact h2, by rw [dot_act]; exact h16⟩
  have h1 := sq_le_dot4 (g.act h) i
  rw [dot_act] at h1
  have h0 := (hg i i le_rfl).1
  nlinarith

/-- Near-tight: primitive, all entries nonzero, `ML < 1/4`. -/
def NearTight (v : V4) : Prop := Primitive v ∧ (∀ i, v i ≠ 0) ∧ ML v < 1 / 4

/-! ## 3. Critical tori and the bridge to `L4Tail.OnCritTorus` -/

/-- `E_0 u = 0` (`u = (A, 2A, 3A, B)`) and `E_1 u = 0` (`u = (a, b, a+b, 2a+b)`). -/
def CritEq (k : Fin 2) (u : V4) : Prop :=
  (k = 0 → u 1 = 2 * u 0 ∧ u 2 = 3 * u 0) ∧ (k = 1 → u 2 = u 0 + u 1 ∧ u 3 = 2 * u 0 + u 1)

theorem sps_of_act (g : SP) (v w : V4) (h : g.act v = w) : L4Tail.SPS v w 1 := by
  refine ⟨le_rfl, g.inv.σ, g.inv.ε, g.inv.hε, fun i => ?_⟩
  have e : v = g.inv.act w := by rw [← h, act_inv_act]
  have := congrFun e i
  simp only [SP.act] at this
  rw [this]; ring

/-- A vector whose image under a signed permutation satisfies `CritEq k` lies on a critical torus. -/
theorem onCritTorus_of_act {k : Fin 2} {g : SP} {v : V4} (h : CritEq k (g.act v)) : L4Tail.OnCritTorus v := by
  fin_cases k
  · obtain ⟨h1, h2⟩ := h.1 rfl
    have e : g.act v = L4Tail.U1v (g.act v 0) (g.act v 3) := by
      funext i; fin_cases i <;> simp [L4Tail.U1v, h1, h2]
    exact ⟨g.act v 0, g.act v 3, 1, Or.inl (sps_of_act g v _ e)⟩
  · obtain ⟨h1, h2⟩ := h.2 rfl
    have e : g.act v = L4Tail.U2v (g.act v 0) (g.act v 1) := by
      funext i; fin_cases i <;> simp [L4Tail.U2v, h1, h2]
    exact ⟨g.act v 0, g.act v 1, 1, Or.inr (sps_of_act g v _ e)⟩

/-- `CritEq` is a linear condition: it passes to integer combinations. -/
theorem critEq_comb (k : Fin 2) (a b : ℤ) (u w : V4) (hu : CritEq k u) (hw : CritEq k w) :
    CritEq k (fun i => a * u i + b * w i) := by
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨h1, h2⟩ := hu.1 hk; obtain ⟨h3, h4⟩ := hw.1 hk
    simp only [h1, h2, h3, h4]; constructor <;> ring
  · obtain ⟨h1, h2⟩ := hu.2 hk; obtain ⟨h3, h4⟩ := hw.2 hk
    simp only [h1, h2, h3, h4]; constructor <;> ring

end L4S4
end LRSpectrumFull
