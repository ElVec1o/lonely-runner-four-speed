/-
# L4S4.EiBad : the integer test `ei_bad` of the generator versus the span condition behind `NoCoord`

The generator's `ei_bad(nd, t)` returns true iff for some coordinate `i` the row `(b_a[i])_a` (the node coordinates `tvec b e_i`)
is parallel to `t`: `b_a[i] · t_{a'} = b_{a'}[i] · t_a` for all `a < a'`.  The Lean property (`NoCoord`) says
`e_i ∉ ℚ L_d` for the new lattice `L_d = ℤ l_0 + … + ℤ l_{j-1} + ℤ y`.

* `eiBad`, `InQExt`      the Rust test; `e_i ∈ ℚ·span(l_0, …, l_{j-1}, y)`.
* `eiBad_of_inQ`         span ==> parallel (any node; no hypothesis on `t`).
* `inQ_of_eiBad`         parallel ==> span, for a node `NodeId l b s r` and `t = tvec b y ≠ 0`
                         (uses the integer lattice lemma `lat_of_orth`; `ls` is needed).
* `eiBad_iff`            the equivalence.  Consequently `¬ ei_bad` ⟺ no `e_i` in `ℚ span(l, y)`, the condition
                         `NoCoord` of the chain (for `d = j+1 ≤ 4`, i.e. at least two node coordinates are in play).

Note: for `d = 1` (`j = 4`) `ei_bad` is vacuously true (no pair `a < a'`), consistent with `ℚ L_5 = ℚ⁵ ∋ e_i`;
`children` is never called there.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S4.Prim

namespace LRSpectrumFull
namespace L4S4

open Matrix Finset LRSpectrumFull.L4S3

/-- The generator's `ei_bad`: some coordinate row of `b` is parallel to `t` (all `2×2` minors vanish). -/
def eiBad {d : ℕ} (b : Fin d → V4) (t : Fin d → ℤ) : Prop :=
  ∃ i : Fin 4, ∀ a a' : Fin d, a < a' → b a i * t a' = b a' i * t a

/-- `u` lies in the rational span of `l_0, …, l_{j-1}, y`. -/
def InQExt {j : ℕ} (l : Fin j → V4) (y u : V4) : Prop :=
  ∃ (c : Fin j → ℚ) (c0 : ℚ), ∀ a, (u a : ℚ) = ∑ k, c k * (l k a : ℚ) + c0 * (y a : ℚ)

theorem dotQ (x y : V4) : (dot x y : ℚ) = ∑ i, (x i : ℚ) * (y i : ℚ) := by simp [dot]

theorem eiBad_of_inQ {j d : ℕ} {l : Fin j → V4} {b : Fin d → V4} {s : Fin j → V4} {r : Fin d → V4}
    (hN : NodeId l b s r) (y : V4) (i : Fin 4) (h : InQExt l y (eVec i)) : eiBad b (tvec b y) := by
  obtain ⟨c, c0, hc⟩ := h
  refine ⟨i, fun a a' _ => ?_⟩
  have key : ∀ a : Fin d, (b a i : ℚ) = c0 * (tvec b y a : ℚ) := by
    intro a
    have h1 : (b a i : ℚ) = ∑ x, (b a x : ℚ) * (eVec i x : ℚ) := by simp [eVec]
    have h2 : ∑ x, (b a x : ℚ) * (eVec i x : ℚ)
        = ∑ x, (b a x : ℚ) * (∑ k, c k * (l k x : ℚ) + c0 * (y x : ℚ)) :=
      Finset.sum_congr rfl (fun x _ => by rw [hc x])
    have h3 : ∑ x, (b a x : ℚ) * (∑ k, c k * (l k x : ℚ) + c0 * (y x : ℚ))
        = ∑ k, c k * (dot (b a) (l k) : ℚ) + c0 * (dot (b a) y : ℚ) := by
      simp only [dotQ, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun x _ => by ring))
      · exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [h1, h2, h3]
    simp [hN.bl a, tvec]
  have e : (b a i : ℚ) * (tvec b y a' : ℚ) = (b a' i : ℚ) * (tvec b y a : ℚ) := by
    rw [key a, key a']; ring
  exact_mod_cast e

theorem inQ_of_eiBad {j d : ℕ} (hjd : j + d = 4) {l : Fin j → V4} {b : Fin d → V4} {s : Fin j → V4}
    {r : Fin d → V4} (hN : NodeId l b s r) (y : V4) (ht : ∃ m, tvec b y m ≠ 0)
    (h : eiBad b (tvec b y)) : ∃ i, InQExt l y (eVec i) := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨m, hm⟩ := ht
  refine ⟨i, ?_⟩
  have hsym : ∀ a a' : Fin d, b a i * tvec b y a' = b a' i * tvec b y a := by
    intro a a'
    rcases lt_trichotomy a a' with h | h | h
    · exact hi a a' h
    · rw [h]
    · exact (hi a' a h).symm
  obtain ⟨T, hT⟩ : ∃ T, T = tvec b y m := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : V4, u = fun x => T * eVec i x - b m i * y x := ⟨_, rfl⟩
  have hux : ∀ x, u x = T * eVec i x - b m i * y x := fun x => by rw [hudef]
  have hu : ∀ a, dot (b a) u = 0 := by
    intro a
    have e1 : dot (b a) (eVec i) = b a i := by simp [dot, eVec]
    have e2 : dot (b a) u = T * dot (b a) (eVec i) - b m i * dot (b a) y := by
      unfold dot
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun x _ => by rw [hux x]; ring)
    rw [e2, e1]
    have := hsym a m
    have hT' : T = dot (b m) y := by rw [hT]; rfl
    unfold tvec at this
    rw [hT']
    linarith
  have hl := lat_of_orth hjd hN u hu
  have hTq : (T : ℚ) ≠ 0 := by rw [hT]; exact_mod_cast hm
  refine ⟨fun k => (dot (s k) u : ℚ) / (T : ℚ), (b m i : ℚ) / (T : ℚ), fun x => ?_⟩
  have hq : (T : ℚ) * (eVec i x : ℚ) - (b m i : ℚ) * (y x : ℚ)
      = ∑ k, (dot (s k) u : ℚ) * (l k x : ℚ) := by
    have := hl x
    rw [hux x] at this
    have := congrArg (Int.cast : ℤ → ℚ) this
    push_cast at this
    exact this
  show (eVec i x : ℚ) = ∑ k, ((dot (s k) u : ℚ) / (T : ℚ)) * (l k x : ℚ)
    + ((b m i : ℚ) / (T : ℚ)) * (y x : ℚ)
  apply mul_left_cancel₀ hTq
  have hr : (T : ℚ) * (∑ k, ((dot (s k) u : ℚ) / (T : ℚ)) * (l k x : ℚ)
      + ((b m i : ℚ) / (T : ℚ)) * (y x : ℚ))
      = ∑ k, (dot (s k) u : ℚ) * (l k x : ℚ) + (b m i : ℚ) * (y x : ℚ) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun k _ => by field_simp)
    · field_simp
  rw [hr]
  linarith

theorem eiBad_iff {j d : ℕ} (hjd : j + d = 4) {l : Fin j → V4} {b : Fin d → V4} {s : Fin j → V4}
    {r : Fin d → V4} (hN : NodeId l b s r) (y : V4) (ht : ∃ m, tvec b y m ≠ 0) :
    eiBad b (tvec b y) ↔ ∃ i, InQExt l y (eVec i) :=
  ⟨inQ_of_eiBad hjd hN y ht, fun ⟨i, h⟩ => eiBad_of_inQ hN y i h⟩

end L4S4
end LRSpectrumFull
