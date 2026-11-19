/-
# L4S4.Link : node data and the flag (chain, complement and norm formula together), plus a non-vacuity instance

For a flag `F` of `v` and a node `(l, b, s, r)` whose chain rows `l` are the first `j` rows of
`F` (`NodeId (fun i : Fin j => hN F.h i) b s r`):

* `flag_minor_node` : `G_j = leadMinor (gram F) j = gF b` (the generator's `gs[j]`),
                      `G_{j+1} = qform b (h_j) = t^T adj(a) t` with `t_i = b_i · h_j`,
                      `μ_{j+1}² = Dq_j = (t^T adj(a) t) / G_j` (the integer norm formula).
* `node_minor_chain`: the same `G_j` for any flag with the same chain level `j` .
* `tvec_of_lat`    : `t = B y` is unchanged when `y` moves by an integer combination of the rows `l`.
* `nodeId_example`  : a concrete inhabited `NodeId` (`j = 1`, `l = e_1`), with the formula evaluated on one `y`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S4.Dict
import LRSpectrumFull.L4S4.Chain
import LRSpectrumFull.L4S3.Minors

namespace LRSpectrumFull
namespace L4S4

open Matrix Finset LRSpectrumFull.L4S3

theorem snoc_eq_hN {v : V4} (F : FlagData v) (j : ℕ) (hj : j < 3) :
    (Fin.snoc (α := fun _ => V4) (fun i : Fin j => hN F.h i.val) (F.h ⟨j, hj⟩) : Fin (j + 1) → V4)
      = fun i : Fin (j + 1) => hN F.h i.val := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [hN, hj]
  · simp [Fin.snoc_castSucc]

theorem flag_minor_node {v : V4} (F : FlagData v) {j d : ℕ} (hjd : j + d = 4) (hj : j < 3)
    {b : Fin d → V4} {s : Fin j → V4} {r : Fin d → V4}
    (hnode : NodeId (fun i : Fin j => hN F.h i.val) b s r) :
    leadMinor (gram F) j = gF b ∧
    leadMinor (gram F) (j + 1) = qform b (F.h ⟨j, hj⟩) ∧
    F.Dq ⟨j, hj⟩ = (qform b (F.h ⟨j, hj⟩) : ℚ) / (gF b : ℚ) := by
  have h1 : leadMinor (gram F) j = gF b := by
    rw [leadMinor_eq_gF F j (by omega), gF_compl hjd hnode]
  have h2 : leadMinor (gram F) (j + 1) = qform b (F.h ⟨j, hj⟩) := by
    rw [leadMinor_eq_gF F (j + 1) (by omega), ← snoc_eq_hN F j hj, gF_snoc hjd hnode]
  refine ⟨h1, h2, ?_⟩
  rw [Dq_minors_thm v F ⟨j, hj⟩]
  simp only [h1, h2]

theorem node_minor_chain {v : V4} (F F' : FlagData v) {j d : ℕ} (hjd : j + d = 4) (hj : j < 3)
    (hc : SameChain F F' j) {b : Fin d → V4} {s : Fin j → V4} {r : Fin d → V4}
    (hnode : NodeId (fun i : Fin j => hN F'.h i.val) b s r) :
    leadMinor (gram F) j = gF b := by
  rw [← leadMinor_chain F F' j (by omega) hc]
  exact (flag_minor_node F' hjd hj hnode).1

theorem tvec_of_lat {j d : ℕ} {l : Fin j → V4} {b : Fin d → V4} {s : Fin j → V4} {r : Fin d → V4}
    (hnode : NodeId l b s r) (y : V4) (c : Fin j → ℤ) :
    tvec b (fun a => y a + ∑ k, c k * l k a) = tvec b y := by
  funext i
  unfold tvec dot
  have : ∀ a, b i a * (y a + ∑ k, c k * l k a) = b i a * y a + ∑ k, c k * (b i a * l k a) := by
    intro a; rw [mul_add, Finset.mul_sum]
    congr 1; exact Finset.sum_congr rfl (fun k _ => by ring)
  simp only [this, Finset.sum_add_distrib]
  have h2 : ∑ a, ∑ k, c k * (b i a * l k a) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero; intro k _
    rw [← Finset.mul_sum]
    have := hnode.bl i k
    unfold dot at this
    rw [this, mul_zero]
  rw [h2, add_zero]

end L4S4
end LRSpectrumFull
