/-
# L4S3.GreedyReduce : `FlagExists` reduced to the existence of a greedy `ℤ`-basis of `Λ`

`FlagBasis.lean` constructs `FlagData v` from an arbitrary `ℤ`-basis of `Λ = {x | x·v = 0}`.  Here the
construction is run on a GIVEN basis: if `h : Fin 3 → ℤ⁴` is `Greedy`, `ℤ`-independent and spans `Λ`
over `ℤ`, then there is a `FlagData v` with `F.h = h` (so `Greedy v F.h`).  The integer right inverse `R`
(saturation) and the rational LDL certificate are therefore automatic; the ONLY content of `FlagExists`
that is not in Lean is `GreedyBasis v`:

  `∃ h : Fin 3 → ℤ⁴, (∀ i, h_i·v = 0) ∧ LinearIndependent ℤ h ∧ (∀ x, x·v = 0 → x ∈ span_ℤ h) ∧ Greedy v h`.

`flagExists_of_greedyBasis : (∀ v, Primitive v → GreedyBasis v) → FlagExists`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.FlagBasis
import LRSpectrumFull.L4S3.Discharge

namespace LRSpectrumFull
namespace L4S3

open Finset

/-- Integer right inverse from an ARBITRARY `ℤ`-basis of `Λ`. -/
theorem exists_R_of_basis (v : V4) (hv : Primitive v) (B : Module.Basis (Fin 3) ℤ (Lam v)) :
    ∃ R : Fin 4 → Fin 3 → ℤ, ∀ i j : Fin 3,
      ∑ k : Fin 4, ((B i : Lam v) : V4) k * R k j = if i = j then 1 else 0 := by
  obtain ⟨u, hu⟩ := exists_dual v hv
  let φ : Fin 3 → V4 →ₗ[ℤ] ℤ := fun j => (B.coord j) ∘ₗ (projLam v u hu)
  refine ⟨fun k j => φ j (fun l => if k = l then 1 else 0), ?_⟩
  intro i j
  have hx : ((B i : Lam v) : V4) =
      ∑ k, ((B i : Lam v) : V4) k • (fun l : Fin 4 => if k = l then (1 : ℤ) else 0) :=
    pi_eq_sum_univ _
  have h2 : φ j ((B i : Lam v) : V4) = if i = j then 1 else 0 := by
    show B.coord j (projLam v u hu ((B i : Lam v) : V4)) = _
    rw [projLam_of_mem, B.coord_apply, B.repr_self, Finsupp.single_apply]
  have h3 : φ j ((B i : Lam v) : V4) =
      ∑ k, ((B i : Lam v) : V4) k * φ j (fun l => if k = l then 1 else 0) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [← h2, h3]

/-- A greedy `ℤ`-basis of `Λ = ℤ⁴ ∩ v^⊥`: rows in `Λ`, `ℤ`-independent, spanning `Λ` over `ℤ`
(saturation), and greedy.  This is the single statement that `FlagExists` still needs. -/
def GreedyBasis (v : V4) : Prop :=
  ∃ h : Fin 3 → V4, (∀ i, dot (h i) v = 0) ∧ LinearIndependent ℤ h ∧
    (∀ x : V4, dot x v = 0 → x ∈ Submodule.span ℤ (Set.range h)) ∧ Greedy v h

theorem flag_of_greedyBasis (v : V4) (hv : Primitive v) (hb : GreedyBasis v) :
    ∃ F : FlagData v, Greedy v F.h := by
  obtain ⟨h, hhv, hz, hsp, hg⟩ := hb
  let w : Fin 3 → Lam v := fun i => ⟨h i, mem_Lam.2 (hhv i)⟩
  have hli : LinearIndependent ℤ w := LinearIndependent.of_comp (Lam v).subtype hz
  have hsp' : ⊤ ≤ Submodule.span ℤ (Set.range w) := by
    intro x _
    rw [← Submodule.apply_mem_span_image_iff_mem_span (Submodule.injective_subtype (Lam v)),
      ← Set.range_comp]
    exact hsp x (mem_Lam.1 x.2)
  let B : Module.Basis (Fin 3) ℤ (Lam v) := Module.Basis.mk hli hsp'
  have hBh : ∀ i, ((B i : Lam v) : V4) = h i := fun i => by
    simp [B, Module.Basis.mk_apply, w]
  obtain ⟨R, hR⟩ := exists_R_of_basis v hv B
  obtain ⟨Lq, Dq, hL1, hL0, hD, hG⟩ := ldl_of_indep h (indepQ_of_indepZ h hz)
  refine ⟨⟨h, R, hhv, ?_, Lq, Dq, hL1, hL0, hD, hG⟩, hg⟩
  intro i j
  simpa [hBh] using hR i j

/-- `FlagExists` follows from the existence of a greedy `ℤ`-basis of `Λ` for every primitive `v`. -/
theorem flagExists_of_greedyBasis (H : ∀ v : V4, Primitive v → GreedyBasis v) : FlagExists :=
  fun v hv => flag_of_greedyBasis v hv (H v hv)

/-- Hence the whole stage chain (`stage_bound`, `stage_prune`, `leaf_strand`, `window_lo`) holds from
`GreedyBasis` alone. -/
theorem flagGeometry_of_greedyBasis (H : ∀ v : V4, Primitive v → GreedyBasis v) : FlagGeometry :=
  flagGeometry_of_exists (flagExists_of_greedyBasis H)

end L4S3
end LRSpectrumFull
