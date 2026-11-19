/-
# L4S3.GreedyDim : the two dimension facts used by the greedy construction

For `Λ = ℤ⁴ ∩ v^⊥` (rank 3):
* `dim_nonempty` : fewer than four vectors never span `Λ` over `ℚ` (`∃ u ∈ Λ` outside their rational span);
* `dim_span`     : four `ℚ`-independent vectors of `Λ` span every vector of `Λ` over `ℚ`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.GreedyAlg
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace LRSpectrumFull
namespace L4S3

open Finset

/-- The `ℚ`-image of the `ℤ`-basis of `Λ`. -/
noncomputable def lamQ (v : V4) (hv : Primitive v) : Fin 3 → (Fin 4 → ℚ) :=
  fun i => castV (((lamBasis v hv) i : Lam v) : V4)

theorem lamQ_indep (v : V4) (hv : Primitive v) : LinearIndependent ℚ (lamQ v hv) := by
  have hz : LinearIndependent ℤ (fun i : Fin 3 => (((lamBasis v hv) i : Lam v) : V4)) :=
    (lamBasis v hv).linearIndependent.map' (Lam v).subtype (Submodule.ker_subtype _)
  exact Fintype.linearIndependent_iff.2 (fun c hc i => indepQ_of_indepZ _ hz c hc i)

theorem castV_mem_span_lam (v : V4) (hv : Primitive v) (x : V4) (hx : dot x v = 0) :
    castV x ∈ Submodule.span ℚ (Set.range (lamQ v hv)) := by
  set B := lamBasis v hv with hB
  let x' : Lam v := ⟨x, mem_Lam.2 hx⟩
  have h1 : x = ∑ i, (B.repr x' i) • (((B i : Lam v)) : V4) := by
    have h0 := congrArg (fun y : Lam v => (y : V4)) (B.sum_repr x')
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h0
    exact h0.symm
  have h2 : castV x = ∑ i, (B.repr x' i) • lamQ v hv i := by
    rw [← castL_apply, h1, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_zsmul, castL_apply]; rfl
  rw [h2]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _

theorem dim_nonempty (v : V4) (hv : Primitive v) (j : ℕ) (hj : j < 3) (h : Fin 3 → V4) :
    ∃ u : V4, dot u v = 0 ∧ ¬ InQN j h u := by
  by_contra hcon
  push_neg at hcon
  classical
  let w : Finset (Fin 4 → ℚ) := Finset.univ.image (fun n : Fin j => castV (hN h n.val))
  have hrange : Set.range (lamQ v hv) ≤ (Submodule.span ℚ (w : Set (Fin 4 → ℚ)) : Set _) := by
    rintro _ ⟨i, rfl⟩
    have hmem : dot (((lamBasis v hv) i : Lam v) : V4) v = 0 := mem_Lam.1 ((lamBasis v hv) i).2
    obtain ⟨a, ha⟩ := hcon _ hmem
    have e : lamQ v hv i = ∑ n : Fin j, a n.val • castV (hN h n.val) := by
      funext k
      simp only [lamQ, castV, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [ha k, Finset.sum_range]
    show lamQ v hv i ∈ Submodule.span ℚ (w : Set (Fin 4 → ℚ))
    rw [e]
    refine Submodule.sum_mem _ (fun n _ => ?_)
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [w]))
  have hle := linearIndependent_le_span' (lamQ v hv) (lamQ_indep v hv) (w : Set (Fin 4 → ℚ)) hrange
  have hcard : Fintype.card (w : Set (Fin 4 → ℚ)) ≤ j := by
    simp only [Finset.coe_sort_coe, Fintype.card_coe]
    exact (Finset.card_image_le).trans (by simp)
  simp only [Cardinal.mk_fintype, Fintype.card_fin] at hle
  have : (3 : ℕ) ≤ Fintype.card (w : Set (Fin 4 → ℚ)) := by exact_mod_cast hle
  omega

theorem dim_span (v : V4) (hv : Primitive v) (h : Fin 3 → V4) (hP : ∀ n : ℕ, n < 3 → dot (hN h n) v = 0)
    (hI : IndN 3 h) (x : V4) (hx : dot x v = 0) : InQN 3 h x := by
  have hq : LinearIndependent ℚ (fun n : Fin 3 => castV (h n)) := by
    refine Fintype.linearIndependent_iff.2 (fun c hc i => ?_)
    have := hI (fun n => if hn : n < 3 then c ⟨n, hn⟩ else 0) (fun k => by
      have h3 := congr_fun hc k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, castV] at h3
      rw [← h3, Finset.sum_range]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      simp [hN_lt, n.2]) i.val i.2
    simpa [i.2] using this
  set Hq := Submodule.span ℚ (Set.range (fun n : Fin 3 => castV (h n))) with hHq
  set Vq := Submodule.span ℚ (Set.range (lamQ v hv)) with hVq
  have hle : Hq ≤ Vq := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, rfl⟩
    exact castV_mem_span_lam v hv (h n) (by simpa [hN_lt] using hP n.val n.2)
  have hH : Module.finrank ℚ Hq = 3 := by rw [hHq, finrank_span_eq_card hq]; simp
  have hV : Module.finrank ℚ Vq = 3 := by rw [hVq, finrank_span_eq_card (lamQ_indep v hv)]; simp
  have heq : Hq = Vq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hH, hV])
  have hxm : castV x ∈ Hq := by rw [heq]; exact castV_mem_span_lam v hv x hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hxm
  refine ⟨fun n => if hn : n < 3 then c ⟨n, hn⟩ else 0, fun k => ?_⟩
  have h3 := congr_fun hc k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castV] at h3
  rw [← h3, Finset.sum_range]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp [hN_lt, n.2]

end L4S3
end LRSpectrumFull
