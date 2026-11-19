/-
# L4S3.FlagBasis : existence of a `FlagData` for every primitive `v` (any basis, no greedy)

For a primitive `v : ℤ⁴`:

* `Λ = {x | x·v = 0}` is a free `ℤ`-module of rank 3 (rank-nullity over `ℤ`, `finrank_Lam`), so it has a
  `ℤ`-basis `b` (`Module.finBasisOfFinrankEq`);
* `ℤ⁴ = Λ ⊕ ℤ u` with `u·v = 1` (`exists_dual`), the projection `x ↦ x - (x·v) u` is `ℤ`-linear, and the
  coordinate functionals of `b` composed with it give the integer right inverse `R` (`H R = I`);
* the rows `h_i = b_i` are `ℚ`-independent, and a rational Gram-Schmidt (`gs_exists`) gives the LDL
  certificate `Lq, Dq` with `Dq_k = |b*_k|² > 0`.

Result: `flagExistsBasis : ∀ v, Primitive v → Nonempty (FlagData v)`; `stage_bound_free`,
`stage_prune_free`: the stage chain for every primitive `v` WITHOUT the `FlagGeometry` structure and without
`Greedy` (the stage tests do not use `Greedy`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.Skeleton
import LRSpectrumFull.L4S3.Minors
import LRSpectrumFull.L4S3.Dist
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Fin

namespace LRSpectrumFull
namespace L4S3

open Finset

/-! ## Part 1: rational Gram-Schmidt -/

theorem gs_exists (f : ℕ → Fin 4 → ℚ) : ∀ N : ℕ,
    (∀ c : ℕ → ℚ, ∑ k ∈ range N, c k • f k = 0 → ∀ k < N, c k = 0) →
    ∃ (L : ℕ → ℕ → ℚ) (b : ℕ → Fin 4 → ℚ),
      (∀ n < N, f n = b n + ∑ k ∈ range n, L n k • b k) ∧
      (∀ m n, m < n → n < N → dotProduct (b n) (b m) = 0) ∧
      (∀ n < N, b n ≠ 0) ∧
      (∀ n < N, b n ∈ Submodule.span ℚ (f '' ↑(range (n + 1)))) := by
  intro N
  induction N with
  | zero =>
    intro _
    exact ⟨fun _ _ => 0, fun _ => 0, by simp, by simp, by simp, by simp⟩
  | succ N ih =>
    intro hind
    have hindN : ∀ c : ℕ → ℚ, ∑ k ∈ range N, c k • f k = 0 → ∀ k < N, c k = 0 := by
      intro c hc k hk
      have h0 : ∑ j ∈ range (N + 1), (if j = N then (0 : ℚ) else c j) • f j = 0 := by
        rw [sum_range_succ, if_pos rfl, zero_smul, add_zero, ← hc]
        exact sum_congr rfl (fun j hj => by simp [(mem_range.1 hj).ne])
      have := hind (fun j => if j = N then (0 : ℚ) else c j) h0 k (by omega)
      simpa [(show k ≠ N by omega)] using this
    obtain ⟨L, b, h1, h2, h3, h4⟩ := ih hindN
    classical
    have hbb : ∀ k < N, dotProduct (b k) (b k) ≠ 0 :=
      fun k hk h => h3 k hk (dotProduct_self_eq_zero.1 h)
    have horth : ∀ k m, k < N → m < N → k ≠ m → dotProduct (b k) (b m) = 0 := by
      intro k m hk hm hkm
      rcases lt_or_gt_of_ne hkm with h | h
      · rw [dotProduct_comm]; exact h2 k m h hm
      · exact h2 m k h hk
    set cN : ℕ → ℚ := fun k => dotProduct (f N) (b k) / dotProduct (b k) (b k) with hcN
    set bN : Fin 4 → ℚ := f N - ∑ k ∈ range N, cN k • b k with hbN
    have horthN : ∀ m < N, dotProduct bN (b m) = 0 := by
      intro m hm
      have hs : dotProduct (∑ k ∈ range N, cN k • b k) (b m) = cN m * dotProduct (b m) (b m) := by
        rw [sum_dotProduct, sum_eq_single m]
        · simp [smul_dotProduct]
        · intro k hk hkm
          simp [smul_dotProduct, horth k m (mem_range.1 hk) hm hkm]
        · intro hm'; exact absurd (mem_range.2 hm) hm'
      rw [hbN, sub_dotProduct, hs, hcN]
      simp only
      rw [div_mul_cancel₀ _ (hbb m hm), sub_self]
    have hbNne : bN ≠ 0 := by
      intro h0
      have hfN : f N = ∑ k ∈ range N, cN k • b k := sub_eq_zero.1 h0
      have hmem : f N ∈ Submodule.span ℚ (f '' ↑(range N)) := by
        rw [hfN]
        apply Submodule.sum_mem
        intro k hk
        apply Submodule.smul_mem
        have hk' := mem_range.1 hk
        refine Submodule.span_mono (Set.image_mono ?_) (h4 k hk')
        intro j hj
        simp only [coe_range, Set.mem_Iio] at hj ⊢
        omega
      rw [Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
      obtain ⟨c, hc⟩ := hmem
      have hsum : ∑ j ∈ range N, (if j = N then (-1 : ℚ) else c j) • f j = ∑ j ∈ range N, c j • f j :=
        sum_congr rfl (fun j hj => by simp [(mem_range.1 hj).ne])
      have h0' : ∑ j ∈ range (N + 1), (if j = N then (-1 : ℚ) else c j) • f j = 0 := by
        rw [sum_range_succ, if_pos rfl, hsum, hc]; simp
      have := hind (fun j => if j = N then (-1 : ℚ) else c j) h0' N (by omega)
      simp at this
    refine ⟨fun n k => if n = N then cN k else L n k, fun n => if n = N then bN else b n,
      ?_, ?_, ?_, ?_⟩
    · intro n hn
      by_cases hnN : n = N
      · subst hnN
        simp only [if_true]
        have : ∑ k ∈ range n, cN k • (if k = n then bN else b k) = ∑ k ∈ range n, cN k • b k :=
          sum_congr rfl (fun k hk => by simp [(mem_range.1 hk).ne])
        rw [this, hbN, sub_add_cancel]
      · have hn' : n < N := by omega
        simp only [hnN, if_false]
        rw [h1 n hn']
        congr 1
        exact sum_congr rfl (fun k hk => by
          have : k ≠ N := by have := mem_range.1 hk; omega
          simp [this])
    · intro m n hmn hn
      have hmN : m ≠ N := by omega
      by_cases hnN : n = N
      · subst hnN
        simp only [if_true, hmN, if_false]
        exact horthN m (by omega)
      · have hn' : n < N := by omega
        simp only [hnN, hmN, if_false]
        exact h2 m n hmn hn'
    · intro n hn
      by_cases hnN : n = N
      · subst hnN; simpa using hbNne
      · simpa [hnN] using h3 n (by omega)
    · intro n hn
      by_cases hnN : n = N
      · subst hnN
        simp only [if_true]
        rw [hbN]
        apply Submodule.sub_mem
        · exact Submodule.subset_span ⟨n, by simp, rfl⟩
        · apply Submodule.sum_mem
          intro k hk
          apply Submodule.smul_mem
          have hk' := mem_range.1 hk
          refine Submodule.span_mono (Set.image_mono ?_) (h4 k hk')
          intro j hj
          simp only [coe_range, Set.mem_Iio] at hj ⊢
          omega
      · simpa [hnN] using h4 n (by omega)

/-! ## Part 2: LDL certificate from `ℚ`-independence of four integer rows -/

/-- Cast of an integer vector to `ℚ⁵`. -/
def castV (x : V4) : Fin 4 → ℚ := fun i => (x i : ℚ)

theorem dot_cast (x y : V4) : ((dot x y : ℤ) : ℚ) = dotProduct (castV x) (castV y) := by
  simp [dot, castV, dotProduct]

theorem ldl_of_indep (h : Fin 3 → V4)
    (hind : ∀ c : Fin 3 → ℚ, ∑ i, c i • castV (h i) = 0 → ∀ i, c i = 0) :
    ∃ (Lq : Fin 3 → Fin 3 → ℚ) (Dq : Fin 3 → ℚ),
      (∀ i, Lq i i = 1) ∧ (∀ i j, i < j → Lq i j = 0) ∧ (∀ i, 0 < Dq i) ∧
      ∀ i j, (dot (h i) (h j) : ℚ) = ∑ k, Lq i k * Dq k * Lq j k := by
  classical
  set f : ℕ → Fin 4 → ℚ := fun n => if hn : n < 3 then castV (h ⟨n, hn⟩) else 0 with hf
  have hfi : ∀ i : Fin 3, f i.val = castV (h i) := by
    intro i; simp [hf, i.2]
  have hindN : ∀ c : ℕ → ℚ, ∑ k ∈ range 3, c k • f k = 0 → ∀ k < 3, c k = 0 := by
    intro c hc k hk
    have : ∑ i : Fin 3, c i.val • castV (h i) = 0 := by
      rw [← hc, Finset.sum_range]
      exact sum_congr rfl (fun i _ => by rw [hfi])
    have := hind (fun i => c i.val) this ⟨k, hk⟩
    simpa using this
  obtain ⟨L, b, h1, h2, h3, h4⟩ := gs_exists f 3 hindN
  set L' : ℕ → ℕ → ℚ := fun n k => if k < n then L n k else if k = n then 1 else 0 with hL'
  have hrep : ∀ n < 3, f n = ∑ k ∈ range 3, L' n k • b k := by
    intro n hn
    have hsub : ∑ k ∈ range 3, L' n k • b k = ∑ k ∈ range (n + 1), L' n k • b k := by
      symm
      apply sum_subset
      · intro k hk; simp only [mem_range] at hk ⊢; omega
      · intro k hk hk'
        simp only [mem_range] at hk hk'
        simp [hL', show ¬ k < n by omega, show k ≠ n by omega]
    rw [hsub, sum_range_succ, h1 n hn]
    have : ∑ k ∈ range n, L' n k • b k = ∑ k ∈ range n, L n k • b k :=
      sum_congr rfl (fun k hk => by simp [hL', mem_range.1 hk])
    rw [this]
    simp [hL', add_comm]
  have horth : ∀ k l, k < 3 → l < 3 → k ≠ l → dotProduct (b k) (b l) = 0 := by
    intro k l hk hl hkl
    rcases lt_or_gt_of_ne hkl with hh | hh
    · rw [dotProduct_comm]; exact h2 k l hh hl
    · exact h2 l k hh hk
  have hDpos : ∀ k < 3, 0 < dotProduct (b k) (b k) := by
    intro k hk
    have hne : dotProduct (b k) (b k) ≠ 0 := fun h0 => h3 k hk (dotProduct_self_eq_zero.1 h0)
    have hnn : 0 ≤ dotProduct (b k) (b k) :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  have hgram : ∀ i j : ℕ, i < 3 → j < 3 →
      dotProduct (f i) (f j) = ∑ k ∈ range 3, L' i k * dotProduct (b k) (b k) * L' j k := by
    intro i j hi hj
    rw [hrep i hi, hrep j hj, sum_dotProduct]
    apply sum_congr rfl
    intro k hk
    rw [smul_dotProduct, dotProduct_sum, sum_eq_single k]
    · rw [dotProduct_smul]; simp only [smul_eq_mul]; ring
    · intro l hl hlk
      rw [dotProduct_smul, horth k l (mem_range.1 hk) (mem_range.1 hl) (Ne.symm hlk)]; simp
    · intro hk'; exact absurd hk hk'
  refine ⟨fun i j => L' i.val j.val, fun k => dotProduct (b k.val) (b k.val), ?_, ?_, ?_, ?_⟩
  · intro i; simp [hL']
  · intro i j hij
    have h5 : ¬ j.val < i.val := by have := Fin.lt_def.1 hij; omega
    have h6 : j.val ≠ i.val := by have := Fin.lt_def.1 hij; omega
    simp [hL', h5, h6]
  · intro k; exact hDpos k.val k.2
  · intro i j
    rw [dot_cast, ← hfi i, ← hfi j, hgram i.val j.val i.2 j.2, Finset.sum_range]

/-! ## Part 3: the lattice `Λ = {x | x·v = 0}`, its `ℤ`-basis, the integer right inverse -/

theorem dot_smul_left (c : ℤ) (x y : V4) : dot (c • x) y = c * dot x y := by
  simp [dot, Finset.mul_sum, mul_assoc]

theorem dot_sub_left (x y z : V4) : dot (x - y) z = dot x z - dot y z := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

/-- `x ↦ x·v` as a `ℤ`-linear functional. -/
def dotLin (v : V4) : V4 →ₗ[ℤ] ℤ where
  toFun x := dot x v
  map_add' x y := by simp [dot, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [dot, Finset.mul_sum, mul_assoc]

/-- The relation lattice `Λ = ℤ⁴ ∩ v^⊥`. -/
def Lam (v : V4) : Submodule ℤ V4 := LinearMap.ker (dotLin v)

theorem mem_Lam {v x : V4} : x ∈ Lam v ↔ dot x v = 0 := by
  simp [Lam, dotLin]

theorem finrank_Lam (v : V4) (hv : Primitive v) : Module.finrank ℤ (Lam v) = 3 := by
  obtain ⟨u, hu⟩ := exists_dual v hv
  have hsurj : Function.Surjective (dotLin v) := fun n =>
    ⟨n • u, by show dot (n • u) v = n; rw [dot_smul_left, hu, mul_one]⟩
  have h := LinearMap.rank_eq_of_surjective hsurj
  rw [rank_fin_fun, Module.rank_self] at h
  have hfin : Module.rank ℤ (LinearMap.ker (dotLin v)) =
      (Module.finrank ℤ (LinearMap.ker (dotLin v)) : Cardinal) :=
    (Module.finrank_eq_rank ℤ _).symm
  rw [hfin] at h
  have h' : (4 : ℕ) = 1 + Module.finrank ℤ (LinearMap.ker (dotLin v)) := by exact_mod_cast h
  show Module.finrank ℤ (LinearMap.ker (dotLin v)) = 3
  omega

/-- A `ℤ`-basis of `Λ` indexed by `Fin 3`. -/
noncomputable def lamBasis (v : V4) (hv : Primitive v) : Module.Basis (Fin 3) ℤ (Lam v) :=
  Module.finBasisOfFinrankEq ℤ (Lam v) (finrank_Lam v hv)

/-- The projection `x ↦ x - (x·v) u` onto `Λ`, for `u·v = 1`. -/
def projLam (v u : V4) (hu : dot u v = 1) : V4 →ₗ[ℤ] Lam v :=
  LinearMap.codRestrict (Lam v) (LinearMap.id - (dotLin v).smulRight u) (by
    intro x
    rw [mem_Lam]
    show dot (x - dot x v • u) v = 0
    rw [dot_sub_left, dot_smul_left, hu]; ring)

theorem projLam_of_mem (v u : V4) (hu : dot u v = 1) (x : Lam v) :
    projLam v u hu (x : V4) = x := by
  apply Subtype.ext
  show (x : V4) - dot (x : V4) v • u = x
  rw [mem_Lam.1 x.2, zero_smul, sub_zero]

theorem exists_basis_R (v : V4) (hv : Primitive v) :
    ∃ (h : Fin 3 → V4) (R : Fin 4 → Fin 3 → ℤ), (∀ i, dot (h i) v = 0) ∧
      (∀ i j : Fin 3, ∑ k : Fin 4, h i k * R k j = if i = j then 1 else 0) ∧
      LinearIndependent ℤ h := by
  obtain ⟨u, hu⟩ := exists_dual v hv
  set B := lamBasis v hv with hB
  let φ : Fin 3 → V4 →ₗ[ℤ] ℤ := fun j => (B.coord j) ∘ₗ (projLam v u hu)
  refine ⟨fun i => ((B i : Lam v) : V4), fun k j => φ j (fun l => if k = l then 1 else 0),
    ?_, ?_, ?_⟩
  · intro i; exact mem_Lam.1 (B i).2
  · intro i j
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
  · exact B.linearIndependent.map' (Lam v).subtype (Submodule.ker_subtype _)

/-! ## Part 4: `ℚ`-independence and the flag -/

/-- Cast `ℤ⁴ → ℚ⁵` as a `ℤ`-linear map. -/
def castL : V4 →ₗ[ℤ] (Fin 4 → ℚ) :=
  LinearMap.pi (fun i => (Int.castAddHom ℚ).toIntLinearMap ∘ₗ LinearMap.proj i)

theorem castL_apply (x : V4) : castL x = castV x := rfl

theorem castL_ker : LinearMap.ker castL = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  funext i
  have := congr_fun hx i
  simpa [castL] using this

theorem indepQ_of_indepZ (h : Fin 3 → V4) (hz : LinearIndependent ℤ h) :
    ∀ c : Fin 3 → ℚ, ∑ i, c i • castV (h i) = 0 → ∀ i, c i = 0 := by
  have h2 : LinearIndependent ℤ (castL ∘ h) := hz.map' castL castL_ker
  have h3 : LinearIndependent ℚ (castL ∘ h) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 h2
  intro c hc
  exact Fintype.linearIndependent_iff.1 h3 c hc

/-- Flag existence for ANY basis (no greedy): every primitive `v` has a `FlagData`. -/
theorem flagExistsBasis (v : V4) (hv : Primitive v) : Nonempty (FlagData v) := by
  obtain ⟨h, R, hhv, hR, hz⟩ := exists_basis_R v hv
  obtain ⟨Lq, Dq, hL1, hL0, hD, hG⟩ := ldl_of_indep h (indepQ_of_indepZ h hz)
  exact ⟨⟨h, R, hhv, hR, Lq, Dq, hL1, hL0, hD, hG⟩⟩

/-- The intermediate statement: flag existence without `Greedy`. -/
def FlagExistsBasis : Prop := ∀ v : V4, Primitive v → Nonempty (FlagData v)

theorem flagExistsBasis_all : FlagExistsBasis := flagExistsBasis

/-! ## Part 5: the stage chain without `FlagGeometry` -/

/-- Test (i): the stage bound for every flag of a primitive `v` (no `Greedy`, no `FlagGeometry`). -/
theorem stage_bound_free (v : V4) (F : FlagData v) (k : ℕ) (x : Fin 4 → ℝ)
    (hv : Primitive v) (hx : StageWitness F k x) :
    fmin x - 1 / 2 * Real.sqrt (Sk F k) ≤ ML v := by
  obtain ⟨z, t, h⟩ := stage_dist_thm v F k x hv hx
  have hS := Sk_nonneg F k
  apply ML_ge_of_close v x z t _ (by positivity)
  have : (1 / 2 * Real.sqrt (Sk F k)) ^ 2 = 1 / 4 * Sk F k := by
    rw [mul_pow, Real.sq_sqrt hS]; ring
  rw [this]; exact h

/-- Stage pruning, free of `Greedy`. -/
theorem stage_prune_free (v : V4) (F : FlagData v) (k : ℕ) (x : Fin 4 → ℝ)
    (hv : Primitive v) (hx : StageWitness F k x) (hlt : ML v < 1 / 4) (c : ℝ)
    (hc : 1 / 4 ≤ c) (hfc : c ≤ fmin x) : 4 * (c - 1 / 4) ^ 2 < Sk F k := by
  have hb := stage_bound_free v F k x hv hx
  have hS := Sk_nonneg F k
  have h1 : 2 * (c - 1 / 4) < Real.sqrt (Sk F k) := by linarith
  have h2 : (2 * (c - 1 / 4)) ^ 2 < Real.sqrt (Sk F k) ^ 2 :=
    pow_lt_pow_left₀ h1 (by linarith) (by norm_num)
  rw [Real.sq_sqrt hS] at h2
  nlinarith

/-- For every primitive `v` with `ML v < 1/4` there is a flag all of whose stage tests hold. -/
theorem exists_flag_stage_prune (v : V4) (hv : Primitive v) (hlt : ML v < 1 / 4) :
    ∃ F : FlagData v, ∀ (k : ℕ) (x : Fin 4 → ℝ) (c : ℝ), StageWitness F k x → 1 / 4 ≤ c →
      c ≤ fmin x → 4 * (c - 1 / 4) ^ 2 < Sk F k := by
  obtain ⟨F⟩ := flagExistsBasis v hv
  exact ⟨F, fun k x c hx hc hfc => stage_prune_free v F k x hv hx hlt c hc hfc⟩

end L4S3
end LRSpectrumFull
