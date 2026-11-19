/-
# L4S4.Chain : the flag data depend only on the chain of lattices

Two flags `F`, `F'` of the
same `v` have the same chain at level `k` (`SameChain F F' k`) when the first `k` rows of each lie in the
`ℤ`-span of the first `k` rows of the other.  Then, with no further hypothesis:

* `stage_iff`      : `StageWitness F k x ↔ StageWitness F' k x`;
* `leadMinor_chain`: `leadMinor (gram F') k = leadMinor (gram F) k`  (`G_k` is an invariant of `L_k`);
* `chain_invariants`: `Dq`, `Sk`, `Mlat` agree when the chains agree at every level;
* `sameChain_of_tri`: a lower-triangular integer change of basis with an integer (lower-triangular) inverse
  (the unitriangular-with-signs change of `exists_change` / `FlagData.flip`) preserves the chain;
* `leadMinor_eq_gF`: `leadMinor (gram F) j` is the Gram determinant of the first `j` rows (`j ≤ 3`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.Minors
import LRSpectrumFull.L4S3.Ratio34
import LRSpectrumFull.L4S3.GramQ
import LRSpectrumFull.L4S3.Skeleton
import Mathlib.Data.Matrix.Block

namespace LRSpectrumFull
namespace L4S4

open Matrix Finset LRSpectrumFull.L4S3

/-- `x` lies in the `ℤ`-span of the first `k` rows of `F`. -/
def LatN {v : V4} (F : FlagData v) (k : ℕ) (x : V4) : Prop :=
  ∃ c : ℕ → ℤ, ∀ a : Fin 4, x a = ∑ m ∈ range k, c m * hN F.h m a

/-- The lattice chains of `F` and `F'` agree at level `k`. -/
def SameChain {v : V4} (F F' : FlagData v) (k : ℕ) : Prop :=
  (∀ i < k, LatN F k (hN F'.h i)) ∧ (∀ i < k, LatN F' k (hN F.h i))

theorem SameChain.symm {v : V4} {F F' : FlagData v} {k : ℕ} (h : SameChain F F' k) :
    SameChain F' F k := ⟨h.2, h.1⟩

/-! ## Stage witnesses -/

theorem stage_of_lat {v : V4} (F F' : FlagData v) (k : ℕ) (hk : k ≤ 3)
    (hc : ∀ i < k, LatN F k (hN F'.h i)) (x : Fin 4 → ℝ) (hx : StageWitness F k x) :
    StageWitness F' k x := by
  intro i hi
  obtain ⟨c, hc⟩ := hc i.val hi
  have hm : ∀ m ∈ range k, ∃ n : ℤ, ∑ a, (hN F.h m a : ℝ) * x a = n := by
    intro m hm
    have hm' := mem_range.1 hm
    have := hx ⟨m, by omega⟩ hm'
    simpa [hN, show m < 3 by omega] using this
  choose! n hn using hm
  refine ⟨∑ m ∈ range k, c m * n m, ?_⟩
  have e1 : ∑ a, (F'.h i a : ℝ) * x a = ∑ a, (hN F'.h i.val a : ℝ) * x a := by
    simp [hN, i.2]
  rw [e1]
  have e2 : ∀ a, (hN F'.h i.val a : ℝ) = ∑ m ∈ range k, (c m : ℝ) * (hN F.h m a : ℝ) := by
    intro a
    have := hc a
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) this
    simpa using h2
  simp only [e2, Finset.sum_mul]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have := hn m hm
  calc ∑ a, (c m : ℝ) * (hN F.h m a : ℝ) * x a
      = (c m : ℝ) * ∑ a, (hN F.h m a : ℝ) * x a := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
    _ = (c m : ℝ) * (n m : ℝ) := by rw [this]

theorem stage_iff {v : V4} (F F' : FlagData v) (k : ℕ) (hk : k ≤ 3) (h : SameChain F F' k)
    (x : Fin 4 → ℝ) : StageWitness F k x ↔ StageWitness F' k x :=
  ⟨stage_of_lat F F' k hk h.1 x, stage_of_lat F' F k hk h.2 x⟩

/-! ## Gram minors -/

theorem leadMinor_eq_gF {v : V4} (F : FlagData v) (j : ℕ) (hj : j ≤ 3) :
    leadMinor (gram F) j = gF (fun i : Fin j => hN F.h i.val) := by
  set σ : Fin j ⊕ Fin (3 - j) ≃ Fin 3 := finSumFinEquiv.trans (finCongr (by omega)) with hσ
  unfold leadMinor
  rw [← Matrix.det_submatrix_equiv_self σ]
  have hv : ∀ a : Fin j, (σ (Sum.inl a)).val = a.val := by
    intro a; simp [hσ]
  have hw : ∀ b : Fin (3 - j), (σ (Sum.inr b)).val = j + b.val := by
    intro b; simp [hσ]
  have hfb : (Matrix.of fun a b : Fin 3 =>
        if a.val < j ∧ b.val < j then gram F a b else if a = b then 1 else 0).submatrix σ σ
      = fromBlocks (Matrix.of fun a b : Fin j => dot (hN F.h a.val) (hN F.h b.val)) 0 0 1 := by
    ext (a | a) (b | b)
    · have h1 := hv a
      have h2 := hv b
      have h1' : σ (Sum.inl a) = ⟨a.val, by omega⟩ := Fin.ext h1
      have h2' : σ (Sum.inl b) = ⟨b.val, by omega⟩ := Fin.ext h2
      simp only [Matrix.submatrix_apply, Matrix.of_apply, fromBlocks_apply₁₁, h1, h2, a.2, b.2,
        and_self, if_true, h1', h2']
      simp [gram, hN, show a.val < 3 by omega, show b.val < 3 by omega]
    · have h1 := hv a
      have h2 := hw b
      have : ¬ (σ (Sum.inl a) = σ (Sum.inr b)) := by
        intro h; have := congrArg Fin.val h; rw [h1, h2] at this; omega
      simp only [Matrix.submatrix_apply, Matrix.of_apply, fromBlocks_apply₁₂, h1, h2, this]
      simp
    · have h1 := hw a
      have h2 := hv b
      have : ¬ (σ (Sum.inr a) = σ (Sum.inl b)) := by
        intro h; have := congrArg Fin.val h; rw [h1, h2] at this; omega
      simp only [Matrix.submatrix_apply, Matrix.of_apply, fromBlocks_apply₂₁, h1, h2, this]
      simp
    · have h1 := hw a
      have h2 := hw b
      simp only [Matrix.submatrix_apply, Matrix.of_apply, fromBlocks_apply₂₂, h1, h2]
      by_cases hab : a = b
      · subst hab; simp
      · have : ¬ (σ (Sum.inr a) = σ (Sum.inr b)) := by
          intro h; apply hab
          have := congrArg Fin.val h; rw [h1, h2] at this
          exact Fin.ext (by omega)
        simp [this, hab]
  rw [hfb, det_fromBlocks_zero₁₂]
  simp [gF]

theorem leadMinor_pos' {v : V4} (F : FlagData v) (j : ℕ) : 0 < leadMinor (gram F) j := by
  have h := prod_pos_aux F j
  rw [← leadMinor_cast_prod F j] at h
  exact_mod_cast h

/-- Shear: `f' = T f` on `Fin j` families gives `gF f' = (det T)² gF f`. -/
theorem gF_shear {j : ℕ} (f f' : Fin j → V4) (T : Matrix (Fin j) (Fin j) ℤ)
    (h : ∀ a c, f' a c = ∑ m, T a m * f m c) : gF f' = T.det ^ 2 * gF f := by
  have hq := GmQ_shear (fun a => castV (f a)) (fun a => castV (f' a))
    (T.map (Int.castRingHom ℚ)) (by
      intro r; funext c
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castV]
      have := congrArg (fun z : ℤ => (z : ℚ)) (h r c)
      simpa using this)
  have hdet : ((T.map (Int.castRingHom ℚ)).det) = (T.det : ℚ) := by
    have := RingHom.map_det (Int.castRingHom ℚ) T
    simpa [RingHom.mapMatrix_apply] using this.symm
  rw [hdet, ← gF_cast, ← gF_cast] at hq
  exact_mod_cast hq

/-- Coefficient matrix from `LatN` memberships. -/
theorem coeff_matrix {v : V4} (F F' : FlagData v) (j : ℕ)
    (hc : ∀ i < j, LatN F j (hN F'.h i)) :
    ∃ T : Matrix (Fin j) (Fin j) ℤ, ∀ (a : Fin j) (c : Fin 4),
      hN F'.h a.val c = ∑ m : Fin j, T a m * hN F.h m.val c := by
  choose! cc hcc using hc
  refine ⟨Matrix.of fun a m => cc a.val m.val, fun a c => ?_⟩
  simp only [Matrix.of_apply]
  rw [hcc a.val a.2 c, Fin.sum_univ_eq_sum_range (fun m => cc a.val m * hN F.h m c) j]

theorem leadMinor_chain {v : V4} (F F' : FlagData v) (j : ℕ) (hj : j ≤ 3)
    (h : SameChain F F' j) : leadMinor (gram F') j = leadMinor (gram F) j := by
  rw [leadMinor_eq_gF F' j hj, leadMinor_eq_gF F j hj]
  obtain ⟨T, hT⟩ := coeff_matrix F F' j h.1
  obtain ⟨T', hT'⟩ := coeff_matrix F' F j h.2
  have e1 := gF_shear (fun i : Fin j => hN F.h i.val) (fun i : Fin j => hN F'.h i.val) T hT
  have e2 := gF_shear (fun i : Fin j => hN F'.h i.val) (fun i : Fin j => hN F.h i.val) T' hT'
  have hpos : 0 < gF (fun i : Fin j => hN F'.h i.val) := by
    rw [← leadMinor_eq_gF F' j hj]; exact leadMinor_pos' F' j
  have hprod : T.det ^ 2 * T'.det ^ 2 = 1 := by
    have : gF (fun i : Fin j => hN F'.h i.val) =
        T.det ^ 2 * T'.det ^ 2 * gF (fun i : Fin j => hN F'.h i.val) := by
      have h0 := e1
      rw [e2] at h0
      linarith
    have h2 : (T.det ^ 2 * T'.det ^ 2 - 1) * gF (fun i : Fin j => hN F'.h i.val) = 0 := by
      linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · linarith
    · exact absurd h3 (ne_of_gt hpos)
  have hT2 : T.det ^ 2 = 1 := by
    have h0 : 0 ≤ T.det ^ 2 := sq_nonneg _
    have h0' : 0 ≤ T'.det ^ 2 := sq_nonneg _
    exact Int.eq_one_of_mul_eq_one_right h0 hprod
  rw [e1, hT2, one_mul]

/-- Chain agreement at every level `0..4`. -/
theorem Dq_chain {v : V4} (F F' : FlagData v) (h : ∀ k ≤ 3, SameChain F F' k) (i : Fin 3) :
    F'.Dq i = F.Dq i := by
  rw [Dq_minors_thm v F' i, Dq_minors_thm v F i,
    leadMinor_chain F F' (i.val + 1) (by omega) (h _ (by omega)),
    leadMinor_chain F F' i.val (by omega) (h _ (by omega))]

theorem Sk_chain {v : V4} (F F' : FlagData v) (h : ∀ k ≤ 3, SameChain F F' k) (k : ℕ) :
    Sk F' k = Sk F k := by
  unfold Sk
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Dq_chain F F' h i]

theorem Mlat_chain {v : V4} (F F' : FlagData v) (k : ℕ) (hk : k ≤ 3) (h : SameChain F F' k) :
    Mlat F' k = Mlat F k := by
  unfold Mlat
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, (stage_iff F F' k hk h x).2 hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, (stage_iff F F' k hk h x).1 hx, rfl⟩

theorem chain_invariants {v : V4} (F F' : FlagData v) (h : ∀ k ≤ 3, SameChain F F' k) :
    (∀ k ≤ 3, leadMinor (gram F') k = leadMinor (gram F) k) ∧
    (∀ i : Fin 3, F'.Dq i = F.Dq i) ∧ (∀ k, Sk F' k = Sk F k) ∧
    (∀ k ≤ 3, ∀ x, StageWitness F k x ↔ StageWitness F' k x) ∧
    (∀ k ≤ 3, Mlat F' k = Mlat F k) :=
  ⟨fun k hk => leadMinor_chain F F' k hk (h k hk), Dq_chain F F' h, Sk_chain F F' h,
    fun k hk x => stage_iff F F' k hk (h k hk) x, fun k hk => Mlat_chain F F' k hk (h k hk)⟩

/-! ## Triangular changes of basis preserve the chain -/

theorem LatN.mono {v : V4} {F : FlagData v} {k k' : ℕ} (hk : k ≤ k') {x : V4}
    (h : LatN F k x) : LatN F k' x := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun m => if m < k then c m else 0, fun a => ?_⟩
  rw [hc a]
  have : ∑ m ∈ range k', (if m < k then c m else 0) * hN F.h m a
      = ∑ m ∈ range k, (if m < k then c m else 0) * hN F.h m a := by
    symm
    apply Finset.sum_subset (range_mono hk)
    intro m hm hm'
    have : ¬ m < k := fun h => hm' (mem_range.2 h)
    simp [this]
  rw [this]
  exact Finset.sum_congr rfl (fun m hm => by simp [mem_range.1 hm])

theorem tri_sum {v : V4} (F : FlagData v) (T : Matrix (Fin 3) (Fin 3) ℤ)
    (hT : ∀ a m, a < m → T a m = 0) (i : ℕ) (hi : i < 3) (k : ℕ) (hik : i < k) (hk : k ≤ 3)
    (a : Fin 4) :
    ∑ b : Fin 3, T ⟨i, hi⟩ b * F.h b a
      = ∑ m ∈ range k, (if hm : m < 3 then T ⟨i, hi⟩ ⟨m, hm⟩ else 0) * hN F.h m a := by
  have e1 : ∑ b : Fin 3, T ⟨i, hi⟩ b * F.h b a
      = ∑ m ∈ range 3, (if hm : m < 3 then T ⟨i, hi⟩ ⟨m, hm⟩ else 0) * hN F.h m a := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => (if hm : m < 3 then T ⟨i, hi⟩ ⟨m, hm⟩ else 0) *
      hN F.h m a) 3]
    exact Finset.sum_congr rfl (fun b _ => by simp [hN, b.2])
  rw [e1]
  symm
  apply Finset.sum_subset (range_mono hk)
  intro m hm hm'
  have hm4 : m < 3 := mem_range.1 hm
  have hmk : ¬ m < k := fun h => hm' (mem_range.2 h)
  have : T ⟨i, hi⟩ ⟨m, hm4⟩ = 0 := hT _ _ (by show i < m; omega)
  simp [hm4, this]

/-- A lower-triangular integer change of basis with an integer lower-triangular inverse preserves the chain
(covers the unitriangular changes with row signs of `exists_change` and `FlagData.flip`). -/
theorem sameChain_of_tri {v : V4} (F F' : FlagData v) (T T' : Matrix (Fin 3) (Fin 3) ℤ)
    (hTT' : T * T' = 1) (hT : ∀ a m, a < m → T a m = 0) (hT' : ∀ a m, a < m → T' a m = 0)
    (hrow : ∀ a k, F'.h a k = ∑ b, T a b * F.h b k) (k : ℕ) (hk : k ≤ 3) :
    SameChain F F' k := by
  have hT'T : T' * T = 1 := mul_eq_one_comm.1 hTT'
  have hrow' : ∀ a k, F.h a k = ∑ b, T' a b * F'.h b k := by
    intro a c
    have h1 : ∑ b, T' a b * F'.h b c = ∑ b, T' a b * ∑ m, T b m * F.h m c := by
      refine Finset.sum_congr rfl (fun b _ => by rw [hrow b c])
    rw [h1]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ m, ∑ b, T' a b * (T b m * F.h m c) = (T' * T) a m * F.h m c := by
      intro m; rw [Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    simp only [h2, hT'T, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    simp
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hi4 : i < 3 := by omega
    refine ⟨fun m => if hm : m < 3 then T ⟨i, hi4⟩ ⟨m, hm⟩ else 0, fun a => ?_⟩
    rw [← tri_sum F T hT i hi4 k hi hk a]
    simp [hN, hi4, hrow]
  · have hi4 : i < 3 := by omega
    refine ⟨fun m => if hm : m < 3 then T' ⟨i, hi4⟩ ⟨m, hm⟩ else 0, fun a => ?_⟩
    rw [← tri_sum F' T' hT' i hi4 k hi hk a]
    simp [hN, hi4, hrow']

end L4S4
end LRSpectrumFull
