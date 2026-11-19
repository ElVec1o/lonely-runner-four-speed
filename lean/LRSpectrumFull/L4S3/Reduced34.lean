/-
# L4S3.Reduced34 : a flag with `μ²_{i+1} ≥ (3/4) μ²_i` exists for every primitive `v` (LLL potential)

`Reduced34 F : ∀ i : Fin 3, (3/4) Dq i ≤ Dq (i+1)` is exactly the conclusion of `ratio34_thm`, but WITHOUT
`Greedy`.  Its existence is proved by the classical LLL potential argument, on top of `FlagBasis`
(saturation is automatic for ANY `ℤ`-basis of `Λ`, so no greedy saturation argument is needed):

* `exists_change`: for an integer matrix `T` with integer right inverse `T'`, the rows `T H` form again a
  `FlagData v` (integer right inverse `R T'`, rational LDL by `ldl_of_indep`);
* `Phi F = G_1 G_2` (integer Gram minors of the prefixes, positive);
* `exists_step_lt`: if `4 Dq(i+1) < 3 Dq i`, size-reduce `h_{i+1} - c h_i` (`c = round Lq(i+1,i)`) and swap:
  the new flag has strictly smaller `Phi`;
* `exists_reduced34`: a flag minimising `Phi` (`Nat.find`) is `Reduced34`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.FlagBasis
import LRSpectrumFull.L4S3.Ratio34
import LRSpectrumFull.L4S3.Minors

namespace LRSpectrumFull
namespace L4S3

open Finset Matrix

/-- The `(3/4)`-ratio condition on the LDL diagonal (the conclusion of `ratio34_thm`, no `Greedy`). -/
def Reduced34 {v : V4} (F : FlagData v) : Prop :=
  ∀ i : Fin 2, (3 / 4 : ℚ) * F.Dq i.castSucc ≤ F.Dq i.succ

/-- Change of basis by an integer matrix `T` with integer right inverse `T'`. -/
theorem exists_change {v : V4} (F : FlagData v) (T T' : Matrix (Fin 3) (Fin 3) ℤ)
    (hTT' : T * T' = 1) :
    ∃ F' : FlagData v, ∀ a k, F'.h a k = ∑ b, T a b * F.h b k := by
  set Hm : Matrix (Fin 3) (Fin 4) ℤ := Matrix.of F.h with hHm
  set Rm : Matrix (Fin 4) (Fin 3) ℤ := Matrix.of F.R with hRm
  have hHR : Hm * Rm = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [hHm, hRm] using F.hR i j
  let h' : Fin 3 → V4 := fun a k => (T * Hm) a k
  let R' : Fin 4 → Fin 3 → ℤ := fun k j => (Rm * T') k j
  have hv' : ∀ a, dot (h' a) v = 0 := by
    intro a
    have : dot (h' a) v = ∑ b, T a b * dot (F.h b) v := by
      simp only [dot, h', Matrix.mul_apply, hHm, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum,
        mul_assoc]
      rw [Finset.sum_comm]
    rw [this]; simp [F.hv]
  have hR' : ∀ i j : Fin 3, ∑ k : Fin 4, h' i k * R' k j = if i = j then 1 else 0 := by
    intro i j
    have e : (T * Hm) * (Rm * T') = 1 := by
      calc (T * Hm) * (Rm * T') = T * (Hm * Rm) * T' := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc Hm Rm T', ← Matrix.mul_assoc]
        _ = 1 := by rw [hHR, Matrix.mul_one, hTT']
    have := congr_fun (congr_fun e i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [h', R'] using this
  have hTTq : ∀ a a' : Fin 3, ∑ b, (T a b : ℚ) * (T' b a') = if a = a' then 1 else 0 := by
    intro a a'
    have := congr_fun (congr_fun hTT' a) a'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    have h2 := congr_arg (fun z : ℤ => (z : ℚ)) this
    simpa using h2
  have hind : ∀ c : Fin 3 → ℚ, ∑ a, c a • castV (h' a) = 0 → ∀ a, c a = 0 := by
    intro c hc
    have hrows : ∀ k : Fin 4, ∑ b, (∑ a, c a * (T a b : ℚ)) * (F.h b k : ℚ) = 0 := by
      intro k
      have h0 := congr_fun hc k
      simp only [Finset.sum_apply, Pi.smul_apply, castV, smul_eq_mul, Pi.zero_apply] at h0
      have e : ∑ b, (∑ a, c a * (T a b : ℚ)) * (F.h b k : ℚ)
          = ∑ a, c a * ((h' a k : ℤ) : ℚ) := by
        simp only [h', Matrix.mul_apply, hHm, Matrix.of_apply]
        push_cast
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; ring
      rw [e]; exact h0
    have hb := rows_indep F (fun b => ∑ a, c a * (T a b : ℚ)) hrows
    intro a
    have h1 : ∑ b, (∑ a', c a' * (T a' b : ℚ)) * (T' b a : ℚ)
        = ∑ a', c a' * ∑ b, (T a' b : ℚ) * (T' b a : ℚ) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply sum_congr rfl; intro a' _; apply sum_congr rfl; intro b _; ring
    have h2 : ∑ a', c a' * ∑ b, (T a' b : ℚ) * (T' b a : ℚ) = c a := by
      simp [hTTq]
    rw [← h2, ← h1]
    simp [hb]
  obtain ⟨Lq, Dq, hL1, hL0, hD, hG⟩ := ldl_of_indep h' hind
  exact ⟨⟨h', R', hv', hR', Lq, Dq, hL1, hL0, hD, hG⟩, fun a k => by
    show (T * Hm) a k = _
    simp [Matrix.mul_apply, hHm]⟩

/-- The LLL potential: product of the integer prefix Gram determinants `G_1 G_2` (`G_3 = |v|²` is
constant, so it is not part of the potential). -/
def Phi {v : V4} (F : FlagData v) : ℤ :=
  gramDetList [F.h 0] * gramDetList [F.h 0, F.h 1]

theorem gd_all {v : V4} (F : FlagData v) :
    ((gramDetList [F.h 0] : ℤ) : ℚ) = F.Dq 0 ∧
    ((gramDetList [F.h 0, F.h 1] : ℤ) : ℚ) = F.Dq 0 * F.Dq 1 := by
  have l01 : F.Lq 0 1 = 0 := F.hLlow 0 1 (by decide)
  have l02 : F.Lq 0 2 = 0 := F.hLlow 0 2 (by decide)
  have l12 : F.Lq 1 2 = 0 := F.hLlow 1 2 (by decide)
  have u0 := F.hLunit 0
  have u1 := F.hLunit 1
  have u2 := F.hLunit 2
  refine ⟨?_, ?_⟩
  · rw [gdl1]
    simp only [dotq_exp, Fin.sum_univ_three, l01, l02, l12, u0, u1, u2]
    ring
  · rw [gdl2]; push_cast
    simp only [dotq_exp, Fin.sum_univ_three, l01, l02, l12, u0, u1, u2]
    ring

theorem Phi_pos {v : V4} (F : FlagData v) : 0 < Phi F := by
  obtain ⟨h1, h2⟩ := gd_all F
  have d0 := F.hDpos 0
  have d1 := F.hDpos 1
  have hq : (0 : ℚ) < (Phi F : ℚ) := by
    unfold Phi
    push_cast
    rw [h1, h2]
    positivity
  exact_mod_cast hq

set_option maxHeartbeats 1600000 in
/-- One LLL step: if `4 Dq(i+1) < 3 Dq i`, there is a flag with strictly smaller potential. -/
theorem exists_step_lt {v : V4} (F : FlagData v) (i : Fin 2)
    (hi : F.Dq i.succ < (3 / 4 : ℚ) * F.Dq i.castSucc) : ∃ F' : FlagData v, Phi F' < Phi F := by
  obtain ⟨h1, h2⟩ := gd_all F
  have l01 : F.Lq 0 1 = 0 := F.hLlow 0 1 (by decide)
  have l02 : F.Lq 0 2 = 0 := F.hLlow 0 2 (by decide)
  have l12 : F.Lq 1 2 = 0 := F.hLlow 1 2 (by decide)
  have u0 := F.hLunit 0
  have u1 := F.hLunit 1
  have u2 := F.hLunit 2
  have d0 := F.hDpos 0
  have d1 := F.hDpos 1
  have d2 := F.hDpos 2
  have hPhi : ((Phi F : ℤ) : ℚ) = F.Dq 0 * (F.Dq 0 * F.Dq 1) := by
    unfold Phi; push_cast; rw [h1, h2]
  fin_cases i
  · -- i = 0
    set c : ℤ := round (F.Lq 1 0) with hc
    have hcb : (F.Lq 1 0 - c) ^ 2 ≤ 1 / 4 := round_bd _
    have hT : (!![-c, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ) *
        !![0, 1, 0; 1, c, 0; 0, 0, 1] = 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
    obtain ⟨F', hF'⟩ := exists_change F _ _ hT
    have e0 : F'.h 0 = fun k => F.h 1 k - c * F.h 0 k := by
      funext k; simp [hF', Fin.sum_univ_three]; ring
    have e1 : F'.h 1 = F.h 0 := by funext k; simp [hF', Fin.sum_univ_three]
    refine ⟨F', ?_⟩
    have hB1 : ((gramDetList [F'.h 0] : ℤ) : ℚ) = F.Dq 1 + (F.Lq 1 0 - c) ^ 2 * F.Dq 0 := by
      rw [e0, gdl1]; simp only [dot_sub_smul, dot_sub_smul']; push_cast
      simp only [dotq_exp, Fin.sum_univ_three, l01, l02, l12, u0, u1, u2]
      ring
    have hB2 : ((gramDetList [F'.h 0, F'.h 1] : ℤ) : ℚ) = F.Dq 0 * F.Dq 1 := by
      rw [e0, e1, gdl2]; simp only [dot_sub_smul, dot_sub_smul']; push_cast
      simp only [dotq_exp, Fin.sum_univ_three, l01, l02, l12, u0, u1, u2]
      ring
    have hPhi' : ((Phi F' : ℤ) : ℚ) = (F.Dq 1 + (F.Lq 1 0 - c) ^ 2 * F.Dq 0) *
        (F.Dq 0 * F.Dq 1) := by
      unfold Phi; push_cast; rw [hB1, hB2]
    have hQ : (0 : ℚ) < F.Dq 0 * F.Dq 1 := by positivity
    have hX : F.Dq 1 + (F.Lq 1 0 - c) ^ 2 * F.Dq 0 < F.Dq 0 := by
      have hi' : F.Dq 1 < 3 / 4 * F.Dq 0 := hi
      have hs := mul_le_mul_of_nonneg_right hcb d0.le; linarith
    have : ((Phi F' : ℤ) : ℚ) < ((Phi F : ℤ) : ℚ) := by
      rw [hPhi', hPhi]
      have := mul_lt_mul_of_pos_right hX hQ
      linarith [this]
    exact_mod_cast this
  · -- i = 1
    set c : ℤ := round (F.Lq 2 1) with hc
    have hcb : (F.Lq 2 1 - c) ^ 2 ≤ 1 / 4 := round_bd _
    have hT : (!![1, 0, 0; 0, -c, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℤ) *
        !![1, 0, 0; 0, 0, 1; 0, 1, c] = 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
    obtain ⟨F', hF'⟩ := exists_change F _ _ hT
    have e0 : F'.h 0 = F.h 0 := by funext k; simp [hF', Fin.sum_univ_three]
    have e1 : F'.h 1 = fun k => F.h 2 k - c * F.h 1 k := by
      funext k; simp [hF', Fin.sum_univ_three]; ring
    refine ⟨F', ?_⟩
    have hB1 : ((gramDetList [F'.h 0] : ℤ) : ℚ) = F.Dq 0 := by rw [e0]; exact h1
    have hB2 : ((gramDetList [F'.h 0, F'.h 1] : ℤ) : ℚ)
        = F.Dq 0 * (F.Dq 2 + (F.Lq 2 1 - c) ^ 2 * F.Dq 1) := by
      rw [e0, e1, gdl2]; simp only [dot_sub_smul, dot_sub_smul']; push_cast
      simp only [dotq_exp, Fin.sum_univ_three, l01, l02, l12, u0, u1, u2]
      ring
    have hPhi' : ((Phi F' : ℤ) : ℚ) = (F.Dq 2 + (F.Lq 2 1 - c) ^ 2 * F.Dq 1) *
        (F.Dq 0 * F.Dq 0) := by
      unfold Phi; push_cast; rw [hB1, hB2]; ring
    have hPhi2 : ((Phi F : ℤ) : ℚ) = F.Dq 1 * (F.Dq 0 * F.Dq 0) := by
      rw [hPhi]; ring
    have hQ : (0 : ℚ) < F.Dq 0 * F.Dq 0 := by positivity
    have hX : F.Dq 2 + (F.Lq 2 1 - c) ^ 2 * F.Dq 1 < F.Dq 1 := by
      have hi' : F.Dq 2 < 3 / 4 * F.Dq 1 := hi
      have hs := mul_le_mul_of_nonneg_right hcb d1.le; linarith
    have : ((Phi F' : ℤ) : ℚ) < ((Phi F : ℤ) : ℚ) := by
      rw [hPhi', hPhi2]
      exact mul_lt_mul_of_pos_right hX hQ
    exact_mod_cast this

/-- LLL: every primitive `v` has a flag satisfying the `3/4` ratios, with no greedy hypothesis. -/
theorem exists_reduced34 (v : V4) (hv : Primitive v) : ∃ F : FlagData v, Reduced34 F := by
  obtain ⟨F0⟩ := flagExistsBasis v hv
  have hex : ∃ n : ℕ, ∃ F : FlagData v, (Phi F).toNat = n := ⟨_, F0, rfl⟩
  classical
  obtain ⟨F1, hF1⟩ := Nat.find_spec hex
  refine ⟨F1, fun i => ?_⟩
  by_contra hlt
  push_neg at hlt
  obtain ⟨F', hlt'⟩ := exists_step_lt F1 i hlt
  have hmin := Nat.find_min' hex (⟨F', rfl⟩ : ∃ F : FlagData v, (Phi F).toNat = (Phi F').toNat)
  have hlt2 : (Phi F').toNat < (Phi F1).toNat := (Int.toNat_lt_toNat (Phi_pos F1)).mpr hlt'
  omega

/-- The whole flag chain for every primitive `v`, without `Greedy`, without any hypothesis: a flag with
the `3/4` ratios (tests (ii), (iii) lower window), the covolume identity, `Dq` as ratios of integer Gram
minors, and the stage bound (test (i)) for every stage witness. -/
theorem flag_chain_unconditional (v : V4) (hv : Primitive v) :
    ∃ F : FlagData v, Reduced34 F ∧ (∏ i, F.Dq i) = (dot v v : ℚ) ∧
      (∀ i : Fin 3, F.Dq i = (leadMinor (gram F) (i.val + 1) : ℚ) / (leadMinor (gram F) i.val : ℚ)) ∧
      (∀ (k : ℕ) (x : Fin 4 → ℝ), StageWitness F k x →
        fmin x - 1 / 2 * Real.sqrt (Sk F k) ≤ ML v) := by
  obtain ⟨F, hF⟩ := exists_reduced34 v hv
  exact ⟨F, hF, covolume_thm v F hv, fun i => Dq_minors_thm v F i,
    fun k x hx => stage_bound_free v F k x hv hx⟩

end L4S3
end LRSpectrumFull
