/-
# L4S3.GreedyFlip : row sign changes preserve `FlagData`, `Greedy` and `Accepted`

The generator keeps one of `±t` (first nonzero coordinate of `t` positive).  On the flag side this is the
freedom `h_i ↦ ε_i h_i`, `ε_i = ±1`: `FlagData.flip` changes the signs of the rows (and of the matching
columns of `R`, the matching entries of `Lq`), `greedy_flip` shows `Greedy` is unchanged, hence by
`accepted_of_greedy` so is `Accepted`.

* `exists_flag_accepted_signed : ∃ F0, Accepted F0 ∧ ∀ ε, (∀ i, ε i = 1 ∨ ε i = -1) → Accepted (F0.flip ε)`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.Accepted

namespace LRSpectrumFull
namespace L4S3

open Finset Matrix

/-- Change the sign of rows `i` with `ε i = -1`. -/
def FlagData.flip {v : V4} (F : FlagData v) (ε : Fin 3 → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    FlagData v where
  h := fun i k => ε i * F.h i k
  R := fun k j => ε j * F.R k j
  hv := fun i => by
    have := F.hv i
    simp only [dot] at this ⊢
    calc ∑ k, ε i * F.h i k * v k = ε i * ∑ k, F.h i k * v k := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
      _ = 0 := by rw [this]; ring
  hR := fun i j => by
    have h1 := F.hR i j
    have hi := hε i
    have hj := hε j
    calc ∑ k, ε i * F.h i k * (ε j * F.R k j) = (ε i * ε j) * ∑ k, F.h i k * F.R k j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
      _ = if i = j then 1 else 0 := by
          rw [h1]
          by_cases hij : i = j
          · subst hij; simp; rcases hi with h | h <;> rw [h] <;> norm_num
          · simp [hij]
  Lq := fun i k => (ε i : ℚ) * (ε k : ℚ) * F.Lq i k
  Dq := F.Dq
  hLunit := fun i => by
    have := F.hLunit i
    rw [this]; rcases hε i with h | h <;> rw [h] <;> norm_num
  hLlow := fun i j hij => by simp [F.hLlow i j hij]
  hDpos := F.hDpos
  hLDL := fun i j => by
    have h1 := F.hLDL i j
    have e : ((dot (fun k => ε i * F.h i k) (fun k => ε j * F.h j k) : ℤ) : ℚ)
        = (ε i : ℚ) * (ε j : ℚ) * ((dot (F.h i) (F.h j) : ℤ) : ℚ) := by
      simp only [dot]; push_cast
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
    rw [e, h1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hk := hε k
    have hk2 : (ε k : ℚ) * (ε k : ℚ) = 1 := by rcases hk with h | h <;> rw [h] <;> norm_num
    linear_combination (-(ε i : ℚ) * ε j * F.Lq i k * F.Dq k * F.Lq j k) * hk2

/-- Extension of the signs to `ℕ`. -/
def epsN (ε : Fin 3 → ℤ) (n : ℕ) : ℤ := if hn : n < 3 then ε ⟨n, hn⟩ else 1

theorem epsN_sq (ε : Fin 3 → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (n : ℕ) : epsN ε n * epsN ε n = 1 := by
  unfold epsN; split_ifs with hn
  · rcases hε ⟨n, hn⟩ with h | h <;> rw [h] <;> norm_num
  · norm_num

theorem hN_flip {v : V4} (F : FlagData v) (ε : Fin 3 → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (n : ℕ) :
    hN (F.flip ε hε).h n = fun k => epsN ε n * hN F.h n k := by
  funext k
  unfold hN epsN
  by_cases hn : n < 3
  · simp [hn, FlagData.flip]
  · simp [hn]

theorem inQN_flip {v : V4} (F : FlagData v) (ε : Fin 3 → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (j : ℕ) (u : V4) : InQN j (F.flip ε hε).h u ↔ InQN j F.h u := by
  have key : ∀ (a : ℕ → ℚ) (k : Fin 4), ∑ n ∈ range j, a n * (hN (F.flip ε hε).h n k : ℚ)
      = ∑ n ∈ range j, (a n * epsN ε n) * (hN F.h n k : ℚ) := by
    intro a k
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hN_flip]; push_cast; ring
  have key2 : ∀ (a : ℕ → ℚ) (k : Fin 4), ∑ n ∈ range j, a n * (hN F.h n k : ℚ)
      = ∑ n ∈ range j, (a n * epsN ε n) * (hN (F.flip ε hε).h n k : ℚ) := by
    intro a k
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hN_flip]; push_cast
    have := epsN_sq ε hε n
    have h3 : ((epsN ε n : ℤ) : ℚ) * (epsN ε n : ℚ) = 1 := by exact_mod_cast this
    calc a n * (hN F.h n k : ℚ) = a n * (hN F.h n k : ℚ) * ((epsN ε n : ℚ) * epsN ε n) := by rw [h3]; ring
      _ = _ := by ring
  constructor
  · rintro ⟨a, ha⟩; exact ⟨fun n => a n * epsN ε n, fun k => by rw [ha k, key]⟩
  · rintro ⟨a, ha⟩; exact ⟨fun n => a n * epsN ε n, fun k => by rw [ha k, key2]⟩

theorem gF_Ef_flip {v : V4} (F : FlagData v) (ε : Fin 3 → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (j : ℕ) (w : V4) : gF (Ef j (F.flip ε hε).h w) = gF (Ef j F.h w) := by
  have hq : ((gF (Ef j (F.flip ε hε).h w) : ℤ) : ℚ) = ((gF (Ef j F.h w) : ℤ) : ℚ) := by
    rw [gF_cast, gF_cast]
    set d : Fin (j + 1) → ℚ := fun r => if r.val < j then (epsN ε r.val : ℚ) else 1 with hd
    have hsh := GmQ_shear (fun i => castV (Ef j F.h w i)) (fun i => castV (Ef j (F.flip ε hε).h w i))
      (Matrix.diagonal d) (by
        intro r
        funext k
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        by_cases hr : r.val < j
        · simp [hd, hr, Ef, castV, hN_flip]
        · simp [hd, hr, Ef, castV])
    rw [hsh, Matrix.det_diagonal]
    have : (∏ i, d i) ^ 2 = 1 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_eq_one (fun i _ => ?_)
      by_cases hi : i.val < j
      · simp only [hd, hi, if_true]
        have := epsN_sq ε hε i.val
        have h3 : ((epsN ε i.val : ℤ) : ℚ) * (epsN ε i.val : ℚ) = 1 := by exact_mod_cast this
        rw [sq]; exact h3
      · simp [hd, hi]
    rw [this, one_mul]
  exact_mod_cast hq

theorem gF_Ef_sign {v : V4} (F : FlagData v) (j : ℕ) (w : V4) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    gF (Ef j F.h (fun k => s * w k)) = gF (Ef j F.h w) := by
  have h := gF_Ef_shear j F.h (fun k => s * w k) w (fun _ => 0) (s : ℚ) (fun k => by simp)
  have hq : ((gF (Ef j F.h (fun k => s * w k)) : ℤ) : ℚ) = ((gF (Ef j F.h w) : ℤ) : ℚ) := by
    rw [h]; rcases hs with h | h <;> rw [h] <;> norm_num
  exact_mod_cast hq

theorem greedy_flip {v : V4} (F : FlagData v) (hg : Greedy v F.h) (ε : Fin 3 → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) : Greedy v (F.flip ε hε).h := by
  intro j hj u hu hq
  have hq1 : ¬ InQN j (F.flip ε hε).h u := (inQSpanPrefix_iff _ j hj.le u).not.mp hq
  have hq2 : ¬ InQN j F.h u := (inQN_flip F ε hε j u).not.mp hq1
  have hq3 : ¬ InQSpanPrefix F.h j u := (inQSpanPrefix_iff _ j hj.le u).not.mpr hq2
  have hgl := hg j hj u hu hq3
  rw [take_succ_eq j hj, take_append_eq j hj.le, gramDetList_ofFn, gramDetList_ofFn] at hgl
  rw [take_succ_eq j hj, take_append_eq j hj.le, gramDetList_ofFn, gramDetList_ofFn,
    gF_Ef_flip F ε hε j u]
  have e : (FlagData.flip F ε hε).h ⟨j, hj⟩ = fun k => ε ⟨j, hj⟩ * F.h ⟨j, hj⟩ k := rfl
  rw [e, gF_Ef_flip F ε hε j, gF_Ef_sign F j _ _ (hε ⟨j, hj⟩)]
  exact hgl

theorem exists_flag_accepted_signed (v : V4) (hv : Primitive v) (hnz : ∀ i, v i ≠ 0)
    (hlt : ML v < 1 / 4) :
    ∃ F0 : FlagData v, Accepted F0 ∧
      ∀ (ε : Fin 3 → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1), Accepted (F0.flip ε hε) := by
  obtain ⟨F, hg⟩ := flag_exists v hv
  exact ⟨F, accepted_of_greedy F hv hnz hlt hg,
    fun ε hε => accepted_of_greedy _ hv hnz hlt (greedy_flip F hg ε hε)⟩

end L4S3
end LRSpectrumFull
