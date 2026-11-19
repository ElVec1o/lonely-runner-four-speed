/-
# L4S3.GreedyFinal : `GreedyBasis v` for every primitive `v`, hence `FlagExists`

Assembly of `GreedyStep.inv_step`: four steps give `InvN v 3 h`, which unpacks into
(i) `h_i ∈ Λ`, (ii) `ℤ`-independence, (iii) `ℤ`-span of `Λ` (saturation + `dim_span`),
(iv) `Greedy v h` (bridge `take_append_eq`, `take_succ_eq`, `gramDetList_ofFn`).

* `greedyBasis_exists (v) (hv : Primitive v) : GreedyBasis v`
* `flag_exists : FlagExists`
* `flag_greedy_unconditional : FlagGeometry`

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.GreedyStep

namespace LRSpectrumFull
namespace L4S3

open Finset

theorem invN_exists (v : V4) (hv : Primitive v) : ∀ j : ℕ, j ≤ 3 → ∃ h : Fin 3 → V4, InvN v j h := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun _ _ => 0, ?_, ?_, ?_, ?_⟩
    · intro n hn; omega
    · intro a _ n hn; omega
    · intro x _ hx
      exact ⟨fun _ => 0, fun k => by
        obtain ⟨a, ha⟩ := hx
        simpa using ha k⟩
    · intro i hi; omega
  | succ j ih =>
    intro hj
    obtain ⟨h, hh⟩ := ih (by omega)
    obtain ⟨h', _, hh'⟩ := inv_step v hv j (by omega) h hh
    exact ⟨h', hh'⟩

theorem greedyBasis_exists (v : V4) (hv : Primitive v) : GreedyBasis v := by
  obtain ⟨h, hP, hI, hS, hG⟩ := invN_exists v hv 3 le_rfl
  have hPi : ∀ i : Fin 3, dot (h i) v = 0 := fun i => by
    have := hP i.val i.2; rwa [hN_lt] at this
  refine ⟨h, hPi, ?_, ?_, ?_⟩
  · refine Fintype.linearIndependent_iff.2 (fun g hg i => ?_)
    have hz := hI (fun n => if hn : n < 3 then (g ⟨n, hn⟩ : ℚ) else 0) (fun k => by
      have h3 := congr_fun hg k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h3
      have h4 : ((∑ i : Fin 3, g i * h i k : ℤ) : ℚ) = 0 := by rw [h3]; simp
      push_cast at h4
      rw [← h4, Finset.sum_range]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      simp [hN_lt, n.2]) i.val i.2
    have : (g i : ℚ) = 0 := by simpa [i.2] using hz
    exact_mod_cast this
  · intro x hx
    have hq := dim_span v hv h (fun n hn => by
      have := hP n hn; exact this) hI x hx
    obtain ⟨m, hm⟩ := hS x hx hq
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun i => m i.val, ?_⟩
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hm k, Finset.sum_range]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp [hN_lt]
  · intro j hj u hu hq
    have hq' : ¬ InQN j h u := (inQSpanPrefix_iff h j hj.le u).not.mp hq
    have := hG j hj u hu hq'
    rw [take_succ_eq j hj, take_append_eq j hj.le, gramDetList_ofFn, gramDetList_ofFn]
    have e : hN h j = h ⟨j, hj⟩ := by simp [hN, hj]
    rw [e] at this
    exact this

theorem flag_exists : FlagExists :=
  flagExists_of_greedyBasis greedyBasis_exists

theorem flag_greedy_unconditional : FlagGeometry :=
  flagGeometry_of_greedyBasis greedyBasis_exists

end L4S3
end LRSpectrumFull
