/-
# L4S4.Radius : the division-form radius test of the generator versus `NodeBound`, and the rational witness evaluator

The generator's `radius_bound(ms, inv, r, C, ks)` is `min` over the `k ∈ ks` with `den_k > 0` of `C / den_k`,
`den_k = 4 m_k² − ∑_{k<i<r} inv_i`, `inv_i = gs[i-1]/gs[i]`, `m_k = c_k − 1/4`, with exact fractions; `children`
accepts `t` iff `q · bd < bn · g` where `bn/bd` is that minimum and `μ² = q/g`.  The certificate checker computes
`c_k = witness_ok(l, x, w) = min_i ‖x_i / w‖` from the record `(x, w)`.

* Evaluator: `nd_rat` (`‖X/W‖ = min(X mod W, W − X mod W)/W`), `wMin`, `fmin_rat`, `WitnessOk`
  (= `witness_ok`: `W > 0` and `W ∣ h_i · X`, `i < k`), `stage_of_ok` (`WitnessOk → StageWitness` of the point `X/W`).
* Division form: `node_div_iff`, `int_lt_rat`, `accept_iff` : the integer comparison `q·bd < bn·g` with the fraction
  `bn/bd` of `radius_bound` is equivalent to `∀ k<d, 4 m_k² < S_k + C · (g/q)`, i.e. the node test of every stage.
* Bridge to the flag: `nodeRHS_rat` : `nodeRHS F d k` is the rational `ratRHS` in the leading Gram minors `G_i`
  (`G_{i-1}/G_i = inv_i = 1/μ_i²`), the numbers the generator keeps in `gs`.
* `nodeBound_to_rat` : `NodeBound F d` implies the checker's rational inequality at every checkable witness.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S4.Chain
import LRSpectrumFull.L4S3.Accepted

namespace LRSpectrumFull
namespace L4S4

open Finset LRSpectrumFull.L4S3

/-! ## evaluator -/

theorem fract_div_int (X W : ℤ) (hW : 0 < W) : Int.fract ((X : ℝ) / W) = ((X % W : ℤ) : ℝ) / W := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : (X : ℝ) = W * ((X / W : ℤ) : ℝ) + ((X % W : ℤ) : ℝ) := by
    exact_mod_cast (Int.mul_ediv_add_emod X W).symm
  have e : (X : ℝ) / W = ((X / W : ℤ) : ℝ) + ((X % W : ℤ) : ℝ) / W := by
    field_simp
    linarith
  rw [e, Int.fract_intCast_add]
  apply Int.fract_eq_self.2
  have h0 : (0 : ℤ) ≤ X % W := Int.emod_nonneg X hW.ne'
  have h2 : X % W < W := Int.emod_lt_of_pos X hW
  constructor
  · positivity
  · rw [div_lt_one hWr]; exact_mod_cast h2

theorem nd_rat (X W : ℤ) (hW : 0 < W) :
    nearestIntDist ((X : ℝ) / W) = ((min (X % W) (W - X % W) : ℤ) : ℝ) / W := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  unfold nearestIntDist
  rw [fract_div_int X W hW]
  push_cast
  rw [← min_div_div_right hWr.le]
  congr 1
  field_simp

/-- `min_i min(X_i mod W, W − X_i mod W)` (`witness_ok`'s `mn`). -/
def wMin (X : V4) (W : ℤ) : ℤ :=
  Finset.univ.inf' Finset.univ_nonempty (fun a => min (X a % W) (W - X a % W))

theorem fmin_rat (X : V4) (W : ℤ) (hW : 0 < W) :
    fmin (fun a => (X a : ℝ) / W) = (wMin X W : ℝ) / W := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  apply le_antisymm
  · obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin 4))
      (fun a => min (X a % W) (W - X a % W))
    have := fmin_le_nd (fun a => (X a : ℝ) / W) a
    rw [nd_rat _ _ hW] at this
    unfold wMin
    rw [ha]
    exact this
  · unfold fmin
    apply Finset.le_inf'
    intro a _
    simp only
    rw [nd_rat _ _ hW]
    apply div_le_div_of_nonneg_right _ hWr.le
    exact_mod_cast Finset.inf'_le (fun a => min (X a % W) (W - X a % W)) (Finset.mem_univ a)

/-- `witness_ok`: `W > 0` and `h_i · X ≡ 0 (mod W)` for the first `k` rows. -/
def WitnessOk {v : V4} (F : FlagData v) (k : ℕ) (X : V4) (W : ℤ) : Prop :=
  0 < W ∧ ∀ i : Fin 3, i.val < k → W ∣ dot (F.h i) X

theorem stage_of_ok {v : V4} (F : FlagData v) (k : ℕ) (X : V4) (W : ℤ) (h : WitnessOk F k X W) :
    StageWitness F k (fun a => (X a : ℝ) / W) := by
  intro i hi
  obtain ⟨m, hm⟩ := h.2 i hi
  have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast h.1.ne'
  refine ⟨m, ?_⟩
  have e : ∑ j, (F.h i j : ℝ) * ((X j : ℝ) / W) = ((dot (F.h i) X : ℤ) : ℝ) / W := by
    simp only [dot, Int.cast_sum, Int.cast_mul, Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [e, hm]
  push_cast
  field_simp

/-! ## bridge to the flag -/

/-- `C_d = ∑_{s<4-d} (4/3)^s` as a rational (`175/27, 37/9, 7/3, 1`). -/
def Cq (d : ℕ) : ℚ := ∑ s ∈ range (4 - d), (4 / 3 : ℚ) ^ s

/-- The right-hand side of the node test in the leading Gram minors `G`: `∑_{k ≤ i < d-1} G_i/G_{i+1} + C_d G_{d-1}/G_d`. -/
def ratRHS (G : ℕ → ℤ) (d k : ℕ) : ℚ :=
  (∑ i ∈ range (d - 1), if k ≤ i then (G i : ℚ) / (G (i + 1) : ℚ) else 0)
    + Cq d * ((G (d - 1) : ℚ) / (G d : ℚ))

theorem Dext_minors {v : V4} (F : FlagData v) (i : ℕ) (hi : i < 3) :
    Dext F i = (((leadMinor (gram F) (i + 1) : ℤ) : ℝ)) / ((leadMinor (gram F) i : ℤ) : ℝ) := by
  have h := Dext_lt F ⟨i, hi⟩
  simp only at h
  rw [h, Dq_minors_thm v F ⟨i, hi⟩]
  push_cast
  rfl

theorem nodeRHS_rat {v : V4} (F : FlagData v) (d k : ℕ) (hd1 : 1 ≤ d) (hd4 : d ≤ 3) :
    nodeRHS F d k = ((ratRHS (fun n => leadMinor (gram F) n) d k : ℚ) : ℝ) := by
  unfold nodeRHS ratRHS Cnode Cq
  push_cast
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_range.1 hi
    by_cases hk : k ≤ i
    · simp only [hk, if_true]
      rw [Dext_minors F i (by omega), one_div_div]
      simp
    · simp [hk]
  · rw [Dext_minors F (d - 1) (by omega), one_div_div]
    have : d - 1 + 1 = d := by omega
    rw [this]

/-- `NodeBound` at the checker's witness gives the checker's rational inequality: if `(X, W)` passes `witness_ok` for
stage `k < d` and `c = wMin/W ≥ 1/4`, then `4 (c − 1/4)² < ratRHS G d k` for `G` the leading Gram minors of the flag. -/
theorem nodeBound_to_rat {v : V4} (F : FlagData v) (d : ℕ) (hd1 : 1 ≤ d) (hd4 : d ≤ 3)
    (hNB : NodeBound F d) (k : ℕ) (hk : k < d) (X : V4) (W : ℤ) (hok : WitnessOk F k X W)
    (c : ℚ) (hcdef : c = ((wMin X W : ℤ) : ℚ) / ((W : ℤ) : ℚ)) (hc : (1 : ℚ) / 4 ≤ c) :
    4 * (c - 1 / 4) ^ 2 < ratRHS (fun n => leadMinor (gram F) n) d k := by
  have hW : (0 : ℝ) < W := by exact_mod_cast hok.1
  have hcast : ((c : ℚ) : ℝ) = (wMin X W : ℝ) / W := by rw [hcdef]; push_cast; ring
  have h := hNB k hk (fun a => (X a : ℝ) / W) ((c : ℚ) : ℝ)
    (stage_of_ok F k X W hok)
    (by have := (Rat.cast_le (K := ℝ)).2 hc; push_cast at this; exact this)
    (by rw [hcast, fmin_rat X W hok.1])
  rw [nodeRHS_rat F d k hd1 hd4] at h
  have h' : ((4 * (c - 1 / 4) ^ 2 : ℚ) : ℝ) < ((ratRHS (fun n => leadMinor (gram F) n) d k : ℚ) : ℝ) := by
    push_cast; exact h
  exact (Rat.cast_lt (K := ℝ)).1 h'

end L4S4
end LRSpectrumFull
