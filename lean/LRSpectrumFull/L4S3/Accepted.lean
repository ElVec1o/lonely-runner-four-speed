/-
# L4S3.Accepted : a flag of every near-tight `v` accepted by every filter of the four-speed tree

The generator (`lean5_wp0a`: `children`, `greedy_ok`, `ei_bad`, `radius_bound`, `d1_list`) keeps a child
`t` of a node (new row `h_d`, new lattice `L_d = ℤ h_0 + … + ℤ h_{d-1}`, `d = 1, 2`, and the leaf level `d = 3`) iff

  (a) `t` is primitive in `ℤ^{4-d+1}`              <->  `L_d` saturated in `ℤ⁴`            : `PrimChild`
  (b) first nonzero coordinate of `t` positive       <->  sign of `h_{d-1}`                   : `flip` (below)
  (c) `ei_bad` false                                 <->  no `e_i` in `ℚ L_d`                 : `NoCoord`
  (d) `greedy_ok`: no vector of `L_d` shorter than `h_0` (`d = 2, 3`), and for `d = 3` no vector of the
      projected lattice shorter than `π h_1`                                                  : `ShortestFirst`
  (e) `μ_d² < radius_bound(..)`  = the node test `4 (M(L_k) - 1/4)² < ∑_{k<i<d} μ_i^{-2} + C_d μ_d^{-2}`
      for every `k < d` (`C_1 = 37/9`, `C_2 = 7/3`, `C_3 = 1`)                          : `NodeBound`
  (f) depth 1 only: `|h_0|² ≤ 16` (the integer form of (e) at `d = 1, k = 0`)                 : `first_le`

`Accepted F` is the conjunction.  `accepted_of_greedy` : a `Greedy` flag of a primitive `v` with all
`v_i ≠ 0` and `ML v < 1/4` is accepted; `exists_flag_accepted` combines this with `greedyBasis_exists`.
All filters are invariant under `h_i ↦ ± h_i` (they only see lattices, Gram forms and `Dq`): `Greedy` is
shown sign-invariant in `GreedyFlip` (so the sign normalisation (b) can be imposed afterwards).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.GreedyFinal
import LRSpectrumFull.L4S3.Reduced34

namespace LRSpectrumFull
namespace L4S3

open Finset LRSpectrumFull.L5S3

/-! ## Definitions of the filters -/

/-- (a) `L_d` is saturated: integer functionals `ρ_b` with `ρ_b (h_a) = δ_ab` (equivalent to `t` primitive). -/
def PrimChild {v : V4} (F : FlagData v) : Prop :=
  ∀ d : ℕ, d ≤ 3 → ∃ ρ : Fin 4 → ℕ → ℤ, ∀ a < d, ∀ b < d,
    ∑ k, hN F.h a k * ρ k b = if a = b then 1 else 0

/-- The coordinate vector `e_i`. -/
def eVec (i : Fin 4) : V4 := fun k => if k = i then 1 else 0

/-- (c) no coordinate vector lies in the rational span of `L_d` (`ei_bad` is false). -/
def NoCoord {v : V4} (F : FlagData v) : Prop :=
  ∀ (i : Fin 4) (d : ℕ), d ≤ 3 → ¬ InQN d F.h (eVec i)

/-- Quadratic form of the Gram matrix of the first `d` rows (`q = ∑ g_ij c_i c_j` in the generator). -/
def gramQ {v : V4} (F : FlagData v) (d : ℕ) (c : ℕ → ℤ) : ℤ :=
  ∑ i ∈ range d, ∑ j ∈ range d, c i * c j * dot (hN F.h i) (hN F.h j)

/-- (d1) `exists_shorter(g, g_00)` is false: `h_0` is a shortest nonzero vector of `L_d`. -/
def ShortestFirst {v : V4} (F : FlagData v) (d : ℕ) : Prop :=
  ∀ c : ℕ → ℤ, (∃ i < d, c i ≠ 0) → dot (hN F.h 0) (hN F.h 0) ≤ gramQ F d c
/-- `μ²_{i+1} = Dq i`, extended by `Dq 2` for `i ≥ 2` (a bookkeeping extension to all of `ℕ`). -/
noncomputable def Dext {v : V4} (F : FlagData v) (i : ℕ) : ℝ := ((F.Dq ⟨min i 2, by omega⟩ : ℚ) : ℝ)

/-- `C_d = ∑_{s < 4-d} (4/3)^s` (`37/9, 7/3, 1` for `d = 1..3`). -/
noncomputable def Cnode (d : ℕ) : ℝ := ∑ s ∈ range (4 - d), (4 / 3 : ℝ) ^ s

/-- Right-hand side of the node test `k` at depth `d`: `∑_{k ≤ i < d-1} μ_{i+1}^{-2} + C_d μ_d^{-2}`. -/
noncomputable def nodeRHS {v : V4} (F : FlagData v) (d k : ℕ) : ℝ :=
  (∑ i ∈ range (d - 1), if k ≤ i then 1 / Dext F i else 0) + Cnode d * (1 / Dext F (d - 1))

/-- (e) node tests: for every stage `k < d`, every stage witness `x` with `f x ≥ c ≥ 1/4`. -/
def NodeBound {v : V4} (F : FlagData v) (d : ℕ) : Prop :=
  ∀ k < d, ∀ (x : Fin 4 → ℝ) (c : ℝ), StageWitness F k x → 1 / 4 ≤ c → c ≤ fmin x →
    4 * (c - 1 / 4) ^ 2 < nodeRHS F d k

/-- All filters of the depth-1, 2, 3 (and 4) nodes, for one flag. -/
structure Accepted {v : V4} (F : FlagData v) : Prop where
  greedy : Greedy v F.h
  prim : PrimChild F
  noCoord : NoCoord F
  short1 : ∀ d, d ≤ 3 → ShortestFirst F d
  reduced : Reduced34 F
  node : ∀ d, 1 ≤ d → d ≤ 3 → NodeBound F d
  first_le : dot (F.h 0) (F.h 0) ≤ 16

/-! ## Proofs -/

theorem Dext_pos {v : V4} (F : FlagData v) (i : ℕ) : 0 < Dext F i := by
  unfold Dext
  exact_mod_cast F.hDpos _

theorem Dext_lt {v : V4} (F : FlagData v) (i : Fin 3) : Dext F i.val = ((F.Dq i : ℚ) : ℝ) := by
  unfold Dext
  have : min i.val 2 = i.val := by have := i.2; omega
  simp only [this]

theorem Dext_step {v : V4} (F : FlagData v) (hr : Reduced34 F) (i : ℕ) :
    3 / 4 * Dext F i ≤ Dext F (i + 1) := by
  by_cases hi : i < 2
  · have h := hr ⟨i, hi⟩
    have e1 : (Fin.castSucc (⟨i, hi⟩ : Fin 2)) = (⟨i, by omega⟩ : Fin 3) := rfl
    have e2 : (Fin.succ (⟨i, hi⟩ : Fin 2)) = (⟨i + 1, by omega⟩ : Fin 3) := rfl
    rw [e1, e2] at h
    have h' : (3 / 4 : ℝ) * ((F.Dq ⟨i, by omega⟩ : ℚ) : ℝ) ≤ ((F.Dq ⟨i + 1, by omega⟩ : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 h
      push_cast at this
      exact this
    have a := Dext_lt F ⟨i, by omega⟩
    have b := Dext_lt F ⟨i + 1, by omega⟩
    simp only at a b
    rw [a, b]; exact h'
  · have h1 : min i 2 = 2 := by omega
    have h2 : min (i + 1) 2 = 2 := by omega
    unfold Dext
    simp only [h1, h2]
    have := F.hDpos ⟨2, by omega⟩
    have h3 : (0 : ℝ) < ((F.Dq ⟨2, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast this
    linarith

theorem Sk_eq_range {v : V4} (F : FlagData v) (k : ℕ) :
    Sk F k = ∑ i ∈ range 3, if k ≤ i then 1 / Dext F i else 0 := by
  unfold Sk
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => if k ≤ i then 1 / Dext F i else 0) 3]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Dext_lt F i]

theorem Cnode_eq (d : ℕ) (hd : 1 ≤ d) (hd4 : d ≤ 3) :
    Cnode d = ∑ s ∈ range (4 - d), (4 / 3 : ℝ) ^ s := rfl

theorem node_of_stage {v : V4} (F : FlagData v) (hv : Primitive v) (hlt : ML v < 1 / 4)
    (hr : Reduced34 F) (d : ℕ) (hd : 1 ≤ d) (hd4 : d ≤ 3) : NodeBound F d := by
  intro k hk x c hx hc hfc
  have hS := stage_prune_free v F k x hv hx hlt c hc hfc
  have hpos : ∀ i, 0 < Dext F i := Dext_pos F
  have hstep : ∀ i, 3 / 4 * Dext F i ≤ Dext F (i + 1) := Dext_step F hr
  have e4 : (3 : ℕ) = (d - 1) + (4 - d) := by omega
  have hsplit : Sk F k = (∑ i ∈ range (d - 1), if k ≤ i then 1 / Dext F i else 0)
      + ∑ s ∈ range (4 - d), 1 / Dext F (d - 1 + s) := by
    rw [Sk_eq_range, e4, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have : k ≤ d - 1 + s := by omega
    simp [this]
  have htail := tail_sum (Dext F) hpos hstep (d - 1) (4 - d)
  have : Sk F k ≤ nodeRHS F d k := by
    rw [hsplit]
    unfold nodeRHS Cnode
    have := htail
    linarith
  linarith

theorem accepted_noCoord {v : V4} (F : FlagData v) (hnz : ∀ i, v i ≠ 0) : NoCoord F := by
  rintro i d hd ⟨a, ha⟩
  apply hnz i
  have h1 : ((v i : ℤ) : ℚ) = ∑ n ∈ range d, a n * ((dot (hN F.h n) v : ℤ) : ℚ) := by
    have e : ((v i : ℤ) : ℚ) = ∑ k : Fin 4, ((eVec i k : ℤ) : ℚ) * (v k : ℚ) := by
      simp [eVec, Finset.sum_ite_eq]
    rw [e]
    simp only [ha, dot]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  have h2 : ∀ n ∈ range d, dot (hN F.h n) v = 0 := by
    intro n hn
    have hn4 : n < 3 := by have := Finset.mem_range.mp hn; omega
    have := F.hv ⟨n, hn4⟩
    simpa [hN, hn4] using this
  have h3 : ((v i : ℤ) : ℚ) = 0 := by
    rw [h1]
    exact Finset.sum_eq_zero (fun n hn => by rw [h2 n hn]; simp)
  exact_mod_cast h3

theorem accepted_prim {v : V4} (F : FlagData v) : PrimChild F := by
  intro d hd
  refine ⟨fun k b => if hb : b < 3 then F.R k ⟨b, hb⟩ else 0, ?_⟩
  intro a ha b hb
  have ha4 : a < 3 := by omega
  have hb4 : b < 3 := by omega
  have := F.hR ⟨a, ha4⟩ ⟨b, hb4⟩
  simp only [hN, ha4, hb4, dite_true]
  rw [this]
  simp [Fin.ext_iff]

theorem dot_sum_sum (d : ℕ) (c : ℕ → ℤ) (x : ℕ → V4) :
    dot (fun k => ∑ i ∈ range d, c i * x i k) (fun k => ∑ i ∈ range d, c i * x i k)
      = ∑ i ∈ range d, ∑ j ∈ range d, c i * c j * dot (x i) (x j) := by
  unfold dot
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem accepted_short1 {v : V4} (F : FlagData v) (hg : Greedy v F.h) (d : ℕ) (hd : d ≤ 3) :
    ShortestFirst F d := by
  intro c ⟨i0, hi0, hc0⟩
  set u : V4 := fun k => ∑ i ∈ range d, c i * hN F.h i k with hu
  have hdv : dot u v = 0 := by
    unfold dot
    have : ∀ k, u k * v k = ∑ i ∈ range d, c i * (hN F.h i k * v k) := by
      intro k; simp only [hu, Finset.sum_mul]; refine Finset.sum_congr rfl (fun i _ => by ring)
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [← Finset.mul_sum]
    have hi4 : i < 3 := by have := Finset.mem_range.mp hi; omega
    have := F.hv ⟨i, hi4⟩
    simp only [dot, hN, hi4, dite_true] at this ⊢
    rw [this]; simp
  have hnq : ¬ InQSpanPrefix F.h 0 u := by
    rintro ⟨c', hc'⟩
    have hz : ∀ k : Fin 4, ∑ m : Fin 3, (if m.val < d then (c m.val : ℚ) else 0) * (F.h m k : ℚ) = 0 := by
      intro k
      have h1 : (u k : ℚ) = 0 := by simpa using hc' k
      have h2 : (u k : ℚ) = ∑ m : Fin 3, (if m.val < d then (c m.val : ℚ) else 0) * (F.h m k : ℚ) := by
        simp only [hu]
        push_cast
        have := prefix_sum_key F.h d hd (fun n => (c n : ℚ)) k
        rw [← this]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        by_cases hm : m.val < d <;> simp [hm, hN_lt]
      rw [← h2]; exact h1
    have := rows_indep F (fun m => if m.val < d then (c m.val : ℚ) else 0) hz ⟨i0, by omega⟩
    simp only [hi0] at this
    exact hc0 (by exact_mod_cast this)
  have := hg 0 (by norm_num) u hdv hnq
  simp only [List.ofFn_succ, List.take_succ_cons, List.take_zero, List.nil_append] at this
  rw [gdl1, gdl1] at this
  have e : dot u u = gramQ F d c := by
    unfold gramQ; exact dot_sum_sum d c (hN F.h)
  have h0 : hN F.h 0 = F.h 0 := by simp [hN]
  rw [← e, h0]
  exact this

theorem Dq0_eq {v : V4} (F : FlagData v) : F.Dq 0 = (dot (F.h 0) (F.h 0) : ℚ) := by
  have h := F.hLDL 0 0
  have l01 : F.Lq 0 1 = 0 := F.hLlow 0 1 (by decide)
  have l02 : F.Lq 0 2 = 0 := F.hLlow 0 2 (by decide)
  have u0 := F.hLunit 0
  simp only [Fin.sum_univ_three, l01, l02, u0] at h
  linarith

theorem accepted_first_le {v : V4} (F : FlagData v) (hv : Primitive v) (hlt : ML v < 1 / 4)
    (hr : Reduced34 F) : dot (F.h 0) (F.h 0) ≤ 16 := by
  have hnb := node_of_stage F hv hlt hr 1 le_rfl (by norm_num) 0 (by norm_num) (fun _ => 1 / 2) (1 / 2)
    (fun i hi => absurd hi (Nat.not_lt_zero _)) (by norm_num) (by
      unfold fmin
      refine Finset.le_inf' _ _ (fun i _ => ?_)
      exact nearestIntDist_ge (by norm_num) (by norm_num) (le_refl _) (by norm_num))
  have hD : Dext F 0 = ((dot (F.h 0) (F.h 0) : ℤ) : ℝ) := by
    have := Dext_lt F 0
    simp only [Fin.val_zero] at this
    rw [this, Dq0_eq]
    push_cast; rfl
  have hpos : (0 : ℝ) < ((dot (F.h 0) (F.h 0) : ℤ) : ℝ) := by rw [← hD]; exact Dext_pos F 0
  unfold nodeRHS at hnb
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, Nat.sub_self] at hnb
  have hC : Cnode 1 = 37 / 9 := by
    unfold Cnode; exact node_constants.2.1
  rw [hC, hD] at hnb
  by_contra hn
  have h19 : (17 : ℝ) ≤ ((dot (F.h 0) (F.h 0) : ℤ) : ℝ) := by
    have : (17 : ℤ) ≤ dot (F.h 0) (F.h 0) := by omega
    exact_mod_cast this
  rw [mul_one_div, lt_div_iff₀ hpos] at hnb
  nlinarith

theorem accepted_of_greedy {v : V4} (F : FlagData v) (hv : Primitive v) (hnz : ∀ i, v i ≠ 0)
    (hlt : ML v < 1 / 4) (hg : Greedy v F.h) : Accepted F := by
  have hr : Reduced34 F := fun i => ratio34_thm F hg i
  exact ⟨hg, accepted_prim F, accepted_noCoord F hnz, fun d hd => accepted_short1 F hg d hd,
    hr, fun d h1 h2 => node_of_stage F hv hlt hr d h1 h2,
    accepted_first_le F hv hlt hr⟩

/-- Every primitive `v` with all entries nonzero and `ML v < 1/4` has a flag accepted by every filter. -/
theorem exists_flag_accepted (v : V4) (hv : Primitive v) (hnz : ∀ i, v i ≠ 0)
    (hlt : ML v < 1 / 4) : ∃ F : FlagData v, Accepted F := by
  obtain ⟨F, hg⟩ := flag_exists v hv
  exact ⟨F, accepted_of_greedy F hv hnz hlt hg⟩

end L4S3
end LRSpectrumFull
