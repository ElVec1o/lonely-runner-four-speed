/-
# L4S4.Leaf4 : leaf records, the integer window, the `K_2` certificate and the critical link (n = 4)


* `WinInt G1 G2 A1 W1 A2 W2 m` : the four integer window tests (`W_lo, W_2, W_1, W_0`);
  `leaf_window_int` PROVES that the integer `m = |v|²` of every near-tight `v` whose accepted flag starts with the rows of
  the leaf satisfies them (from `Reduced34` and `NodeBound 3`, k = 0, 1, 2; covolume `μ_3² = m / G_2`).
* `LeafBQP` : the `K_2` certificate of a leaf record (`H B = 0`, `B Q + P H = I`); `lat_of_BQP` : every integer `u` with
  `h · u = y · u = 0` is `∑_j (q_j · u) k_j`.
* `CritEq` link: `crit_link4` : `CritEq ck (g k_j)` for the two basis vectors gives `CritEq ck (g u)` for every such `u`.
* `LeafRel4` (kind 1: critical, only `K_2 ⊆ g⁻¹(critical lattice)`; kind 0: a witness `(x_2, W_2)` and the line claim
  `LinesOk`), `LeafWin4`, `LinesOk`.  A critical leaf is NOT asked for a stage-2 witness or a radius.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S4.Child4

namespace LRSpectrumFull
namespace L4S4

open Matrix Finset LRSpectrumFull.L4S3

/-! ## 1. The integer window -/

/-- The four integer window tests for `m = |v|²` (strict `hi`, non-strict `lo`). -/
def WinInt (G1 G2 A1 W1 A2 W2 m : ℤ) : Prop :=
  3 * G2 ^ 2 ≤ 4 * G1 * m ∧ A2 ^ 2 * m < 4 * W2 ^ 2 * G2 ∧
  A1 ^ 2 * G2 * m < 4 * W1 ^ 2 * (G1 * m + G2 ^ 2) ∧ G1 * G2 * m < 4 * (G2 * m + G1 ^ 2 * m + G1 * G2 ^ 2)

theorem sq_form (m W A : ℤ) (hW : 0 < W) (hA : A = 4 * m - W) :
    4 * ((m : ℚ) / W - 1 / 4) ^ 2 = (A : ℚ) ^ 2 / (4 * (W : ℚ) ^ 2) := by
  have hWq : (0 : ℚ) < W := by exact_mod_cast hW
  have : (A : ℚ) = 4 * m - W := by rw [hA]; push_cast; ring
  rw [this]; first | (field_simp; done) | (field_simp; ring)

theorem gF_two (f : Fin 2 → V4) : gF f = dot (f 0) (f 0) * dot (f 1) (f 1) - dot (f 0) (f 1) ^ 2 := by
  simp [gF, Matrix.det_fin_two, dot_comm' (f 1) (f 0)]
  ring

theorem leadMinor_two {v : V4} (F : FlagData v) :
    leadMinor (gram F) 2 = dot (F.h 0) (F.h 0) * dot (F.h 1) (F.h 1) - dot (F.h 0) (F.h 1) ^ 2 := by
  rw [leadMinor_eq_gF F 2 (by norm_num), gF_two]
  simp [hN]

theorem Cq_three : Cq 3 = 1 := by
  norm_num [Cq, Finset.sum_range_succ]

theorem leadMinor_three_eq {v : V4} (F : FlagData v) (hv : Primitive v) : leadMinor (gram F) 3 = dot v v := by
  rw [leadMinor_three, gram_det_eq_normsq F hv]

/-- **The leaf window is sound.**  For an accepted flag `F` of a primitive `v` and stage witnesses of `M(L_1), M(L_2)`
with `c ≥ 1/4`, the integers `G_1, G_2, A_1, A_2, m = |v|²` satisfy the four tests. -/
theorem leaf_window_int {v : V4} (hv : Primitive v) (F : FlagData v) (hacc : Accepted F)
    (x1 : V4) (W1 : ℤ) (hok1 : WitnessOk F 1 x1 W1) (hc1 : (1 : ℚ) / 4 ≤ cOf (x1, W1))
    (x2 : V4) (W2 : ℤ) (hok2 : WitnessOk F 2 x2 W2) (hc2 : (1 : ℚ) / 4 ≤ cOf (x2, W2)) :
    WinInt (leadMinor (gram F) 1) (leadMinor (gram F) 2) (4 * wMin x1 W1 - W1) W1
      (4 * wMin x2 W2 - W2) W2 (dot v v) := by
  have hm : leadMinor (gram F) 3 = dot v v := leadMinor_three_eq F hv
  have p1 := leadMinor_pos' F 1
  have p2 := leadMinor_pos' F 2
  have p3 : 0 < dot v v := by rw [← hm]; exact leadMinor_pos' F 3
  have q1 : (0 : ℚ) < (leadMinor (gram F) 1 : ℚ) := by exact_mod_cast p1
  have q2 : (0 : ℚ) < (leadMinor (gram F) 2 : ℚ) := by exact_mod_cast p2
  have q3 : (0 : ℚ) < (dot v v : ℚ) := by exact_mod_cast p3
  have hW1 := hok1.1
  have hW2 := hok2.1
  have hW1q : (0 : ℚ) < W1 := by exact_mod_cast hW1
  have hW2q : (0 : ℚ) < W2 := by exact_mod_cast hW2
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- W_lo : ratio34 at i = 1
    have h := hacc.reduced ⟨1, by norm_num⟩
    have e1 : (Fin.castSucc (⟨1, by norm_num⟩ : Fin 2)) = (1 : Fin 3) := rfl
    have e2 : (Fin.succ (⟨1, by norm_num⟩ : Fin 2)) = (2 : Fin 3) := rfl
    rw [e1, e2, Dq_minors_thm v F 1, Dq2_eq F hv] at h
    have h1 : (leadMinor (gram F) (1 + 1) : ℚ) = (leadMinor (gram F) 2 : ℚ) := rfl
    simp only [Fin.val_one] at h
    by_contra hlt
    push Not at hlt
    have hlt' : (4 * (leadMinor (gram F) 1 : ℚ) * (dot v v : ℚ)) < 3 * (leadMinor (gram F) 2 : ℚ) ^ 2 := by
      exact_mod_cast hlt
    have e : (dot v v : ℚ) / (leadMinor (gram F) 2 : ℚ) - 3 / 4 * ((leadMinor (gram F) 2 : ℚ) / (leadMinor (gram F) 1 : ℚ))
        = (4 * (leadMinor (gram F) 1 : ℚ) * (dot v v : ℚ) - 3 * (leadMinor (gram F) 2 : ℚ) ^ 2)
          / (4 * (leadMinor (gram F) 1 : ℚ) * (leadMinor (gram F) 2 : ℚ)) := by
      first | (field_simp; done) | (field_simp; ring)
    have hneg : (4 * (leadMinor (gram F) 1 : ℚ) * (dot v v : ℚ) - 3 * (leadMinor (gram F) 2 : ℚ) ^ 2)
          / (4 * (leadMinor (gram F) 1 : ℚ) * (leadMinor (gram F) 2 : ℚ)) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by positivity)
    have hh : 3 / 4 * ((leadMinor (gram F) 2 : ℚ) / (leadMinor (gram F) 1 : ℚ)) ≤ (dot v v : ℚ) / (leadMinor (gram F) 2 : ℚ) := by
      simpa using h
    linarith
  · -- W_2 : node 3, k = 2
    have hb := nodeBound_to_rat F 3 (by norm_num) (by norm_num) (hacc.node 3 (by norm_num) (by norm_num)) 2
      (by norm_num) x2 W2 hok2 (cOf (x2, W2)) rfl hc2
    have hR : ratRHS (fun n => leadMinor (gram F) n) 3 2 = (leadMinor (gram F) 2 : ℚ) / (dot v v : ℚ) := by
      unfold ratRHS; rw [Cq_three]; simp [Finset.sum_range_succ, hm]
    rw [hR] at hb
    unfold cOf at hb
    simp only [] at hb
    rw [sq_form _ _ _ hW2 rfl, div_lt_div_iff₀ (by positivity) q3] at hb
    have : (4 * wMin x2 W2 - W2 : ℚ) ^ 2 * (dot v v : ℚ) < 4 * (W2 : ℚ) ^ 2 * (leadMinor (gram F) 2 : ℚ) := by
      push_cast at hb ⊢; nlinarith
    exact_mod_cast this
  · -- W_1 : node 3, k = 1
    have hb := nodeBound_to_rat F 3 (by norm_num) (by norm_num) (hacc.node 3 (by norm_num) (by norm_num)) 1
      (by norm_num) x1 W1 hok1 (cOf (x1, W1)) rfl hc1
    have hR : ratRHS (fun n => leadMinor (gram F) n) 3 1
        = (leadMinor (gram F) 1 : ℚ) / (leadMinor (gram F) 2 : ℚ) + (leadMinor (gram F) 2 : ℚ) / (dot v v : ℚ) := by
      unfold ratRHS; rw [Cq_three]; simp [Finset.sum_range_succ, hm]
    rw [hR] at hb
    unfold cOf at hb
    simp only [] at hb
    have e : (leadMinor (gram F) 1 : ℚ) / (leadMinor (gram F) 2 : ℚ) + (leadMinor (gram F) 2 : ℚ) / (dot v v : ℚ)
        = ((leadMinor (gram F) 1 : ℚ) * (dot v v : ℚ) + (leadMinor (gram F) 2 : ℚ) ^ 2)
          / ((leadMinor (gram F) 2 : ℚ) * (dot v v : ℚ)) := by
      first | (field_simp; done) | (field_simp; ring)
    rw [e, sq_form _ _ _ hW1 rfl, div_lt_div_iff₀ (by positivity) (by positivity)] at hb
    have : (4 * wMin x1 W1 - W1 : ℚ) ^ 2 * (leadMinor (gram F) 2 : ℚ) * (dot v v : ℚ)
        < 4 * (W1 : ℚ) ^ 2 * ((leadMinor (gram F) 1 : ℚ) * (dot v v : ℚ) + (leadMinor (gram F) 2 : ℚ) ^ 2) := by
      push_cast at hb ⊢; nlinarith
    exact_mod_cast this
  · -- W_0 : node 3, k = 0 with c_0 = 1/2
    have hok0 : WitnessOk F 0 (fun _ => 1) 2 := ⟨by norm_num, fun i hi => absurd hi (by omega)⟩
    have hb := nodeBound_to_rat F 3 (by norm_num) (by norm_num) (hacc.node 3 (by norm_num) (by norm_num)) 0
      (by norm_num) (fun _ => 1) 2 hok0 (1 / 2) (by rw [← cOf_const, cOf]) (by norm_num)
    have hR : ratRHS (fun n => leadMinor (gram F) n) 3 0
        = 1 / (leadMinor (gram F) 1 : ℚ) + (leadMinor (gram F) 1 : ℚ) / (leadMinor (gram F) 2 : ℚ)
          + (leadMinor (gram F) 2 : ℚ) / (dot v v : ℚ) := by
      unfold ratRHS; rw [Cq_three]; simp [Finset.sum_range_succ, hm, leadMinor_zero]
    rw [hR] at hb
    have e : 1 / (leadMinor (gram F) 1 : ℚ) + (leadMinor (gram F) 1 : ℚ) / (leadMinor (gram F) 2 : ℚ)
          + (leadMinor (gram F) 2 : ℚ) / (dot v v : ℚ)
        = ((leadMinor (gram F) 2 : ℚ) * (dot v v : ℚ) + (leadMinor (gram F) 1 : ℚ) ^ 2 * (dot v v : ℚ)
          + (leadMinor (gram F) 1 : ℚ) * (leadMinor (gram F) 2 : ℚ) ^ 2)
          / ((leadMinor (gram F) 1 : ℚ) * (leadMinor (gram F) 2 : ℚ) * (dot v v : ℚ)) := by
      first | (field_simp; done) | (field_simp; ring)
    rw [e, lt_div_iff₀ (by positivity)] at hb
    have : ((leadMinor (gram F) 1 : ℚ) * (leadMinor (gram F) 2 : ℚ) * (dot v v : ℚ))
        < 4 * ((leadMinor (gram F) 2 : ℚ) * (dot v v : ℚ) + (leadMinor (gram F) 1 : ℚ) ^ 2 * (dot v v : ℚ)
          + (leadMinor (gram F) 1 : ℚ) * (leadMinor (gram F) 2 : ℚ) ^ 2) := by
      norm_num at hb; nlinarith
    exact_mod_cast this

/-! ## 2. The `K_2` certificate and the critical link -/

/-- `K_2` certificate of a leaf record (all kinds): `H B = 0` and `B Q + P H = I_4`. -/
def LeafBQP (h : V4) (lf : LeafRec4) : Prop :=
  (∀ j : Fin 2, dot h (lf.k j) = 0 ∧ dot lf.y (lf.k j) = 0) ∧
  ∀ a c : Fin 4, ∑ j : Fin 2, lf.k j a * lf.q j c + lf.p a 0 * h c + lf.p a 1 * lf.y c = if a = c then 1 else 0

/-- Every integer vector orthogonal to both rows is an integer combination of the two basis vectors. -/
theorem lat_of_BQP (h : V4) (lf : LeafRec4) (hb : LeafBQP h lf) (u : V4) (hu0 : dot h u = 0)
    (hu1 : dot lf.y u = 0) : ∀ a, u a = ∑ j : Fin 2, dot (lf.q j) u * lf.k j a := by
  intro a
  have e1 : u a = ∑ c, (∑ j : Fin 2, lf.k j a * lf.q j c + lf.p a 0 * h c + lf.p a 1 * lf.y c) * u c := by
    have : ∀ c, (∑ j : Fin 2, lf.k j a * lf.q j c + lf.p a 0 * h c + lf.p a 1 * lf.y c) = if a = c then 1 else 0 :=
      fun c => hb.2 a c
    simp only [this]
    simp
  have e2 : ∑ c, (∑ j : Fin 2, lf.k j a * lf.q j c + lf.p a 0 * h c + lf.p a 1 * lf.y c) * u c
      = ∑ j : Fin 2, dot (lf.q j) u * lf.k j a + lf.p a 0 * dot h u + lf.p a 1 * dot lf.y u := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · congr 1
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        unfold dot
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun c _ => by ring)
      · unfold dot
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun c _ => by ring)
    · unfold dot
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun c _ => by ring)
  rw [e1, e2, hu0, hu1]
  simp

/-- The critical link: if `g` maps both basis vectors of `K_2` into the critical lattice (`CritEq`), it maps every
integer `u ⟂ rows` there. -/
theorem crit_link4 (h : V4) (lf : LeafRec4) (hb : LeafBQP h lf) (u : V4) (hu0 : dot h u = 0)
    (hu1 : dot lf.y u = 0) (hc : ∀ j : Fin 2, CritEq lf.ck (lf.g.act (lf.k j))) :
    CritEq lf.ck (lf.g.act u) := by
  have hu := lat_of_BQP h lf hb u hu0 hu1
  have e : lf.g.act u = fun i => dot (lf.q 0) u * lf.g.act (lf.k 0) i + dot (lf.q 1) u * lf.g.act (lf.k 1) i := by
    funext i
    simp only [SP.act]
    rw [hu (lf.g.σ i), Fin.sum_univ_two]
    ring
  rw [e]
  exact critEq_comb lf.ck _ _ _ _ (hc 0) (hc 1)

/-! ## 3. The leaf relation -/

/-- `G_2 = |h|² |y|² - (h · y)²` of the rows `(h, y)`. -/
def G2of (n : NodeW 1 3) (y : V4) : ℤ := G1 n * dot y y - (dot (hN n.rows 0) y) ^ 2

/-- The window tests for the leaf record `lf` under the node `n`. -/
def LeafWin4 (n : NodeW 1 3) (lf : LeafRec4) (m : ℤ) : Prop :=
  WinInt (G1 n) (G2of n lf.y) (A1 n) (n.wit 1).2 (4 * wMin lf.x2 lf.W2 - lf.W2) lf.W2 m

/-- Noncritical leaf data (kind 0): the witness `(x_2, W_2)` of `M(L_2) ≥ 1/4`. -/
def LeafNoncrit (n : NodeW 1 3) (lf : LeafRec4) : Prop :=
  0 < lf.W2 ∧ lf.W2 ∣ dot (hN n.rows 0) lf.x2 ∧ lf.W2 ∣ dot lf.y lf.x2 ∧ (1 : ℚ) / 4 ≤ cOf (lf.x2, lf.W2)

/-- The line claim of a noncritical leaf (what the line loops establish): every primitive `u` of `K_2` with nonzero distinct
absolute entries in the window is a stored residual tuple (up to a signed permutation) or has `1/4 ≤ ML u`. -/
def LinesOk (C : Certificate4) (n : NodeW 1 3) (lf : LeafRec4) : Prop :=
  ∀ u : V4, Primitive u → (∀ i, u i ≠ 0) → (∀ i j, i ≠ j → |u i| ≠ |u j|) →
    dot (hN n.rows 0) u = 0 → dot lf.y u = 0 → LeafWin4 n lf (dot u u) →
    (∃ r ∈ C.t5, ∃ g : SP, g.act u = r.v) ∨ 1 / 4 ≤ ML u

/-- What the checker verifies for a leaf record (a critical leaf needs only the identification of `K_2`
with the critical lattice, no stage-2 witness, no radius, no window). -/
def LeafRel4 (C : Certificate4) (n : NodeW 1 3) (lf : LeafRec4) : Prop :=
  LeafBQP (hN n.rows 0) lf ∧
    ((lf.kind = 1 ∧ ∀ j : Fin 2, CritEq lf.ck (lf.g.act (lf.k j))) ∨
     (lf.kind = 0 ∧ LeafNoncrit n lf ∧ LinesOk C n lf))

end L4S4
end LRSpectrumFull
