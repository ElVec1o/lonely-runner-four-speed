/-
# L4S5.CheckT1 : the depth-1 checker (`StreamHyp4.t1`) on the real certificate

* `t1Chk_all` : the 15 stored records pass `T1Chk` (kernel evaluation); hence `R1`, the set of the 15 node images
  `(t1At i).toNode`, is a set of nodes.  `0 < A1` at each node is part of `T1Chk` (`W1 < 4 wMin`), used in `node_sound`.
* `chkAllOf` : every sorted vector with entries in `[0, 4]`, `gcd = 1`, `2 ≤ |h|² ≤ 16` is among the stored `h`
  (625-candidate loop, kernel evaluation); `t1_hyp` is the field `t1` of `StreamHyp4` for `R1`.
* Controls: a corrupted record fails `T1Chk`; a list with one vector removed fails the loop.

No `sorry`, no `native_decide` (`decide +kernel` only), no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S5.Data

namespace LRSpectrumFull
namespace L4S5

open Matrix Finset LRSpectrumFull.L4S3 LRSpectrumFull.L4S4

def t1Dflt : T1Rec4 := ⟨![0, 0, 0, 0], ![0, 0, 0, 0], 1, fun _ => ![0, 0, 0, 0], fun _ => ![0, 0, 0, 0], ![0, 0, 0, 0]⟩

def t1At (i : ℕ) : T1Rec4 := t1Data.getD i t1Dflt

theorem t1Data_length : t1Data.length = 15 := by decide +kernel

theorem t1Chk_all : ∀ i < 15, T1Chk (t1At i) := by decide +kernel

/-- The depth-1 nodes of the certificate. -/
def R1 : Set (NodeW 1 3) := {n | ∃ i < 15, ∃ hc : T1Chk (t1At i), n = (t1At i).toNode hc}

def d1Tup : List (ℤ × ℤ × ℤ × ℤ) :=
  (List.range 15).map fun i => ((t1At i).h 0, (t1At i).h 1, (t1At i).h 2, (t1At i).h 3)

def d1Chk (a0 a1 a2 a3 : ℤ) : Bool :=
  decide (a0 ≤ a1) && decide (a1 ≤ a2) && decide (a2 ≤ a3) &&
  decide (2 ≤ a0 * a0 + a1 * a1 + a2 * a2 + a3 * a3) && decide (a0 * a0 + a1 * a1 + a2 * a2 + a3 * a3 ≤ 16) &&
  decide (Nat.gcd (Nat.gcd (Nat.gcd a0.natAbs a1.natAbs) a2.natAbs) a3.natAbs = 1)

def d1Vals : List ℤ := [0, 1, 2, 3, 4]

def chkAllOf (L : List (ℤ × ℤ × ℤ × ℤ)) : Bool :=
  d1Vals.all fun a0 => d1Vals.all fun a1 => d1Vals.all fun a2 => d1Vals.all fun a3 =>
    !d1Chk a0 a1 a2 a3 || L.contains (a0, a1, a2, a3)

theorem chkAll_true : chkAllOf d1Tup = true := by decide +kernel

theorem mem_vals {a : ℤ} (h0 : 0 ≤ a) (h4 : a ≤ 4) : a ∈ d1Vals := by
  unfold d1Vals
  interval_cases a <;> simp

theorem chkAll_sound {L : List (ℤ × ℤ × ℤ × ℤ)} (hL : chkAllOf L = true) (a0 a1 a2 a3 : ℤ)
    (h0 : a0 ∈ d1Vals) (h1 : a1 ∈ d1Vals) (h2 : a2 ∈ d1Vals) (h3 : a3 ∈ d1Vals)
    (hc : d1Chk a0 a1 a2 a3 = true) : (a0, a1, a2, a3) ∈ L := by
  unfold chkAllOf at hL
  simp only [List.all_eq_true] at hL
  have := hL a0 h0 a1 h1 a2 h2 a3 h3
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with h | h
  · rw [h] at hc; exact absurd hc (by decide)
  · simpa using h

theorem gcd_prim4 (h : V4) (hp : Primitive h) :
    Nat.gcd (Nat.gcd (Nat.gcd (h 0).natAbs (h 1).natAbs) (h 2).natAbs) (h 3).natAbs = 1 := by
  set g := Nat.gcd (Nat.gcd (Nat.gcd (h 0).natAbs (h 1).natAbs) (h 2).natAbs) (h 3).natAbs with hg
  have d3 : g ∣ (h 3).natAbs := Nat.gcd_dvd_right _ _
  have d2 : g ∣ (h 2).natAbs := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have d1 : g ∣ (h 1).natAbs := ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_right _ _)
  have d0 : g ∣ (h 0).natAbs := ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_left _ _)
  have key : ∀ i, (g : ℤ) ∣ h i := by
    intro i
    fin_cases i
    · exact Int.natCast_dvd.2 d0
    · exact Int.natCast_dvd.2 d1
    · exact Int.natCast_dvd.2 d2
    · exact Int.natCast_dvd.2 d3
  rcases hp g key with e | e
  · exact_mod_cast e
  · omega

theorem dot_four (h : V4) : dot h h = h 0 * h 0 + h 1 * h 1 + h 2 * h 2 + h 3 * h 3 := by
  simp [dot, Fin.sum_univ_four]

/-- Every depth-1 vector `T1Ok4 h` is a stored vector. -/
theorem t1_complete (h : V4) (hT : T1Ok4 h) : ∃ i < 15, (t1At i).h = h := by
  obtain ⟨hs, hb, hp, h2, h16⟩ := hT
  have hge : ∀ i, 0 ≤ h i := fun i => (hs i i le_rfl).1
  have hmon : ∀ i j : Fin 4, i ≤ j → h i ≤ h j := fun i j hij => (hs i j hij).2
  have hc : d1Chk (h 0) (h 1) (h 2) (h 3) = true := by
    rw [dot_four] at h2 h16
    have e01 := hmon 0 1 (by decide)
    have e12 := hmon 1 2 (by decide)
    have e23 := hmon 2 3 (by decide)
    have g1 := gcd_prim4 h hp
    simp [d1Chk, e01, e12, e23, h2, h16, g1]
  have hm := chkAll_sound chkAll_true (h 0) (h 1) (h 2) (h 3)
    (mem_vals (hge 0) (hb 0)) (mem_vals (hge 1) (hb 1)) (mem_vals (hge 2) (hb 2)) (mem_vals (hge 3) (hb 3)) hc
  unfold d1Tup at hm
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hm
  obtain ⟨i, hi, e0, e1, e2, e3⟩ := hm
  refine ⟨i, hi, ?_⟩
  funext a
  fin_cases a <;> simp [e0, e1, e2, e3]

/-- **`StreamHyp4.t1` for `R1`.** -/
theorem t1_hyp : ∀ h : V4, T1Ok4 h → ∃ n ∈ R1, hN n.rows 0 = h := by
  intro h hT
  obtain ⟨i, hi, e⟩ := t1_complete h hT
  exact ⟨(t1At i).toNode (t1Chk_all i hi), ⟨i, hi, t1Chk_all i hi, rfl⟩, by rw [toNode_row0, e]⟩

/-! ## Controls -/

/-- A corrupted record (`b_0` changed): the node identities fail. -/
def badB : T1Rec4 := { t1At 0 with b := fun i => if i = 0 then ![1, 1, 1, 1] else (t1At 0).b i }

theorem ctl_badB : ¬ T1Chk badB := by decide +kernel

/-- A corrupted witness (`W1` multiplied by 5: the strict test `W1 < 4 wMin` fails). -/
def badW : T1Rec4 := { t1At 0 with W1 := 5 * (t1At 0).W1 }

theorem ctl_badW : ¬ T1Chk badW := by decide +kernel

/-- Dropping one stored vector breaks the completeness loop. -/
theorem ctl_dropped : chkAllOf (d1Tup.drop 1) = false := by decide +kernel

theorem ctl_chk : d1Chk 0 0 0 1 = false ∧ d1Chk 1 2 3 4 = false ∧ d1Chk 0 0 1 1 = true := by decide +kernel

end L4S5
end LRSpectrumFull
