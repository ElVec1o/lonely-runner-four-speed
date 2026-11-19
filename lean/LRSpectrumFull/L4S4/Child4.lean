/-
# L4S4.Child4 : the single child step of the four-speed tree (depth-1 node -> leaf rows)

A depth-1 node is data
`NodeW 1 3` (row `h`, basis `b` of `h^⊥` with right inverse `r`, saturation functional `s`, stage witnesses `(x_k, W_k)`
of `M(L_k)`, `k ≤ 1`).  There is NO radius set field (there is no `rk`:
the radius test is the explicit integer inequality F1 below), so a node/leaf never demands anything false at a
critical leaf.

`ChildPass4 n y` is exactly the PASS predicate of the frozen certificate (each conjunct is one filter F0-F5):
 F2 `GcdOne t`, F0 `FirstPos t`, F3 `¬ eiBad`, F1 radius `G2 · 3 A1² < 28 W1² det a` (node test `k = 1`, `C_2 = 7/3`),
 F4 `3 G1 G2 < 12 G2 + 28 G1²` (node test `k = 0`, `c_0 = 1/2`), F5 `3 G1² ≤ 4 G2` (`ratio34`).
It depends on `y` only through `t = tvec b y` (`qform b y = tᵀ adj(a) t`), so there is no representative-invariance
obligation (no `existsShorter` test is needed).

* `child_step4`, `child_step_signed4` : an accepted flag whose first row is the node row passes `ChildPass4` (after the
  sign choice of `h_1`).  `prefixEq_child4` : any lift `y'` of the same coordinates `t` gives the same chain.
* `childPass_box4` : the radius test implies the box `|t_i| ≤ isqrt (28 W1² a_ii / (3 A1²))` (the `tmax` of the certificate).
* `T1Chk`, `T1Rec4.toNode` : a `T1Rec4` that passes the integer checks defines a node.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S4.Records4
import LRSpectrumFull.L4S4.Link
import LRSpectrumFull.L4S4.Prim
import LRSpectrumFull.L4S4.EiBad
import LRSpectrumFull.L4S4.Radius
import LRSpectrumFull.L4S4.Window

namespace LRSpectrumFull
namespace L4S4

open Matrix Finset LRSpectrumFull.L4S3

/-! ## 1. Row families, witnesses, node data -/

/-- Replace row `j` of a (padded) row family by `y`. -/
def setRow (rows : Fin 3 → V4) (j : ℕ) (y : V4) : Fin 3 → V4 := fun i => if i.val = j then y else rows i

theorem hN_setRow_lt (rows : Fin 3 → V4) (j : ℕ) (y : V4) (m : ℕ) (hm : m < j) :
    hN (setRow rows j y) m = hN rows m := by
  by_cases h3 : m < 3
  · simp [hN, h3, setRow, Nat.ne_of_lt hm]
  · simp [hN, h3]

theorem hN_setRow_eq (rows : Fin 3 → V4) (j : ℕ) (y : V4) (hj : j < 3) :
    hN (setRow rows j y) j = y := by
  simp [hN, hj, setRow]

/-- The value `c = min_i ‖X_i / W‖` of a witness. -/
def cOf (w : V4 × ℤ) : ℚ := ((wMin w.1 w.2 : ℤ) : ℚ) / ((w.2 : ℤ) : ℚ)

/-- A node of the tree at level `j` (`d = 4 - j`) with the data the generator stores. NO radius-set field. -/
structure NodeW (j d : ℕ) where
  rows : Fin 3 → V4
  b : Fin d → V4
  s : Fin j → V4
  r : Fin d → V4
  id : NodeId (fun i : Fin j => hN rows i.val) b s r
  wit : ℕ → V4 × ℤ
  w0 : wit 0 = (fun _ => 1, 2)
  wok : ∀ k ≤ j, 0 < (wit k).2 ∧ ∀ i : Fin 3, i.val < k → (wit k).2 ∣ dot (rows i) (wit k).1
  wge : ∀ k ≤ j, (1 : ℚ) / 4 ≤ cOf (wit k)

/-- First nonzero coordinate positive. -/
def FirstPos {d : ℕ} (t : Fin d → ℤ) : Prop := ∃ m : Fin d, 0 < t m ∧ ∀ i : Fin d, i < m → t i = 0

/-- `G_1 = |h|²` of a depth-1 node, and `A_1 = 4 wMin(x_1, W_1) - W_1` (`4 W_1 (c_1 - 1/4)`). -/
def G1 (n : NodeW 1 3) : ℤ := dot (hN n.rows 0) (hN n.rows 0)

def A1 (n : NodeW 1 3) : ℤ := 4 * wMin (n.wit 1).1 (n.wit 1).2 - (n.wit 1).2

/-- The PASS predicate of the frozen certificate (filters F0-F5). -/
def ChildPass4 (n : NodeW 1 3) (y : V4) : Prop :=
  GcdOne (tvec n.b y) ∧ FirstPos (tvec n.b y) ∧ ¬ eiBad n.b (tvec n.b y) ∧
  qform n.b y * (3 * A1 n ^ 2) < 28 * (n.wit 1).2 ^ 2 * (gramK n.b).det ∧
  3 * G1 n * qform n.b y < 12 * qform n.b y + 28 * G1 n ^ 2 ∧
  3 * G1 n ^ 2 ≤ 4 * qform n.b y

/-- The box of the generator is implied by the radius test (`tmax_j = isqrt(bn a_jj / bd)`, `bn = 28 W1²`, `bd = 3 A1²`). -/
theorem childPass_box4 (n : NodeW 1 3) (y : V4) (hp : ChildPass4 n y) (hA : 0 < A1 n) (i : Fin 3) :
    |tvec n.b y i| ≤ isqrtI (28 * (n.wit 1).2 ^ 2 * gramK n.b i i / (3 * A1 n ^ 2)) :=
  box_covers (by norm_num : 1 + 3 = 4) n.id y i _ _ (by positivity) hp.2.2.2.1

/-! ## 2. Small lemmas -/

theorem tvec_neg {d : ℕ} (b : Fin d → V4) (y : V4) :
    tvec b (fun c => - y c) = fun i => - tvec b y i := by
  funext i; simp [tvec, dot, Finset.sum_neg_distrib]

theorem exists_firstpos {d : ℕ} (t : Fin d → ℤ) (h : ∃ m, t m ≠ 0) :
    FirstPos t ∨ FirstPos (fun i => - t i) := by
  classical
  obtain ⟨a, ha⟩ := h
  set S := (Finset.univ : Finset (Fin d)).filter (fun m => t m ≠ 0) with hS
  have hne : S.Nonempty := ⟨a, by simp [hS, ha]⟩
  set m := S.min' hne with hm
  have hmS : t m ≠ 0 := by
    have := Finset.min'_mem S hne
    simpa [hS] using this
  have hbefore : ∀ i : Fin d, i < m → t i = 0 := by
    intro i hi
    by_contra hti
    have : i ∈ S := by simp [hS, hti]
    exact absurd (Finset.min'_le S i this) (not_le.2 hi)
  rcases lt_or_gt_of_ne hmS with h1 | h1
  · right; exact ⟨m, by simpa using h1, fun i hi => by simp [hbefore i hi]⟩
  · left; exact ⟨m, h1, hbefore⟩

theorem gF_one (f : Fin 1 → V4) : gF f = dot (f 0) (f 0) := by
  simp [gF, Matrix.det_unique]

theorem leadMinor_zero (M : Matrix (Fin 3) (Fin 3) ℤ) : leadMinor M 0 = 1 := by
  unfold leadMinor
  have : (Matrix.of fun a b : Fin 3 => if a.val < 0 ∧ b.val < 0 then M a b else if a = b then (1 : ℤ) else 0) = 1 := by
    ext a b; simp [Matrix.one_apply]
  rw [this, Matrix.det_one]

theorem leadMinor_one {v : V4} (F : FlagData v) : leadMinor (gram F) 1 = dot (F.h 0) (F.h 0) := by
  rw [leadMinor_eq_gF F 1 (by norm_num), gF_one]
  simp [hN]

theorem accepted_h0_primitive {v : V4} (F : FlagData v) (hacc : Accepted F) : Primitive (F.h 0) := by
  intro d hd
  obtain ⟨ρ, hρ⟩ := hacc.prim 1 (by norm_num)
  have h1 := hρ 0 (by norm_num) 0 (by norm_num)
  have h2 : ∑ k, F.h 0 k * ρ k 0 = 1 := by simpa [hN] using h1
  have : d ∣ 1 := by
    rw [← h2]; exact Finset.dvd_sum (fun k _ => Dvd.dvd.mul_right (hd k) _)
  exact Int.isUnit_iff.1 (isUnit_of_dvd_one this)

theorem accepted_two_le {v : V4} (hnz : ∀ i, v i ≠ 0) (F : FlagData v) (hacc : Accepted F) :
    2 ≤ dot (F.h 0) (F.h 0) := by
  have hpos : 0 < dot (F.h 0) (F.h 0) := by
    have := leadMinor_pos' F 1
    rwa [leadMinor_one] at this
  by_contra hcon
  have h1 : dot (F.h 0) (F.h 0) = 1 := by omega
  have hv0 := F.hv 0
  have hex : ∃ k0, F.h 0 k0 ≠ 0 := by
    by_contra hh
    push_neg at hh
    have : dot (F.h 0) (F.h 0) = 0 := by simp [dot, hh]
    omega
  obtain ⟨k0, hk0⟩ := hex
  have hsq : ∀ k, F.h 0 k * F.h 0 k ≤ 1 := fun k => by
    have := sq_le_dot4 (F.h 0) k; omega
  have hk0sq : 1 ≤ F.h 0 k0 * F.h 0 k0 := by
    have : 0 < F.h 0 k0 * F.h 0 k0 := mul_self_pos.2 hk0
    omega
  have hzero : ∀ k, k ≠ k0 → F.h 0 k = 0 := by
    intro k hk
    have hpair : F.h 0 k0 * F.h 0 k0 + F.h 0 k * F.h 0 k ≤ 1 := by
      rw [← h1, ← Finset.sum_pair (f := fun x => F.h 0 x * F.h 0 x) (Ne.symm hk)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => mul_self_nonneg _)
    nlinarith [mul_self_nonneg (F.h 0 k)]
  have : dot (F.h 0) v = F.h 0 k0 * v k0 := by
    unfold dot
    rw [Finset.sum_eq_single k0]
    intro k _ hk; rw [hzero k hk]; ring
    intro hh; exact absurd (Finset.mem_univ _) hh
  rw [this] at hv0
  rcases mul_eq_zero.1 hv0 with h | h
  · exact hk0 h
  · exact hnz k0 h

/-! ## 3. The integer forms of the node tests -/

/-- Node test `k = 1`, `C_2 = 7/3`, in integers (the radius test F1). -/
theorem rad_conv (A W G1 G2 m : ℤ) (hW : 0 < W) (hG1 : 0 < G1) (hG2 : 0 < G2) (hA : A = 4 * m - W)
    (h : 4 * ((m : ℚ) / W - 1 / 4) ^ 2 < 7 / 3 * ((G1 : ℚ) / G2)) : G2 * (3 * A ^ 2) < 28 * W ^ 2 * G1 := by
  have hWq : (0 : ℚ) < W := by exact_mod_cast hW
  have h1q : (0 : ℚ) < G1 := by exact_mod_cast hG1
  have h2q : (0 : ℚ) < G2 := by exact_mod_cast hG2
  have key : 4 * ((m : ℚ) / W - 1 / 4) ^ 2 = (A : ℚ) ^ 2 / (4 * (W : ℚ) ^ 2) := by
    have : (A : ℚ) = 4 * m - W := by rw [hA]; push_cast; ring
    rw [this]; first | (field_simp; done) | (field_simp; ring)
  have e2 : (7 / 3 : ℚ) * ((G1 : ℚ) / G2) * (4 * (W : ℚ) ^ 2) = 28 * (W : ℚ) ^ 2 * G1 / (3 * G2) := by
    first | (field_simp; done) | (field_simp; ring)
  rw [key, div_lt_iff₀ (by positivity), e2, lt_div_iff₀ (by positivity)] at h
  have : (G2 : ℚ) * (3 * (A : ℚ) ^ 2) < 28 * (W : ℚ) ^ 2 * G1 := by nlinarith
  exact_mod_cast this

/-- Node test `k = 0` (witness `c_0 = 1/2`), `C_2 = 7/3`, in integers (F4). -/
theorem f4_conv (G1 G2 : ℤ) (hG1 : 0 < G1) (hG2 : 0 < G2)
    (h : 4 * ((1 : ℚ) / 2 - 1 / 4) ^ 2 < 1 / (G1 : ℚ) + 7 / 3 * ((G1 : ℚ) / G2)) :
    3 * G1 * G2 < 12 * G2 + 28 * G1 ^ 2 := by
  have h1q : (0 : ℚ) < G1 := by exact_mod_cast hG1
  have h2q : (0 : ℚ) < G2 := by exact_mod_cast hG2
  have e : 1 / (G1 : ℚ) + 7 / 3 * ((G1 : ℚ) / G2) = (3 * G2 + 7 * (G1 : ℚ) ^ 2) / (3 * G1 * G2) := by
    first | (field_simp; done) | (field_simp; ring)
  rw [e, lt_div_iff₀ (by positivity)] at h
  have : (3 * G1 * G2 : ℚ) < 12 * G2 + 28 * (G1 : ℚ) ^ 2 := by nlinarith
  exact_mod_cast this

theorem Cq_two : Cq 2 = 7 / 3 := by
  norm_num [Cq, Finset.sum_range_succ]

/-! ## 4. The child step -/

theorem inQN_of_ext {v : V4} (F : FlagData v) {j : ℕ} (u : V4)
    (h : InQExt (fun i : Fin j => hN F.h i.val) (hN F.h j) u) : InQN (j + 1) F.h u := by
  obtain ⟨c, c0, hc⟩ := h
  refine ⟨fun m => if hm : m < j then c ⟨m, hm⟩ else c0, fun k => ?_⟩
  rw [hc k, Finset.sum_range_succ]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun m => (if hm : m < j then c ⟨m, hm⟩ else c0) * (hN F.h m k : ℚ)) j]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [i.2]
  · simp

theorem nodeF_of_rows {v : V4} (F : FlagData v) {j d : ℕ} (hj : j ≤ 3) (n : NodeW j d)
    (hrows : ∀ i : Fin 3, i.val < j → F.h i = n.rows i) :
    NodeId (fun i : Fin j => hN F.h i.val) n.b n.s n.r := by
  have : (fun i : Fin j => hN F.h i.val) = (fun i : Fin j => hN n.rows i.val) := by
    funext i
    have hi3 : i.val < 3 := by omega
    simp [hN, hi3, hrows ⟨i.val, hi3⟩ i.2]
  rw [this]; exact n.id

theorem hN_rows_eq {v : V4} (F : FlagData v) {j d : ℕ} (hj : j ≤ 3) (n : NodeW j d)
    (hrows : ∀ i : Fin 3, i.val < j → F.h i = n.rows i) (m : ℕ) (hm : m < j) :
    hN F.h m = hN n.rows m := by
  have h3 : m < 3 := by omega
  simp [hN, h3, hrows ⟨m, h3⟩ hm]

/-- **Child step.**  An accepted flag `F` whose first row is the row of the depth-1 node `n`, and whose second row has
`t = tvec b h_1` with first nonzero coordinate positive, passes every filter of the certificate at `n`. -/
theorem child_step4 {v : V4} (F : FlagData v) (hacc : Accepted F) (n : NodeW 1 3)
    (hrows : ∀ i : Fin 3, i.val < 1 → F.h i = n.rows i)
    (hpos : FirstPos (tvec n.b (hN F.h 1))) : ChildPass4 n (hN F.h 1) := by
  have hj3 : 1 < 3 := by norm_num
  have hjd : 1 + 3 = 4 := by norm_num
  have hy : hN F.h 1 = F.h ⟨1, hj3⟩ := by simp [hN]
  have hnodeF := nodeF_of_rows F (j := 1) (d := 3) (by norm_num) n hrows
  have hFN := hN_rows_eq F (j := 1) (d := 3) (by norm_num) n hrows
  have h0 : hN n.rows 0 = hN F.h 0 := (hFN 0 (by norm_num)).symm
  have hgcd : GcdOne (tvec n.b (hN F.h 1)) := by
    rw [hy]; exact gcd_of_primChild F hjd hj3 hnodeF hacc.prim
  have hex : ∃ m, tvec n.b (hN F.h 1) m ≠ 0 := by
    by_contra hh
    push_neg at hh
    have : Finset.univ.gcd (tvec n.b (hN F.h 1)) = 0 := by
      rw [Finset.gcd_eq_zero_iff]; intro x _; exact hh x
    exact absurd (hgcd.symm.trans this) one_ne_zero
  have hnoei : ¬ eiBad n.b (tvec n.b (hN F.h 1)) := by
    intro h
    rw [eiBad_iff hjd hnodeF _ hex] at h
    obtain ⟨i, hi⟩ := h
    exact hacc.noCoord i (1 + 1) (by norm_num) (inQN_of_ext F _ hi)
  -- minors
  have hmin := flag_minor_node F hjd hj3 hnodeF
  have hGj : leadMinor (gram F) 1 = (gramK n.b).det := hmin.1
  have hGq : leadMinor (gram F) 2 = qform n.b (hN F.h 1) := by rw [hy]; exact hmin.2.1
  have hDq1 : F.Dq ⟨1, hj3⟩ = (qform n.b (hN F.h 1) : ℚ) / ((gramK n.b).det : ℚ) := by
    have := hmin.2.2; rw [hy]; exact this
  have hG1 : G1 n = leadMinor (gram F) 1 := by
    unfold G1; rw [leadMinor_one, h0]; simp [hN]
  have hdet : (gramK n.b).det = G1 n := by rw [hG1, hGj]
  have hp1 : 0 < G1 n := by rw [hG1]; exact leadMinor_pos' F 1
  have hp2 : 0 < qform n.b (hN F.h 1) := by rw [← hGq]; exact leadMinor_pos' F 2
  -- F5: ratio34
  have hr : 3 * G1 n ^ 2 ≤ 4 * qform n.b (hN F.h 1) := by
    have h := hacc.reduced ⟨0, by norm_num⟩
    have e1 : (Fin.castSucc (⟨0, by norm_num⟩ : Fin 2)) = (0 : Fin 3) := rfl
    have e2 : (Fin.succ (⟨0, by norm_num⟩ : Fin 2)) = (⟨1, hj3⟩ : Fin 3) := rfl
    rw [e1, e2, Dq0_eq, hDq1, hdet] at h
    have hdot : (dot (F.h 0) (F.h 0) : ℚ) = (G1 n : ℚ) := by rw [hG1, leadMinor_one]
    rw [hdot] at h
    have hp1q : (0 : ℚ) < G1 n := by exact_mod_cast hp1
    rw [le_div_iff₀ hp1q] at h
    have : (3 * (G1 n : ℚ) ^ 2) ≤ 4 * (qform n.b (hN F.h 1) : ℚ) := by nlinarith
    exact_mod_cast this
  -- F1: radius (node test k = 1)
  have hW1 := n.wok 1 le_rfl
  have hok1 : WitnessOk F 1 (n.wit 1).1 (n.wit 1).2 :=
    ⟨hW1.1, fun i hi => by rw [hrows i hi]; exact hW1.2 i hi⟩
  have hb1 := nodeBound_to_rat F 2 (by norm_num) (by norm_num) (hacc.node 2 (by norm_num) (by norm_num)) 1
    (by norm_num) (n.wit 1).1 (n.wit 1).2 hok1 (cOf (n.wit 1)) rfl (n.wge 1 le_rfl)
  have hR1 : ratRHS (fun m => leadMinor (gram F) m) 2 1
      = 7 / 3 * ((leadMinor (gram F) 1 : ℚ) / (leadMinor (gram F) 2 : ℚ)) := by
    unfold ratRHS; rw [Cq_two]; simp [Finset.sum_range_succ]
  rw [hR1, ← hG1, hGq] at hb1
  have hrad := rad_conv (A1 n) (n.wit 1).2 (G1 n) (qform n.b (hN F.h 1)) (wMin (n.wit 1).1 (n.wit 1).2)
    hW1.1 hp1 hp2 rfl hb1
  -- F4: node test k = 0 with the witness c_0 = 1/2
  have hw0 := n.wok 0 (by norm_num)
  have hok0 : WitnessOk F 0 (n.wit 0).1 (n.wit 0).2 := ⟨hw0.1, fun i hi => absurd hi (by omega)⟩
  have hb0 := nodeBound_to_rat F 2 (by norm_num) (by norm_num) (hacc.node 2 (by norm_num) (by norm_num)) 0
    (by norm_num) (n.wit 0).1 (n.wit 0).2 hok0 (cOf (n.wit 0)) rfl (n.wge 0 (by norm_num))
  have hc0 : cOf (n.wit 0) = 1 / 2 := by
    rw [cOf, n.w0]; simp [wMin]
  have hR0 : ratRHS (fun m => leadMinor (gram F) m) 2 0
      = 1 / (leadMinor (gram F) 1 : ℚ) + 7 / 3 * ((leadMinor (gram F) 1 : ℚ) / (leadMinor (gram F) 2 : ℚ)) := by
    unfold ratRHS; rw [Cq_two]; simp [Finset.sum_range_succ, leadMinor_zero]
  rw [hR0, hc0, ← hG1, hGq] at hb0
  have hf4 := f4_conv (G1 n) (qform n.b (hN F.h 1)) hp1 hp2 hb0
  exact ⟨hgcd, hpos, hnoei, by rw [hdet]; exact hrad, hf4, hr⟩

/-- The sign of `h_1` can be chosen so that `t` has first nonzero coordinate positive. -/
theorem child_step_signed4 {v : V4} (hv : Primitive v) (hnz : ∀ i, v i ≠ 0) (hlt : ML v < 1 / 4)
    (F : FlagData v) (hacc : Accepted F) (n : NodeW 1 3)
    (hrows : ∀ i : Fin 3, i.val < 1 → F.h i = n.rows i) :
    ∃ F' : FlagData v, Accepted F' ∧ (∀ i : Fin 3, i.val < 1 → F'.h i = n.rows i) ∧
      ChildPass4 n (hN F'.h 1) := by
  have hj3 : 1 < 3 := by norm_num
  have hy : hN F.h 1 = F.h ⟨1, hj3⟩ := by simp [hN]
  have hnodeF := nodeF_of_rows F (j := 1) (d := 3) (by norm_num) n hrows
  have hgcd : GcdOne (tvec n.b (hN F.h 1)) := by
    rw [hy]; exact gcd_of_primChild F (by norm_num : 1 + 3 = 4) hj3 hnodeF hacc.prim
  have hex : ∃ m, tvec n.b (hN F.h 1) m ≠ 0 := by
    by_contra hh
    push_neg at hh
    have : Finset.univ.gcd (tvec n.b (hN F.h 1)) = 0 := by
      rw [Finset.gcd_eq_zero_iff]; intro x _; exact hh x
    exact absurd (hgcd.symm.trans this) one_ne_zero
  rcases exists_firstpos _ hex with hp | hp
  · exact ⟨F, hacc, hrows, child_step4 F hacc n hrows hp⟩
  · let ε : Fin 3 → ℤ := fun i => if i = (1 : Fin 3) then -1 else 1
    have hε : ∀ i, ε i = 1 ∨ ε i = -1 := fun i => by
      by_cases h : i = (1 : Fin 3) <;> simp [ε, h]
    have hacc' : Accepted (F.flip ε hε) :=
      accepted_of_greedy _ hv hnz hlt (greedy_flip F hacc.greedy ε hε)
    have hrows' : ∀ i : Fin 3, i.val < 1 → (F.flip ε hε).h i = n.rows i := by
      intro i hi
      have hne : i ≠ (1 : Fin 3) := fun h => by rw [h] at hi; exact lt_irrefl _ hi
      rw [← hrows i hi]
      funext k
      simp [FlagData.flip, ε, hne]
    have hrowj : hN (F.flip ε hε).h 1 = fun c => - hN F.h 1 c := by
      funext c
      simp [hN, hj3, FlagData.flip, ε]
    refine ⟨F.flip ε hε, hacc', hrows', child_step4 _ hacc' n hrows' ?_⟩
    rw [hrowj, tvec_neg]
    exact hp

/-! ## 5. The row `y'` of the enumerated child: same chain -/

theorem latRows_self (r : Fin 3 → V4) (i : ℕ) : LatRows r (i + 1) (hN r i) := by
  refine ⟨fun m => if m = i then 1 else 0, fun a => ?_⟩
  simp [Finset.sum_ite_eq']

theorem prefixEq_child4 {v : V4} (F : FlagData v) (n : NodeW 1 3)
    (hrows : ∀ i : Fin 3, i.val < 1 → F.h i = n.rows i) (y' : V4)
    (hy : ∀ i, dot (n.b i) y' = dot (n.b i) (hN F.h 1)) :
    PrefixEq F (setRow n.rows 1 y') 2 := by
  have hj : 1 < 3 := by norm_num
  have hnodeF := nodeF_of_rows F (j := 1) (d := 3) (by norm_num) n hrows
  have hFN := hN_rows_eq F (j := 1) (d := 3) (by norm_num) n hrows
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hij | hij
  · have e : hN (setRow n.rows 1 y') i = hN F.h i := by
      rw [hN_setRow_lt _ _ _ _ hij, hFN i hij]
    rw [e]
    exact ⟨latRows_self F.h i, by have := latRows_self (setRow n.rows 1 y') i; rwa [e] at this⟩
  · have key : LatRows F.h 2 (hN (setRow n.rows 1 y') 1) ∧ LatRows (setRow n.rows 1 y') 2 (hN F.h 1) := by
      have hd := lat_of_same_coords (by norm_num : 1 + 3 = 4) hnodeF (hN F.h 1) y' (fun i => (hy i).symm)
      set β : ℕ → ℤ := fun m => if hm : m < 1 then dot (n.s ⟨m, hm⟩) (fun c => y' c - hN F.h 1 c) else 0 with hβ
      have hsum : ∀ a, ∑ k : Fin 1, dot (n.s k) (fun c => y' c - hN F.h 1 c) * hN F.h k.val a
          = ∑ m ∈ range 1, β m * hN F.h m a := by
        intro a
        rw [← Fin.sum_univ_eq_sum_range (fun m => β m * hN F.h m a) 1]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        have hk0 : k = 0 := Subsingleton.elim _ _
        subst hk0
        simp [hβ]
      have hy'a : ∀ a, y' a = hN F.h 1 a + ∑ m ∈ range 1, β m * hN F.h m a := by
        intro a
        rw [← hsum a]
        exact hd a
      rw [hN_setRow_eq _ _ _ hj]
      refine ⟨⟨fun m => if m < 1 then β m else 1, fun a => ?_⟩, ⟨fun m => if m < 1 then - β m else 1, fun a => ?_⟩⟩
      · rw [Finset.sum_range_succ, hy'a a]
        have : ∑ m ∈ range 1, (if m < 1 then β m else 1) * hN F.h m a = ∑ m ∈ range 1, β m * hN F.h m a :=
          Finset.sum_congr rfl (fun m hm => by simp [Finset.mem_range.1 hm])
        rw [this]; simp; ring
      · rw [Finset.sum_range_succ, hN_setRow_eq _ _ _ hj]
        have : ∑ m ∈ range 1, (if m < 1 then - β m else 1) * hN (setRow n.rows 1 y') m a
            = - ∑ m ∈ range 1, β m * hN F.h m a := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl (fun m hm => ?_)
          have hm' := Finset.mem_range.1 hm
          rw [hN_setRow_lt _ _ _ _ hm', ← hFN m hm']
          simp [hm']
        rw [this, hy'a a]; simp
    rw [hij]; exact key

/-! ## 6. The depth-1 records and their integer checks -/

/-- The integer checks of a `T1Rec4`: `b ⊥ h`, `h · s = 1`, `b r = I`, witness `W1 > 0`, `W1 ∣ h · x1`,
`4 wMin(x1, W1) > W1`.  (The shape `2 ≤ |h|² ≤ 16` and the completeness loop are `T1Ok4` / the `t1` stream.) -/
def T1Chk (r : T1Rec4) : Prop :=
  (∀ i, dot (r.b i) r.h = 0) ∧ dot r.h r.s = 1 ∧ (∀ i k, dot (r.b i) (r.r k) = if i = k then 1 else 0) ∧
  0 < r.W1 ∧ r.W1 ∣ dot r.h r.x1 ∧ r.W1 < 4 * wMin r.x1 r.W1

theorem cOf_const : cOf (fun _ => (1 : ℤ), (2 : ℤ)) = 1 / 2 := by
  rw [cOf]; simp [wMin]

/-- A passing `T1Rec4` is a depth-1 node. -/
def T1Rec4.toNode (r : T1Rec4) (c : T1Chk r) : NodeW 1 3 where
  rows := fun _ => r.h
  b := r.b
  s := fun _ => r.s
  r := r.r
  id := ⟨fun i k => by simpa [hN, dot_comm'] using c.1 i,
         fun i k => by
           have : i = k := Subsingleton.elim _ _
           subst this; simpa [hN] using c.2.1,
         c.2.2.1⟩
  wit := fun k => if k = 0 then ((fun _ => 1), 2) else (r.x1, r.W1)
  w0 := by simp
  wok := fun k hk => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
    · simp
    · exact ⟨by simpa using c.2.2.2.1, fun i hi => by
        have : i.val = 0 := by omega
        simpa [this] using c.2.2.2.2.1⟩
  wge := fun k hk => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
    · simp only [if_true]; rw [cOf_const]; norm_num
    · simp only [one_ne_zero, if_false]
      have hW : (0 : ℚ) < r.W1 := by exact_mod_cast c.2.2.2.1
      have h4 : (r.W1 : ℚ) < 4 * wMin r.x1 r.W1 := by exact_mod_cast c.2.2.2.2.2
      rw [cOf, le_div_iff₀ hW]
      simp only []
      nlinarith

end L4S4
end LRSpectrumFull
