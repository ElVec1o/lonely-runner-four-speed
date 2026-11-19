/-
# L4S5.LinesSound : soundness of the line loop (second half of the line check)

`leafLinesB_sound : leafLinesB r lf = true → LinesOk C (r.toNode c) lf`  (for `C.t5 = t5Data`, `LeafBQP r.h lf`).

Proof outline (the executable specification is `Lines.leafLinesB`):
1. `lat_of_BQP` : a primitive `u ⟂ (h, y)` is `u = x k₀ + z k₁` with `x = q₀·u`, `z = q₁·u`  (`lineVec`).
2. `gcd(x, z) = 1`: a common divisor of `x, z` divides every `u_i`, and `u` is primitive.
3. sign: `-u` has the same `|u_i|`, hence the same `PB` (time witness or residual tuple); so `z ≥ 0` and `z = 0 → x = 1`.
4. box: `a m = (a x + b z)² + D z²`, `d m = (d z + b x)² + D x²` with `D = a d - b² > 0`, and `m = |u|² ≤ nmax` by the window
   test `A₂² m < 4 W₂² G₂` (`A₂ > 0`); `le_isqrtI` gives `z ≤ Z`, `|x| ≤ X`.
5. `lineB` is `true` at `(x, z)` and its guard (gcd, `WinInt`, nonzero, distinct) holds, so `PB u`:
   a time `a/q` of the list `TL` with `TimeOk` (then `timeOk_sound`: `1/4 ≤ ML u`), or `sortAbs u` equals a stored residual
   tuple (then a signed permutation maps `u` onto it: `exists_act_of_sortAbs`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S5.Lines

namespace LRSpectrumFull
namespace L4S5

open Matrix Finset LRSpectrumFull.L4S3 LRSpectrumFull.L4S4

noncomputable section

/-! ## 1. The witness predicate `PB` and the guard `CondB` -/

/-- A time of the list `TL` with `TimeOk`, or a stored residual tuple (compared through the sorted absolute values). -/
def PB (u : V4) : Bool := TL.any (fun p => decide (TimeOk u p.1 p.2)) || t5B u

/-- The guard of `lineB`: coprime `(x, z)`, the four integer window tests, nonzero entries, distinct absolute values. -/
def CondB (r : T1Rec4) (lf : LeafRec4) (x z : ℤ) : Bool :=
  (Int.gcd x z == 1) &&
  decide (WinInt (dot r.h r.h) (dot r.h r.h * dot lf.y lf.y - dot r.h lf.y ^ 2) (4 * wMin r.x1 r.W1 - r.W1) r.W1
    (4 * wMin lf.x2 lf.W2 - lf.W2) lf.W2 (dot (lineVec lf x z) (lineVec lf x z))) &&
  decide (∀ i, lineVec lf x z i ≠ 0) && decide (∀ i j, i ≠ j → |lineVec lf x z i| ≠ |lineVec lf x z j|)

theorem lineB_eq (r : T1Rec4) (lf : LeafRec4) (x z : ℤ) :
    lineB r lf x z = (!CondB r lf x z || PB (lineVec lf x z)) := rfl

theorem CondB_iff (r : T1Rec4) (lf : LeafRec4) (x z : ℤ) :
    CondB r lf x z = true ↔
      Int.gcd x z = 1 ∧
      WinInt (dot r.h r.h) (dot r.h r.h * dot lf.y lf.y - dot r.h lf.y ^ 2) (4 * wMin r.x1 r.W1 - r.W1) r.W1
        (4 * wMin lf.x2 lf.W2 - lf.W2) lf.W2 (dot (lineVec lf x z) (lineVec lf x z)) ∧
      (∀ i, lineVec lf x z i ≠ 0) ∧ (∀ i j, i ≠ j → |lineVec lf x z i| ≠ |lineVec lf x z j|) := by
  simp only [CondB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]

theorem lineB_true (r : T1Rec4) (lf : LeafRec4) (x z : ℤ) (hl : lineB r lf x z = true)
    (hc : CondB r lf x z = true) : PB (lineVec lf x z) = true := by
  rw [lineB_eq, hc] at hl
  simpa using hl

/-! ## 2. Sign invariance of `PB` -/

theorem timeOk_neg (u : V4) (a q : ℤ) : TimeOk (fun i => -u i) a q ↔ TimeOk u a q := by
  simp [TimeOk, abs_neg]

theorem PB_neg (u : V4) : PB (fun i => -u i) = PB u := by
  have e1 : TL.any (fun p => decide (TimeOk (fun i => -u i) p.1 p.2)) = TL.any (fun p => decide (TimeOk u p.1 p.2)) := by
    congr 1
    funext p
    exact decide_eq_decide.2 (timeOk_neg u p.1 p.2)
  have e2 : t5B (fun i => -u i) = t5B u := by
    simp [t5B, sortAbs, abs_neg]
  unfold PB
  rw [e1, e2]

theorem lineVec_neg (lf : LeafRec4) (x z : ℤ) : lineVec lf (-x) (-z) = fun i => -lineVec lf x z i := by
  funext i
  simp [lineVec]
  ring

theorem dot_neg_self (u : V4) : dot (fun i => -u i) (fun i => -u i) = dot u u := by
  simp [dot]

/-! ## 3. A residual tuple: sorted absolute values give a signed permutation -/

instance : IsTotal ℤ (fun a b : ℤ => decide (a ≤ b) = true) := ⟨fun a b => by simpa using le_total a b⟩
instance : IsTrans ℤ (fun a b : ℤ => decide (a ≤ b) = true) :=
  ⟨fun a b c h1 h2 => by simp only [decide_eq_true_eq] at h1 h2 ⊢; exact le_trans h1 h2⟩

theorem sortAbs_pairwise (u : V4) : (sortAbs u).Pairwise (· ≤ ·) := by
  have := List.pairwise_insertionSort (fun a b : ℤ => decide (a ≤ b) = true) [|u 0|, |u 1|, |u 2|, |u 3|]
  exact this.imp (fun h => by simpa using h)

theorem exists_act_of_sortAbs (u : V4) (hnz : ∀ i, u i ≠ 0) (v : V4)
    (h : sortAbs u = [v 0, v 1, v 2, v 3]) : ∃ g : SP, g.act u = v := by
  let a : Fin 4 → ℤ := fun i => |u i|
  let σ := Tuple.sort a
  have hmono : Monotone (a ∘ σ) := Tuple.monotone_sort a
  have hp1 : List.Perm (List.ofFn (a ∘ σ)) [|u 0|, |u 1|, |u 2|, |u 3|] := by
    have := σ.ofFn_comp_perm a
    simpa [List.ofFn_succ, a] using this
  have hp2 : List.Perm (sortAbs u) [|u 0|, |u 1|, |u 2|, |u 3|] :=
    List.perm_insertionSort (fun a b : ℤ => decide (a ≤ b) = true) _
  have heq : List.ofFn (a ∘ σ) = sortAbs u :=
    (hp1.trans hp2.symm).eq_of_pairwise' hmono.sortedLE_ofFn.pairwise (sortAbs_pairwise u)
  rw [h] at heq
  have hv : a ∘ σ = v := by
    apply List.ofFn_injective
    rw [heq]
    simp [List.ofFn_succ]
  refine ⟨⟨σ, fun i => if 0 ≤ u (σ i) then 1 else -1, fun i => by by_cases hh : 0 ≤ u (σ i) <;> simp [hh]⟩, ?_⟩
  funext i
  have hi := congrFun hv i
  simp only [Function.comp, a] at hi
  simp only [SP.act]
  by_cases hh : 0 ≤ u (σ i)
  · simp [hh, ← hi, abs_of_nonneg hh]
  · have : u (σ i) < 0 := lt_of_not_ge hh
    simp [hh, ← hi, abs_of_neg this]

theorem PB_sound (C : Certificate4) (hC : C.t5 = t5Data) (u : V4) (hnz : ∀ i, u i ≠ 0) (h : PB u = true) :
    (∃ r ∈ C.t5, ∃ g : SP, g.act u = r.v) ∨ (1 : ℝ) / 4 ≤ ML u := by
  unfold PB at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · right
    rw [List.any_eq_true] at h
    obtain ⟨p, _, hp⟩ := h
    exact timeOk_sound u p.1 p.2 (of_decide_eq_true hp)
  · left
    unfold t5B at h
    rw [List.any_eq_true] at h
    obtain ⟨r, hr, hs⟩ := h
    have hs' : sortAbs u = [r.v 0, r.v 1, r.v 2, r.v 3] := by simpa using hs
    obtain ⟨g, hg⟩ := exists_act_of_sortAbs u hnz r.v hs'
    exact ⟨r, by rw [hC]; exact hr, g, hg⟩

/-! ## 4. The loop box -/

theorem box_bounds {a b d x z m A2 N : ℤ} (hD : 0 < a * d - b ^ 2) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hm : m = a * x ^ 2 + 2 * b * x * z + d * z ^ 2) (hA : 0 < A2) (hlt : A2 ^ 2 * m < N + 1) :
    |z| ≤ isqrtI (a * (N / A2 ^ 2) / (a * d - b ^ 2)) ∧ |x| ≤ isqrtI (d * (N / A2 ^ 2) / (a * d - b ^ 2)) := by
  have hA2 : 0 < A2 ^ 2 := by positivity
  have hm1 : A2 ^ 2 * m ≤ N := by omega
  have hmN : m ≤ N / A2 ^ 2 := Int.le_ediv_of_mul_le hA2 (by linarith [mul_comm m (A2 ^ 2)])
  have ez : a * m = (a * x + b * z) ^ 2 + (a * d - b ^ 2) * z ^ 2 := by rw [hm]; ring
  have ex : d * m = (d * z + b * x) ^ 2 + (a * d - b ^ 2) * x ^ 2 := by rw [hm]; ring
  have h1 : (a * d - b ^ 2) * z ^ 2 ≤ a * (N / A2 ^ 2) := by
    have := mul_le_mul_of_nonneg_left hmN ha
    nlinarith [sq_nonneg (a * x + b * z)]
  have h2 : (a * d - b ^ 2) * x ^ 2 ≤ d * (N / A2 ^ 2) := by
    have := mul_le_mul_of_nonneg_left hmN hd
    nlinarith [sq_nonneg (d * z + b * x)]
  exact ⟨le_isqrtI (Int.le_ediv_of_mul_le hD (by linarith)), le_isqrtI (Int.le_ediv_of_mul_le hD (by linarith))⟩

theorem dot_lineVec (lf : LeafRec4) (x z : ℤ) :
    dot (lineVec lf x z) (lineVec lf x z) =
      dot (lf.k 0) (lf.k 0) * x ^ 2 + 2 * dot (lf.k 0) (lf.k 1) * x * z + dot (lf.k 1) (lf.k 1) * z ^ 2 := by
  simp only [dot, lineVec, Fin.sum_univ_four]
  ring

theorem dot_self_nonneg (v : V4) : 0 ≤ dot v v := by
  simp only [dot, Fin.sum_univ_four]
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]

/-- The core: a line `(x, z)` with `z ≥ 0` (`z = 0 → x = 1`) satisfying the guard has a witness, if the loop succeeded. -/
theorem line_core (r : T1Rec4) (lf : LeafRec4) (h : leafLinesB r lf = true) (x z : ℤ) (hz : 0 ≤ z)
    (hz0 : z = 0 → x = 1) (hc : CondB r lf x z = true) : PB (lineVec lf x z) = true := by
  obtain ⟨hg, hw, hn, hd⟩ := (CondB_iff r lf x z).1 hc
  unfold leafLinesB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hD, hA⟩, hloop⟩ := h
  obtain ⟨hz', hx'⟩ := box_bounds hD (dot_self_nonneg _) (dot_self_nonneg _) (m := dot (lineVec lf x z) (lineVec lf x z))
    (x := x) (z := z) (N := 4 * lf.W2 ^ 2 * (dot r.h r.h * dot lf.y lf.y - dot r.h lf.y ^ 2) - 1) (dot_lineVec lf x z) hA (by linarith [hw.2.1])
  have hzmem : z.toNat < (isqrtI (dot (lf.k 0) (lf.k 0) *
      ((4 * lf.W2 ^ 2 * (dot r.h r.h * dot lf.y lf.y - dot r.h lf.y ^ 2) - 1) / (4 * wMin lf.x2 lf.W2 - lf.W2) ^ 2) /
      (dot (lf.k 0) (lf.k 0) * dot (lf.k 1) (lf.k 1) - dot (lf.k 0) (lf.k 1) ^ 2)) + 1).toNat := by
    have := (abs_le.1 hz').2
    omega
  have key := hloop z.toNat hzmem
  have hl : lineB r lf x z = true := by
    by_cases hz1 : z = 0
    · have hx1 := hz0 hz1
      subst hz1
      have := key 1 (by simp)
      simpa [hx1] using this
    · have hne : z.toNat ≠ 0 := by omega
      have hxm : x ∈ rngZ (-isqrtI (dot (lf.k 1) (lf.k 1) *
        ((4 * lf.W2 ^ 2 * (dot r.h r.h * dot lf.y lf.y - dot r.h lf.y ^ 2) - 1) / (4 * wMin lf.x2 lf.W2 - lf.W2) ^ 2) /
        (dot (lf.k 0) (lf.k 0) * dot (lf.k 1) (lf.k 1) - dot (lf.k 0) (lf.k 1) ^ 2)))
        (isqrtI (dot (lf.k 1) (lf.k 1) *
        ((4 * lf.W2 ^ 2 * (dot r.h r.h * dot lf.y lf.y - dot r.h lf.y ^ 2) - 1) / (4 * wMin lf.x2 lf.W2 - lf.W2) ^ 2) /
        (dot (lf.k 0) (lf.k 0) * dot (lf.k 1) (lf.k 1) - dot (lf.k 0) (lf.k 1) ^ 2))) := by
        rw [mem_rngZ]; exact abs_le.1 hx'
      have := key x (by simp only [hne, if_false]; exact hxm)
      rwa [Int.toNat_of_nonneg hz] at this
  exact lineB_true r lf x z hl hc

/-! ## 5. The soundness theorem -/

theorem leafLinesB_sound (C : Certificate4) (hC : C.t5 = t5Data) (r : T1Rec4) (c : T1Chk r) (lf : LeafRec4)
    (hb : LeafBQP r.h lf) (h : leafLinesB r lf = true) : LinesOk C (r.toNode c) lf := by
  intro u hprim hnz hdist h0 h1 hwin
  rw [toNode_row0 r c] at h0
  have hwin' : WinInt (dot r.h r.h) (dot r.h r.h * dot lf.y lf.y - dot r.h lf.y ^ 2) (4 * wMin r.x1 r.W1 - r.W1) r.W1
      (4 * wMin lf.x2 lf.W2 - lf.W2) lf.W2 (dot u u) := by
    have := hwin
    simp only [LeafWin4, G2of, toNode_G1, toNode_A1, toNode_W1, toNode_row0] at this
    exact this
  -- (1) the coordinates of `u` in the basis of `K_2`
  have hu := lat_of_BQP r.h lf hb u h0 h1
  set x := dot (lf.q 0) u with hx
  set z := dot (lf.q 1) u with hz
  have hue : u = lineVec lf x z := by
    funext a
    rw [hu a, Fin.sum_univ_two]
    rfl
  -- (2) coprimality from primitivity
  have hgcd : Int.gcd x z = 1 := by
    have hdx : ((Int.gcd x z : ℕ) : ℤ) ∣ x := Int.gcd_dvd_left x z
    have hdz : ((Int.gcd x z : ℕ) : ℤ) ∣ z := Int.gcd_dvd_right x z
    have hdu : ∀ i, ((Int.gcd x z : ℕ) : ℤ) ∣ u i := by
      intro i
      rw [hue]
      exact dvd_add (dvd_mul_of_dvd_left hdx _) (dvd_mul_of_dvd_left hdz _)
    rcases hprim _ hdu with h' | h'
    · exact_mod_cast h'
    · have : (0 : ℤ) ≤ ((Int.gcd x z : ℕ) : ℤ) := Int.natCast_nonneg _
      omega
  -- the guard for `(x, z)` and for `(-x, -z)`
  have hcond : CondB r lf x z = true := by
    rw [CondB_iff]
    rw [← hue]
    exact ⟨hgcd, hwin', hnz, hdist⟩
  have hcond' : CondB r lf (-x) (-z) = true := by
    rw [CondB_iff, lineVec_neg, dot_neg_self, ← hue]
    refine ⟨by simpa using hgcd, hwin', fun i => by simpa using hnz i, fun i j hij => by simpa using hdist i j hij⟩
  -- (3) sign normalisation
  have hPB : PB u = true := by
    by_cases hpos : 0 < z ∨ (z = 0 ∧ x = 1)
    · have hz0 : 0 ≤ z := by rcases hpos with h' | ⟨h', _⟩ <;> omega
      have hzx : z = 0 → x = 1 := by
        intro hzz
        rcases hpos with h' | ⟨_, h'⟩
        · omega
        · exact h'
      have := line_core r lf h x z hz0 hzx hcond
      rwa [← hue] at this
    · push Not at hpos
      obtain ⟨hz0, hz1⟩ := hpos
      have hx1 : z = 0 → x = -1 := by
        intro hzz
        have hg0 : Int.gcd x 0 = 1 := by rw [← hzz]; exact hgcd
        have hx_abs : x.natAbs = 1 := by simpa using hg0
        have h' := hz1 hzz
        omega
      have := line_core r lf h (-x) (-z) (by omega) (fun hzz => by have := hx1 (by omega); omega) hcond'
      rw [lineVec_neg, PB_neg, ← hue] at this
      exact this
  exact PB_sound C hC u hnz hPB

end

end L4S5
end LRSpectrumFull
