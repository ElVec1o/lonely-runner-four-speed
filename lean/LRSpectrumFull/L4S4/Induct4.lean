/-
# L4S4.Induct4 : the T1 -> leaf induction (completeness of the four-speed tree) and `tree_complete4`

`StreamHyp4` has the two stage statements the checkers (`L4S5`) must discharge:

* `t1` : every depth-1 representative `T1Ok4 h` is the first row of a stored depth-1 node of `R1`;
* `t2` : every candidate row `y` that passes `ChildPass4` at a node of `R1` has a stored leaf record `lf` with the SAME
  coordinates `t` (`b_i · lf.y = b_i · y`) satisfying `LeafRel4` (`K_2` certificate, then critical identification
  (kind 1) or a stage-2 witness and the line claim `LinesOk` (kind 0)).

`tree_complete4` PROVES, from `StreamHyp4` and the verified chain `L4S3`/`L4S4` (`exists_flag_accepted`,
`chain1_rep_flag4`, `child_step_signed4`, `prefixEq_child4`, `accepted_prefix`, `leaf_window_int`, `crit_link4`):
every near-tight `v` with pairwise distinct absolute entries is on a critical torus (`L4Tail.OnCritTorus`) or is, up to a
signed permutation, a stored residual tuple.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S4.Leaf4

namespace LRSpectrumFull
namespace L4S4

open Matrix Finset LRSpectrumFull.L4S3

/-- The two per-stage statements of the n = 4 certificate (nothing else is assumed). -/
structure StreamHyp4 (C : Certificate4) (R1 : Set (NodeW 1 3)) : Prop where
  t1 : ∀ h : V4, T1Ok4 h → ∃ n ∈ R1, hN n.rows 0 = h
  t2 : ∀ n ∈ R1, ∀ y : V4, ChildPass4 n y →
    ∃ lf ∈ C.leaves, (∀ i, dot (n.b i) lf.y = dot (n.b i) y) ∧ LeafRel4 C n lf

/-- Depth 1 : an accepted flag of `v` and a signed permutation sending its first row to `rep 0` give an accepted flag
of `g v` whose first row is `rep 0`. -/
theorem chain1_rep_flag4 {v : V4} (hv : Primitive v) (hnz : ∀ i, v i ≠ 0) (hlt : ML v < 1 / 4)
    (F : FlagData v) (hacc : Accepted F) (g : SP) (rep : Fin 3 → V4) (hrel : g.act (hN F.h 0) = hN rep 0) :
    ∃ F' : FlagData (g.act v), Accepted F' ∧ F'.h 0 = rep 0 := by
  have hP : PrefixEq (F.act g) rep 1 := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    have h0 : hN (F.act g).h 0 = g.act (hN F.h 0) := by
      funext a; simp [hN, L4S3.FlagData.act]
    refine ⟨⟨fun _ => 1, fun a => ?_⟩, ⟨fun _ => 1, fun a => ?_⟩⟩ <;>
    · have := congrFun hrel a
      (simp [h0]) <;> linarith [this]
  obtain ⟨F', hacc', _, hrows⟩ := accepted_act_prefix hv hnz hlt F hacc.greedy g rep 1 (by omega) hP
  exact ⟨F', hacc', hrows 0 (by simp)⟩

/-- **The tree theorem for four speeds, from the per-stage statements.**  Every near-tight `v` with pairwise distinct
absolute entries lies, up to a signed permutation, on a critical torus, or is a stored residual tuple. -/
theorem tree_complete4 {C : Certificate4} {R1 : Set (NodeW 1 3)} (H : StreamHyp4 C R1) (v : V4)
    (hnt : NearTight v) (hdist : ∀ i j, i ≠ j → |v i| ≠ |v j|) :
    L4Tail.OnCritTorus v ∨ (∃ r ∈ C.t5, ∃ g : SP, g.act v = r.v) := by
  obtain ⟨hv, hnz, hlt⟩ := hnt
  obtain ⟨F, hacc⟩ := exists_flag_accepted v hv hnz hlt
  -- depth 1: the sorted representative
  obtain ⟨g1, hg1⟩ := depth1_cover4 (F.h 0) (accepted_h0_primitive F hacc) (accepted_two_le hnz F hacc) hacc.first_le
  obtain ⟨n1, hn1, hn1h⟩ := H.t1 _ hg1
  have hv1 : Primitive (g1.act v) := primitive_act hv g1
  have hnz1 := nz_act hnz g1
  have hlt1 : ML (g1.act v) < 1 / 4 := by rw [ML_act]; exact hlt
  obtain ⟨F1, hacc1, hF1⟩ := chain1_rep_flag4 hv hnz hlt F hacc g1 n1.rows (by rw [hn1h]; simp [hN])
  have hrows1 : ∀ i : Fin 3, i.val < 1 → F1.h i = n1.rows i := by
    intro i hi
    have : i = 0 := by ext; simp; omega
    rw [this]; exact hF1
  -- the child step
  obtain ⟨F1s, hacc1s, hrows1s, hpass1⟩ := child_step_signed4 hv1 hnz1 hlt1 F1 hacc1 n1 hrows1
  obtain ⟨lf, hlf, hy', hrel⟩ := H.t2 n1 hn1 _ hpass1
  have hP : PrefixEq F1s (setRow n1.rows 1 lf.y) 2 := prefixEq_child4 F1s n1 hrows1s lf.y hy'
  obtain ⟨F2, hacc2, -, hF2rows⟩ :=
    accepted_prefix hv1 hnz1 hlt1 F1s hacc1s.greedy (setRow n1.rows 1 lf.y) 2 (by norm_num) hP
  have hr0 : F2.h 0 = n1.rows 0 := by
    have := hF2rows 0 (by simp)
    rw [this]; simp [setRow]
  have hr1 : F2.h 1 = lf.y := by
    have := hF2rows 1 (by simp)
    rw [this]; simp [setRow]
  have hperp0 : dot (hN n1.rows 0) (g1.act v) = 0 := by
    have := F2.hv 0
    rw [hr0] at this; simpa [hN] using this
  have hperp1 : dot lf.y (g1.act v) = 0 := by
    have := F2.hv 1
    rwa [hr1] at this
  obtain ⟨hbqp, hcase⟩ := hrel
  rcases hcase with ⟨hk1, hcrit⟩ | ⟨hk0, hnc, hlines⟩
  · -- critical leaf: `K_2` lies in the critical lattice after `lf.g`
    left
    have := crit_link4 (hN n1.rows 0) lf hbqp (g1.act v) hperp0 hperp1 hcrit
    exact onCritTorus_of_act (g := lf.g.mul g1) (k := lf.ck) (by rw [act_mul]; exact this)
  · -- noncritical leaf: the line claim at `u = g1 v`
    obtain ⟨hW2, hd0, hd1, hc2⟩ := hnc
    have hW1 := n1.wok 1 le_rfl
    have hok1 : WitnessOk F2 1 (n1.wit 1).1 (n1.wit 1).2 :=
      ⟨hW1.1, fun i hi => by
        have : i = 0 := by ext; simp; omega
        subst this
        rw [hr0]; exact hW1.2 0 hi⟩
    have hok2 : WitnessOk F2 2 lf.x2 lf.W2 :=
      ⟨hW2, fun i hi => by
        have hi' : i.val = 0 ∨ i.val = 1 := by omega
        rcases hi' with h | h
        · have : i = 0 := Fin.ext h
          subst this; rw [hr0]; exact hd0
        · have : i = 1 := Fin.ext h
          subst this; rw [hr1]; exact hd1⟩
    have hwin := leaf_window_int hv1 F2 hacc2 (n1.wit 1).1 (n1.wit 1).2 hok1 (n1.wge 1 le_rfl) lf.x2 lf.W2 hok2 hc2
    have hG1 : leadMinor (gram F2) 1 = G1 n1 := by
      rw [leadMinor_one, hr0]; rfl
    have hG2 : leadMinor (gram F2) 2 = G2of n1 lf.y := by
      rw [leadMinor_two, hr0, hr1]; unfold G2of G1; simp [hN]
    have hmem : LeafWin4 n1 lf (dot (g1.act v) (g1.act v)) := by
      unfold LeafWin4 A1
      rw [hG1, hG2] at hwin
      exact hwin
    have hd : ∀ i j, i ≠ j → |g1.act v i| ≠ |g1.act v j| := by
      intro i j hij
      simp only [SP.act, abs_mul]
      rcases g1.hε i with a | a <;> rcases g1.hε j with b | b <;> simp [a, b] <;>
        exact hdist _ _ (fun h => hij (g1.σ.injective h))
    rcases hlines (g1.act v) hv1 hnz1 hd hperp0 hperp1 hmem with ⟨r, hr, g2, hg2⟩ | hge
    · right
      refine ⟨r, hr, g2.mul g1, ?_⟩
      rw [act_mul]; exact hg2
    · exact absurd hlt1 (not_lt.2 hge)

end L4S4
end LRSpectrumFull
