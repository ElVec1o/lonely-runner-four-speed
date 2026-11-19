/-
# L4S5.AssembleB : `StreamHyp4` and `tree_complete4` for the real certificate, WITHOUT hypothesis

`Assemble` (superseded) took the line claim `LinesAll` as a hypothesis.  Here it is discharged: `nodes_all` from the split node
theorems `NodeS<i>`, `lines_chunks` from the 17 generated chunk theorems `linesChunk_<i>_<c>` (`LinesN<i>C<c>`; nodes 8 and 11 have
no records), `lines_all := lines_all_generic cert rfl nodes_all lines_chunks`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.  Do not import together with `Assemble`.
-/
import LRSpectrumFull.L4S5.NodeS0
import LRSpectrumFull.L4S5.NodeS1
import LRSpectrumFull.L4S5.NodeS2
import LRSpectrumFull.L4S5.NodeS3
import LRSpectrumFull.L4S5.NodeS4
import LRSpectrumFull.L4S5.NodeS5
import LRSpectrumFull.L4S5.NodeS6
import LRSpectrumFull.L4S5.NodeS7
import LRSpectrumFull.L4S5.NodeS8
import LRSpectrumFull.L4S5.NodeS9
import LRSpectrumFull.L4S5.NodeS10
import LRSpectrumFull.L4S5.NodeS11
import LRSpectrumFull.L4S5.NodeS12
import LRSpectrumFull.L4S5.NodeS13
import LRSpectrumFull.L4S5.NodeS14
import LRSpectrumFull.L4S5.LinesN0C0
import LRSpectrumFull.L4S5.LinesN1C0
import LRSpectrumFull.L4S5.LinesN1C1
import LRSpectrumFull.L4S5.LinesN2C0
import LRSpectrumFull.L4S5.LinesN3C0
import LRSpectrumFull.L4S5.LinesN4C0
import LRSpectrumFull.L4S5.LinesN4C1
import LRSpectrumFull.L4S5.LinesN4C2
import LRSpectrumFull.L4S5.LinesN4C3
import LRSpectrumFull.L4S5.LinesN5C0
import LRSpectrumFull.L4S5.LinesN6C0
import LRSpectrumFull.L4S5.LinesN7C0
import LRSpectrumFull.L4S5.LinesN9C0
import LRSpectrumFull.L4S5.LinesN10C0
import LRSpectrumFull.L4S5.LinesN12C0
import LRSpectrumFull.L4S5.LinesN13C0
import LRSpectrumFull.L4S5.LinesN14C0
import LRSpectrumFull.L4S5.LinesGlue

namespace LRSpectrumFull
namespace L4S5

open LRSpectrumFull.L4S3 LRSpectrumFull.L4S4

noncomputable section

theorem nodes_all : ∀ i < 15, nodeB (t1At i) (nodeChunks i) = true := by
  intro i hi
  interval_cases i
  exacts [node_0, node_1, node_2, node_3, node_4, node_5, node_6, node_7, node_8, node_9, node_10, node_11,
    node_12, node_13, node_14]

theorem linesChunk_empty (r : T1Rec4) (ch : Chunk) (h : ch.cnt = 0) : linesChunkB r ch = true := by
  simp [linesChunkB, h]

theorem lines_chunks : ∀ i < 15, ∀ ch ∈ nodeChunks i, linesChunkB (t1At i) ch = true := by
  intro i hi ch hch
  interval_cases i
  · rw [nc_0, List.mem_singleton] at hch; subst hch; exact linesChunk_0_0
  · rw [nc_1] at hch
    rcases List.mem_cons.1 hch with rfl | h
    · exact linesChunk_1_0
    · rw [List.mem_singleton] at h; subst h; exact linesChunk_1_1
  · rw [nc_2, List.mem_singleton] at hch; subst hch; exact linesChunk_2_0
  · rw [nc_3, List.mem_singleton] at hch; subst hch; exact linesChunk_3_0
  · rw [nc_4] at hch
    rcases List.mem_cons.1 hch with rfl | h
    · exact linesChunk_4_0
    rcases List.mem_cons.1 h with rfl | h
    · exact linesChunk_4_1
    rcases List.mem_cons.1 h with rfl | h
    · exact linesChunk_4_2
    rw [List.mem_singleton] at h; subst h; exact linesChunk_4_3
  · rw [nc_5, List.mem_singleton] at hch; subst hch; exact linesChunk_5_0
  · rw [nc_6, List.mem_singleton] at hch; subst hch; exact linesChunk_6_0
  · rw [nc_7, List.mem_singleton] at hch; subst hch; exact linesChunk_7_0
  · rw [nc_8, List.mem_singleton] at hch; subst hch; exact linesChunk_empty _ _ rfl
  · rw [nc_9, List.mem_singleton] at hch; subst hch; exact linesChunk_9_0
  · rw [nc_10, List.mem_singleton] at hch; subst hch; exact linesChunk_10_0
  · rw [nc_11, List.mem_singleton] at hch; subst hch; exact linesChunk_empty _ _ rfl
  · rw [nc_12, List.mem_singleton] at hch; subst hch; exact linesChunk_12_0
  · rw [nc_13, List.mem_singleton] at hch; subst hch; exact linesChunk_13_0
  · rw [nc_14, List.mem_singleton] at hch; subst hch; exact linesChunk_14_0

/-- All stored leaf records, in the order of the data. -/
def allLeaves : List LeafRec4 :=
  (List.range 15).flatMap fun i => (nodeChunks i).flatMap fun ch =>
    (List.range ch.cnt).map fun j => decLeaf (recOf ch.bl j)

/-- The certificate. -/
def cert : Certificate4 := ⟨(List.range 15).map t1At, allLeaves, t5Data⟩

/-- The line claim for every noncritical stored record. -/
def LinesAll : Prop :=
  ∀ i < 15, ∀ hc : T1Chk (t1At i), ∀ ch ∈ nodeChunks i, ∀ j < ch.cnt,
    (decLeaf (recOf ch.bl j)).kind = 0 → LinesOk cert ((t1At i).toNode hc) (decLeaf (recOf ch.bl j))

/-- **The line claim is discharged** : the line claim holds for the real certificate. -/
theorem lines_all : LinesAll := lines_all_generic cert rfl nodes_all lines_chunks

theorem streamHyp4_of_lines (hL : LinesAll) : StreamHyp4 cert R1 := by
  refine ⟨t1_hyp, ?_⟩
  rintro n ⟨i, hi, hc, rfl⟩ y hp
  obtain ⟨ch, hch, j, hj, ht, hok⟩ := node_sound (t1At i) hc (nodeChunks i) (nodes_all i hi) y hp
  refine ⟨decLeaf (recOf ch.bl j), ?_, fun a => ?_, leafRel_of_ok cert _ hc _ hok (hL i hi hc ch hch j hj)⟩
  · unfold cert allLeaves
    simp only [List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨i, hi, ch, hch, j, hj, rfl⟩
  · exact (hok.1 a).trans (congrFun ht a)

/-- `StreamHyp4` for the real certificate, no hypothesis. -/
theorem streamHyp4_real : StreamHyp4 cert R1 := streamHyp4_of_lines lines_all

/-- `tree_complete4` for the real certificate, no open hypothesis. -/
theorem tree_complete4_real (v : V4) (hnt : NearTight v) (hdist : ∀ i j, i ≠ j → |v i| ≠ |v j|) :
    L4Tail.OnCritTorus v ∨ (∃ r ∈ cert.t5, ∃ g : SP, g.act v = r.v) :=
  tree_complete4 streamHyp4_real v hnt hdist

end

end L4S5
end LRSpectrumFull
