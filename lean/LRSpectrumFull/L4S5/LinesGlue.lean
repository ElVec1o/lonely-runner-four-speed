/-
# L4S5.LinesGlue : from the chunk theorems to the line claim of every stored noncritical record

`lines_all_generic` : if every node passes `nodeB` (child list and leaf records, `NodeS0..NodeS14`) and every chunk of every
node passes `linesChunkB` (the generated `LinesN<i>C<c>` theorems), then `LinesOk` holds for every noncritical stored record.
`AssembleB.lines_all` is this statement for `cert` (`cert.t5 = t5Data` by `rfl`); the one-line instantiation is
`fun .. => lines_all_generic cert rfl nodes_all hchunks`, written in the final assembly, not here, so that this module does
not import the node kernel theorems.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S5.LinesChunk

namespace LRSpectrumFull
namespace L4S5

open LRSpectrumFull.L4S3 LRSpectrumFull.L4S4

noncomputable section

theorem leafOk_of_nodeB (r : T1Rec4) (cs : List Chunk) (h : nodeB r cs = true) (ch : Chunk) (hch : ch ∈ cs) :
    ∀ j < ch.cnt, LeafOk r (decLeaf (recOf ch.bl j)) := by
  intro j hj
  simp only [nodeB, Bool.and_eq_true, List.all_eq_true] at h
  have hc := h.2 ch hch
  simp only [chunkB, Bool.and_eq_true, List.all_eq_true] at hc
  have := hc.2 j (List.mem_range.2 hj)
  simpa [leafB] using this

theorem lines_all_generic (C : Certificate4) (hC : C.t5 = t5Data)
    (hn : ∀ i < 15, nodeB (t1At i) (nodeChunks i) = true)
    (hl : ∀ i < 15, ∀ ch ∈ nodeChunks i, linesChunkB (t1At i) ch = true) :
    ∀ i < 15, ∀ hc : T1Chk (t1At i), ∀ ch ∈ nodeChunks i, ∀ j < ch.cnt,
      (decLeaf (recOf ch.bl j)).kind = 0 → LinesOk C ((t1At i).toNode hc) (decLeaf (recOf ch.bl j)) :=
  fun i hi hc ch hch j hj hk =>
    linesChunk_sound C hC (t1At i) hc ch (hl i hi ch hch) (leafOk_of_nodeB _ _ (hn i hi) ch hch) j hj hk

end

end L4S5
end LRSpectrumFull
