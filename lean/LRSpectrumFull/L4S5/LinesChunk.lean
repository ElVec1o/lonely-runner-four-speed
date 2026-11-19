/-
# L4S5.LinesChunk : gluing of range theorems (chunking)

`linesRangeB r ch lo hi = true` is a kernel theorem on records `lo ≤ j < hi` of a chunk.  `linesRange_trans` glues two adjacent
ranges, `linesChunk_of_range` turns the range `[0, cnt)` into `linesChunkB`, and `linesChunk_sound` is the pointwise reading:
every noncritical record of a chunk with `linesChunkB = true` passes `leafLinesB`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S5.LinesSound
import LRSpectrumFull.L4S5.ChunkAt

namespace LRSpectrumFull
namespace L4S5

open LRSpectrumFull.L4S3 LRSpectrumFull.L4S4

noncomputable section

theorem linesRange_sound (r : T1Rec4) (ch : Chunk) (lo hi : ℕ) (h : linesRangeB r ch lo hi = true) (j : ℕ)
    (h1 : lo ≤ j) (h2 : j < hi) :
    (decide ((decLeaf (recOf ch.bl j)).kind ≠ 0) || leafLinesB r (decLeaf (recOf ch.bl j))) = true := by
  unfold linesRangeB at h
  rw [List.all_eq_true] at h
  have := h (j - lo) (List.mem_range.2 (by omega))
  have e : lo + (j - lo) = j := by omega
  rwa [e] at this

theorem linesRange_trans {r : T1Rec4} {ch : Chunk} {lo mid hi : ℕ} (h1 : linesRangeB r ch lo mid = true)
    (h2 : linesRangeB r ch mid hi = true) : linesRangeB r ch lo hi = true := by
  unfold linesRangeB
  rw [List.all_eq_true]
  intro i hi'
  rw [List.mem_range] at hi'
  by_cases hm : lo + i < mid
  · exact linesRange_sound r ch lo mid h1 (lo + i) (by omega) hm
  · exact linesRange_sound r ch mid hi h2 (lo + i) (by omega) (by omega)

theorem linesChunk_of_range {r : T1Rec4} {ch : Chunk} (h : linesRangeB r ch 0 ch.cnt = true) :
    linesChunkB r ch = true := by
  unfold linesChunkB
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hj
  exact linesRange_sound r ch 0 ch.cnt h j (by omega) hj

theorem linesChunk_sound (C : Certificate4) (hC : C.t5 = t5Data) (r : T1Rec4) (c : T1Chk r) (ch : Chunk)
    (h : linesChunkB r ch = true) (hok : ∀ j < ch.cnt, LeafOk r (decLeaf (recOf ch.bl j))) (j : ℕ) (hj : j < ch.cnt)
    (hk : (decLeaf (recOf ch.bl j)).kind = 0) : LinesOk C (r.toNode c) (decLeaf (recOf ch.bl j)) := by
  unfold linesChunkB at h
  rw [List.all_eq_true] at h
  have := h j (List.mem_range.2 hj)
  rw [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h' | h'
  · exact absurd hk h'
  · exact leafLinesB_sound C hC r c _ (hok j hj).2.1 h'

end

end L4S5
end LRSpectrumFull
