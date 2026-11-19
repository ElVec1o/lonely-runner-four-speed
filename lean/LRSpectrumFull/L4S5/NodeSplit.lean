/-
# L4S5.NodeSplit : splitting of the node kernel theorems (memory)

`nodeB` was checked in one kernel theorem per node (peak 7 to 9 GB).  Here `chunkB` is cut into its child-stream part
(`goB`) and the leaf checks, and the leaf checks into ranges `leafRangeB r ch lo hi`; `leafRange_trans` glues adjacent ranges and
`chunkB_of_parts` reassembles `chunkB`.  The generated modules `NodeS<i>` use only these.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S5.ChunkAt

namespace LRSpectrumFull
namespace L4S5

open LRSpectrumFull.L4S3 LRSpectrumFull.L4S4

noncomputable section

/-- The leaf checks on the records `lo ≤ j < hi` of a chunk. -/
def leafRangeB (r : T1Rec4) (ch : Chunk) (lo hi : ℕ) : Bool :=
  (List.range (hi - lo)).all fun i => leafB r (recOf ch.bl (lo + i))

theorem leafRange_sound (r : T1Rec4) (ch : Chunk) (lo hi : ℕ) (h : leafRangeB r ch lo hi = true) (j : ℕ)
    (h1 : lo ≤ j) (h2 : j < hi) : leafB r (recOf ch.bl j) = true := by
  unfold leafRangeB at h
  rw [List.all_eq_true] at h
  have := h (j - lo) (List.mem_range.2 (by omega))
  have e : lo + (j - lo) = j := by omega
  rwa [e] at this

theorem leafRange_trans {r : T1Rec4} {ch : Chunk} {lo mid hi : ℕ} (h1 : leafRangeB r ch lo mid = true)
    (h2 : leafRangeB r ch mid hi = true) : leafRangeB r ch lo hi = true := by
  unfold leafRangeB
  rw [List.all_eq_true]
  intro i hi'
  rw [List.mem_range] at hi'
  by_cases hm : lo + i < mid
  · exact leafRange_sound r ch lo mid h1 (lo + i) (by omega) hm
  · exact leafRange_sound r ch mid hi h2 (lo + i) (by omega) (by omega)

theorem chunkB_of_parts (r : T1Rec4) (ch : Chunk)
    (hg : goB (ctxR r) (cands (ctxR r) ch.lo ch.hi) (stOf ch.bl ch.cnt) = true)
    (hl : leafRangeB r ch 0 ch.cnt = true) : chunkB r ch = true := by
  unfold chunkB
  rw [Bool.and_eq_true]
  refine ⟨hg, ?_⟩
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hj
  exact leafRange_sound r ch 0 ch.cnt hl j (Nat.zero_le _) hj

end

end L4S5
end LRSpectrumFull
