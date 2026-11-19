/-
# L4S5.ChunkAt : chunk selector (node 4 is checked chunk by chunk to keep each kernel run under 8 GB)
-/
import LRSpectrumFull.L4S5.CheckT1

namespace LRSpectrumFull
namespace L4S5

def chunkAt (i c : ℕ) : Chunk := (nodeChunks i).getD c ⟨0, 0, 0, []⟩

theorem node4_chunks : nodeChunks 4 = [chunkAt 4 0, chunkAt 4 1, chunkAt 4 2, chunkAt 4 3] := rfl

end L4S5
end LRSpectrumFull
