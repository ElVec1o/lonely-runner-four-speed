/-
# L4S4.Window : the last diagonal entry `μ_3² = |v|² / G_2` of a four-speed flag

`leadMinor_three`, `Dq2_eq` : `Dq 2 = |v|² / G_2` (covolume identity at the last stage).  (the integer window itself is `LeafWin4` in `Leaf4.lean`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S4.Chain
import LRSpectrumFull.L4S3.Accepted

namespace LRSpectrumFull
namespace L4S4

open Finset LRSpectrumFull.L4S3

theorem leadMinor_three (M : Matrix (Fin 3) (Fin 3) ℤ) : leadMinor M 3 = M.det := by
  unfold leadMinor
  congr 1
  ext a b
  simp [a.2, b.2]

theorem Dq2_eq {v : V4} (F : FlagData v) (hv : Primitive v) :
    F.Dq 2 = (dot v v : ℚ) / (leadMinor (gram F) 2 : ℚ) := by
  have h : F.Dq 2 = (leadMinor (gram F) 3 : ℚ) / (leadMinor (gram F) 2 : ℚ) := Dq_minors_thm v F 2
  rw [h, leadMinor_three, gram_det_eq_normsq F hv]

end L4S4
end LRSpectrumFull
