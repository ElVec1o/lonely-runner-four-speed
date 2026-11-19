/-
# L4S3.Discharge : `FlagGeometry` from flag existence alone

Four of the five fields of `FlagGeometry` (`Dq_minors`, `ratio34`, `covolume`, `stage_dist`) are now
theorems (`Minors`, `Ratio34`, `Dist`).  The remaining ingredient `FlagExists` (the greedy flag with saturation) is the
theorem `L4S3.flag_exists` (`GreedyFinal`), so `FlagGeometry` holds unconditionally.  `flagGeometry_of_exists` builds the structure
`FlagGeometry` from it, so that `stage_bound`, `stage_prune`, `leaf_strand`, `window_lo` of
`Skeleton.lean` hold from `FlagExists` only.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.Skeleton
import LRSpectrumFull.L4S3.Dist
import LRSpectrumFull.L4S3.Minors
import LRSpectrumFull.L4S3.Ratio34

namespace LRSpectrumFull
namespace L4S3

/-- The one remaining hypothesis: existence of a saturated greedy flag for a primitive `v`. -/
def FlagExists : Prop := ∀ v : V4, Primitive v → ∃ F : FlagData v, Greedy v F.h

theorem flagGeometry_of_exists (h : FlagExists) : FlagGeometry where
  flag_exists := h
  Dq_minors := fun v F i => Dq_minors_thm v F i
  ratio34 := fun v F hg i => ratio34_thm F hg i
  covolume := fun v F hv => covolume_thm v F hv
  stage_dist := fun v F k x hv hx => stage_dist_thm v F k x hv hx

/-- Stage bound from `FlagExists` alone. -/
theorem stage_bound_of_exists (h : FlagExists) (v : V4) (F : FlagData v) (k : ℕ) (x : Fin 4 → ℝ)
    (hv : Primitive v) (hx : StageWitness F k x) :
    fmin x - 1 / 2 * Real.sqrt (Sk F k) ≤ ML v :=
  stage_bound (flagGeometry_of_exists h) v F k x hv hx

end L4S3
end LRSpectrumFull
