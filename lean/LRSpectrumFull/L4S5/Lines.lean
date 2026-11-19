/-
# L4S5.Lines : the line loop of a noncritical leaf (the Boolean checker and its kernel probe)

For a noncritical leaf `lf` (`K_2 = Z k0 + Z k1`) the lines are `u = x k0 + z k1` with `gcd(x, z) = 1`, `z ≥ 0` (`z = 0`: only
`x = 1`), in the window `WinInt` and with nonzero pairwise distinct absolute entries.  Each must have a time of the
list `TL` (387 reduced `a/q`, `q ≤ 50`) with `TimeOk`, or be a stored residual tuple (`T5`, compared through the sorted
absolute values).  The loop box is `z ≤ Z`, `|x| ≤ X` with `nmax = (4 W2² G2 - 1) / A2²`, `Z = isqrt(a nmax / D)`, `X = isqrt(d nmax / D)`.

`leafLinesB` is the executable specification; `lines_probe_*` are kernel runs on real leaves (time and memory in the report).
The soundness `leafLinesB r lf = true → LinesOk cert n lf` is NOT proved here (see `LinesSound`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S5.CheckT1

namespace LRSpectrumFull
namespace L4S5

open Matrix Finset LRSpectrumFull.L4S3 LRSpectrumFull.L4S4

noncomputable section

instance (s : V4) (a q : ℤ) : Decidable (TimeOk s a q) := by unfold TimeOk; infer_instance
instance (G1 G2 A1 W1 A2 W2 m : ℤ) : Decidable (WinInt G1 G2 A1 W1 A2 W2 m) := by unfold WinInt; infer_instance

/-- The time list: reduced `a/q`, `2 ≤ q ≤ 50`, `1 ≤ a ≤ q/2`, ordered by `q` then `a`. -/
def TL : List (ℤ × ℤ) :=
  (List.range 49).flatMap fun k =>
    ((List.range ((k + 2) / 2)).map fun a => (((a + 1 : ℕ) : ℤ), ((k + 2 : ℕ) : ℤ))).filter fun p => Int.gcd p.1 p.2 == 1

def sortAbs (u : V4) : List ℤ := List.insertionSort (fun a b => decide (a ≤ b)) [|u 0|, |u 1|, |u 2|, |u 3|]

def t5B (u : V4) : Bool := t5Data.any fun r => sortAbs u == [r.v 0, r.v 1, r.v 2, r.v 3]

def lineVec (lf : LeafRec4) (x z : ℤ) : V4 := fun i => x * lf.k 0 i + z * lf.k 1 i

/-- One line `(x, z)` of the leaf `lf` under the node record `r`. -/
def lineB (r : T1Rec4) (lf : LeafRec4) (x z : ℤ) : Bool :=
  let u := lineVec lf x z
  !((Int.gcd x z == 1) &&
  decide (WinInt (dot r.h r.h) (dot r.h r.h * dot lf.y lf.y - dot r.h lf.y ^ 2) (4 * wMin r.x1 r.W1 - r.W1) r.W1
    (4 * wMin lf.x2 lf.W2 - lf.W2) lf.W2 (dot u u)) &&
  decide (∀ i, u i ≠ 0) && decide (∀ i j, i ≠ j → |u i| ≠ |u j|)) ||
  (TL.any (fun p => decide (TimeOk u p.1 p.2)) || t5B u)

/-- The loop of a noncritical leaf (with the checks `D > 0` and `A2 > 0` the bounds need). -/
def leafLinesB (r : T1Rec4) (lf : LeafRec4) : Bool :=
  let a := dot (lf.k 0) (lf.k 0)
  let b := dot (lf.k 0) (lf.k 1)
  let d := dot (lf.k 1) (lf.k 1)
  let D := a * d - b ^ 2
  let G2 := dot r.h r.h * dot lf.y lf.y - dot r.h lf.y ^ 2
  let A2 := 4 * wMin lf.x2 lf.W2 - lf.W2
  let nmax := (4 * lf.W2 ^ 2 * G2 - 1) / A2 ^ 2
  let Z := isqrtI (a * nmax / D)
  let X := isqrtI (d * nmax / D)
  decide (0 < D) && decide (0 < A2) &&
  (List.range (Z + 1).toNat).all fun zn =>
    (if zn = 0 then [1] else rngZ (-X) X).all fun x => lineB r lf x zn

/-- Probe: every noncritical leaf record of a chunk passes the line loop (kernel evaluation). -/
def linesChunkB (r : T1Rec4) (ch : Chunk) : Bool :=
  (List.range ch.cnt).all fun j => decide ((decLeaf (recOf ch.bl j)).kind ≠ 0) || leafLinesB r (decLeaf (recOf ch.bl j))


/-- Probe on records `lo ≤ j < hi` only. -/
def linesRangeB (r : T1Rec4) (ch : Chunk) (lo hi : ℕ) : Bool :=
  (List.range (hi - lo)).all fun i => decide ((decLeaf (recOf ch.bl (lo + i))).kind ≠ 0) || leafLinesB r (decLeaf (recOf ch.bl (lo + i)))

end

end L4S5
end LRSpectrumFull
