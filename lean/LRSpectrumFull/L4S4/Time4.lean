/-
# L4S4.Time4 : soundness of the time list (`time_ok`)

`TimeOk s a q` is the integer test of the certificate (`r_i = (|s_i| a) mod q`, `4 min(r_i, q - r_i) ≥ q`, `q ≥ 1`);
`timeOk_sound` : `TimeOk s a q → 1/4 ≤ ML s`.  This is the "witness" half of the line stage: the line checkers (`L4S5`)
only have to show `TimeOk` for some `(a, q)` of the stored list `TL` (387 times) or to find the tuple in `T5`; the
`1/4 ≤ ML u` conclusion of `LinesOk` then follows from this lemma and the signed-permutation invariance `ML_act`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S4.Induct4

namespace LRSpectrumFull
namespace L4S4

open LRSpectrumFull.L4S3

/-- The integer time test of the certificate. -/
def TimeOk (s : V4) (a q : ℤ) : Prop :=
  0 < q ∧ ∀ i, q ≤ 4 * min ((|s i| * a) % q) (q - (|s i| * a) % q)

theorem timeOk_sound (s : V4) (a q : ℤ) (h : TimeOk s a q) : (1 : ℝ) / 4 ≤ ML s := by
  obtain ⟨hq, h⟩ := h
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hgap : (1 : ℝ) / 4 ≤ gap s ((a : ℝ) / q) := by
    apply le_gap
    intro i
    have e : nearestIntDist ((s i : ℝ) * ((a : ℝ) / q)) = nearestIntDist (((|s i| * a : ℤ) : ℝ) / q) := by
      rcases abs_choice (s i) with hh | hh
      · rw [hh]; congr 1; push_cast; ring
      · rw [hh]
        push_cast
        rw [show ((-(s i : ℝ)) * a / q) = -((s i : ℝ) * ((a : ℝ) / q)) by ring, nearestIntDist_neg]
    rw [e, nd_rat _ _ hq, le_div_iff₀ hqr]
    have : (q : ℝ) ≤ 4 * ((min ((|s i| * a) % q) (q - (|s i| * a) % q) : ℤ) : ℝ) := by exact_mod_cast h i
    linarith
  exact hgap.trans (le_csSup (bddAbove_range_gap s) ⟨_, rfl⟩)

/-- Negative control: `s = (1,2,3,8)` has no witness at `a/q = 1/3` (`2 · 1 mod 3 = 2`, `4 · min(2, 1) = 4 ≥ 3`, but
`3 · 1 mod 3 = 0`), and the test is false there. -/
theorem planted_time_bad : ¬ TimeOk ![1, 2, 3, 8] 1 3 := by
  intro h
  have := h.2 2
  revert this
  decide +kernel

end L4S4
end LRSpectrumFull
