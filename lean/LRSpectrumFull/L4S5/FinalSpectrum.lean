/-
# L4S5.FinalSpectrum : the four-speed spectrum, from the tree theorem as an explicit hypothesis `hT`

`four_speed_spectrum_of_tree` : if the tree theorem `TreeThm` holds (it is `tree_complete4_real`, proved without hypothesis
in `L4S5.AssembleB`), then for every four distinct positive integer speeds `v` with `ML v < 1/4`,
`ML v = j/(4j+2)` for an integer `j ≥ 2`, `j ≠ 3`.

Cases: the tree output is `OnCritTorus w` (then `four_tails_of_torus`) or a stored residual tuple, and
`t5Data = [(1,2,3,8), (1,3,4,14)]`: `ML (1,2,3,8) = 2/9` (`U1_exc_exact 2`, `j = 4`) and `ML (1,3,4,14) = 4/17`
(`L4Tail.ML_1_3_4_14`, `j = 8`), both transported by `ML_act`.
Hypotheses of the normalisation: a vector of positive integers is `d` times a primitive vector (`exists_prim`),
`ML (d w) = ML w` (`nf_ML_smul`); distinct positive entries stay distinct and positive.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S5.Data
import LRSpectrumFull.L4Tail.Sporadic
import LRSpectrumFull.L4S4.Records4

namespace LRSpectrumFull
namespace L4S5

open LRSpectrumFull.L4S3 LRSpectrumFull.L4S4

/-- The tree theorem, as a hypothesis for the development: every near-tight vector with distinct absolute entries
is on a critical torus or is a signed permutation of a stored residual tuple. -/
def TreeThm : Prop :=
  ∀ v : V4, NearTight v → (∀ i j, i ≠ j → |v i| ≠ |v j|) →
    L4Tail.OnCritTorus v ∨ (∃ r ∈ t5Data, ∃ g : SP, g.act v = r.v)

/-- **E11a.**  A vector of positive integers is `d ≥ 1` times a primitive vector of positive integers. -/
theorem exists_prim (v : V4) (hpos : ∀ i, 0 < v i) :
    ∃ d : ℤ, 1 ≤ d ∧ ∃ w : V4, Primitive w ∧ (∀ i, 0 < w i) ∧ (∀ i, v i = d * w i) := by
  set d : ℤ := Finset.univ.gcd v with hd
  have hdv : ∀ i, d ∣ v i := fun i => Finset.gcd_dvd (Finset.mem_univ i)
  have hd0 : d ≠ 0 := by
    intro h0
    have := (Finset.gcd_eq_zero_iff.1 h0) 0 (Finset.mem_univ _)
    exact (hpos 0).ne' this
  have hdn : 0 ≤ d := Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd)
  have hd1 : 1 ≤ d := by omega
  choose w hw using hdv
  refine ⟨d, hd1, w, ?_, ?_, hw⟩
  · intro e he
    have h1 : ∀ i, d * e ∣ v i := by
      intro i
      rw [hw i]
      exact mul_dvd_mul_left d (he i)
    have h2 : d * e ∣ d := Finset.dvd_gcd (fun i _ => h1 i)
    have h3 : d * e ∣ d * 1 := by simpa using h2
    have h4 : e ∣ 1 := (mul_dvd_mul_iff_left hd0).1 h3
    exact Int.isUnit_iff.mp (isUnit_of_dvd_one h4)
  · intro i
    have := hpos i
    rw [hw i] at this
    by_contra hneg
    have : d * w i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hdn (by omega)
    omega

/-- **The four-speed spectrum**, from the tree theorem. -/
theorem four_speed_spectrum_of_tree (hT : TreeThm) (v : Fin 4 → ℤ) (hpos : ∀ i, 0 < v i)
    (hinj : Function.Injective v) (hlt : ML v < 1 / 4) :
    ∃ j : ℤ, 2 ≤ j ∧ j ≠ 3 ∧ ML v = (j : ℝ) / (4 * (j : ℝ) + 2) := by
  obtain ⟨d, hd1, w, hprim, hwpos, hvw⟩ := exists_prim v hpos
  have hv : v = fun i => d * w i := funext hvw
  have hML : ML v = ML w := by
    rw [hv]; exact L4Tail.nf_ML_smul d (by omega) w
  rw [hML] at hlt ⊢
  have hnz : ∀ i, w i ≠ 0 := fun i => (hwpos i).ne'
  have hdist : ∀ i j, i ≠ j → |w i| ≠ |w j| := by
    intro i j hij h
    rw [abs_of_pos (hwpos i), abs_of_pos (hwpos j)] at h
    apply hij
    apply hinj
    rw [hvw i, hvw j, h]
  rcases hT w ⟨hprim, hnz, hlt⟩ hdist with hT' | ⟨r, hr, g, hg⟩
  · exact L4Tail.four_tails_of_torus w hwpos hT' hlt
  · have hml : ML w = ML r.v := by rw [← hg, ML_act]
    simp only [t5Data, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨4, by norm_num, by norm_num, ?_⟩
      have e : (![1, 2, 3, 8] : Fin 4 → ℤ) = L4Tail.U1v 1 (4 * 2) := by
        funext i; fin_cases i <;> simp [L4Tail.U1v]
      rw [hml]
      show ML (![1, 2, 3, 8] : Fin 4 → ℤ) = _
      rw [e, L4Tail.U1_exc_exact 2 (by norm_num)]
      norm_num
    · refine ⟨8, by norm_num, by norm_num, ?_⟩
      rw [hml]
      show ML (![1, 3, 4, 14] : Fin 4 → ℤ) = _
      rw [L4Tail.ML_1_3_4_14]
      norm_num

/-- **Attainment**: every `j ≥ 2`, `j ≠ 3` occurs, by four distinct positive integer speeds. -/
theorem four_speed_attained (j : ℤ) (hj : 2 ≤ j) (hj3 : j ≠ 3) :
    ∃ v : Fin 4 → ℤ, (∀ i, 0 < v i) ∧ Function.Injective v ∧ ML v = (j : ℝ) / (4 * (j : ℝ) + 2) := by
  obtain ⟨v, h1, h2, -, h4⟩ := L4Tail.four_occurs j hj hj3
  exact ⟨v, h1, h2, h4⟩

end L4S5
end LRSpectrumFull
