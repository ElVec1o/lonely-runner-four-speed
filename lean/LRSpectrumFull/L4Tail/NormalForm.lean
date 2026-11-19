/-
# L4Tail / NormalForm: bookkeeping that puts a four-speed vector on a normal-form critical line

`FourTails.four_tails` is stated for a line `U1v A B = (A, 2A, 3A, B)` or `U2v A B = (a, b, a+b, 2a+b)` with
coprime parameters `≥ 1`.  This module proves that every vector `v : Fin 4 → ℤ` with positive entries
lying on a critical torus *in the general sense* (a common integer factor `g ≥ 1`, a signed permutation of
the coordinates, and arbitrary integer parameters `A, B`) can be brought to that normal form:

* `SPS v w g` : `v i = g * (ε i * w (σ i))` with `g ≥ 1`, `σ` a permutation, `ε i = ±1`
  (`SPS.ML_eq`: `ML v = ML w`; `SPS.trans`; `SPS.injective`, `SPS.nonzero_of_pos`);
* `OnCritTorus v` : `SPS v (U1v A B) g` or `SPS v (U2v A B) g` for some integers `A B` and some `g`;
* `U2_to_pos`   : on the torus `U2` every line with nonzero entries is a signed permutation of a line with
  parameters `a', b' ≥ 1` (Weyl group of `B2`: two reflections and the sign change);
* `normal_form` : positive `v` on a critical torus is `SPS` to `U1v A B` or `U2v A B` with `A, B ≥ 1` coprime;
* `four_tails_of_torus` : `ML v < 1/4` then `ML v = j/(4j+2)`, `j ≥ 2`, `j ≠ 3`  (no distinctness needed);
* `crit_torus_list` : for distinct positive `v` on a critical torus with `ML v < 1/4`, the exact list of the
  quadruples covered: `g` times a signed permutation of `(1, 2, 3, 4j)`, `j ≥ 1`, or of `(a, b, a+b, 2a+b)`
  with `a, b ≥ 1` coprime, `a ≠ b`.

Not covered here (stated, not proved): that a vector produced by the finite tree lies on a critical torus,
the sporadic vector `(1, 3, 4, 14)` (not on a critical torus), distinctness/`gcd` reductions for repeated speeds.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4Tail.FourTails
import Mathlib.GroupTheory.Perm.Basic

namespace LRSpectrumFull
namespace L4Tail

/-! ## ML invariances, self-contained for any number of runners -/

theorem nf_gap_perm {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (v : Fin (k + 1) → ℤ) (t : ℝ) :
    gap (fun i => v (σ i)) t = gap v t := by
  apply le_antisymm
  · apply le_gap v t
    intro i
    simpa using gap_le (fun i => v (σ i)) t (σ.symm i)
  · apply le_gap (fun i => v (σ i)) t
    intro i
    exact gap_le v t (σ i)

theorem nf_ML_perm {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (v : Fin (k + 1) → ℤ) :
    ML (fun i => v (σ i)) = ML v := by
  have h : gap (fun i => v (σ i)) = gap v := funext (nf_gap_perm σ v)
  simp only [ML, h]

theorem nf_nid_sign (a ε : ℤ) (hε : ε = 1 ∨ ε = -1) (t : ℝ) :
    nearestIntDist (((ε * a : ℤ) : ℝ) * t) = nearestIntDist ((a : ℝ) * t) := by
  rcases hε with rfl | rfl
  · simp
  · have e : (((-1 * a : ℤ) : ℝ)) * t = -((a : ℝ) * t) := by push_cast; ring
    rw [e, nearestIntDist_neg]

theorem nf_gap_signs {k : ℕ} (ε v : Fin (k + 1) → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (t : ℝ) :
    gap (fun i => ε i * v i) t = gap v t := by
  apply le_antisymm
  · apply le_gap v t
    intro i
    have h := gap_le (fun i => ε i * v i) t i
    rwa [nf_nid_sign (v i) (ε i) (hε i) t] at h
  · apply le_gap (fun i => ε i * v i) t
    intro i
    rw [nf_nid_sign (v i) (ε i) (hε i) t]
    exact gap_le v t i

theorem nf_ML_signs {k : ℕ} (ε v : Fin (k + 1) → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ML (fun i => ε i * v i) = ML v := by
  have h : gap (fun i => ε i * v i) = gap v := funext (nf_gap_signs ε v hε)
  simp only [ML, h]

theorem nf_gap_smul {k : ℕ} (c : ℤ) (v : Fin (k + 1) → ℤ) (t : ℝ) :
    gap (fun i => c * v i) t = gap v ((c : ℝ) * t) := by
  unfold gap
  congr 1; funext i; congr 1; push_cast; ring

theorem nf_ML_smul {k : ℕ} (c : ℤ) (hc : c ≠ 0) (v : Fin (k + 1) → ℤ) :
    ML (fun i => c * v i) = ML v := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hrange : Set.range (gap (fun i => c * v i)) = Set.range (gap v) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨(c : ℝ) * t, (nf_gap_smul c v t).symm⟩
    · rintro ⟨s, rfl⟩
      refine ⟨s / (c : ℝ), ?_⟩
      rw [nf_gap_smul]; congr 1; field_simp
  unfold ML; rw [hrange]

/-! ## Signed permutation and scaling -/

/-- `v` is `g` times a signed permutation of `w`. -/
def SPS (v w : Fin 4 → ℤ) (g : ℤ) : Prop :=
  1 ≤ g ∧ ∃ (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤ),
    (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ i, v i = g * (ε i * w (σ i))

theorem SPS.refl (v : Fin 4 → ℤ) : SPS v v 1 :=
  ⟨le_rfl, 1, fun _ => 1, fun _ => Or.inl rfl, fun i => by simp⟩

theorem SPS.ML_eq {v w : Fin 4 → ℤ} {g : ℤ} (h : SPS v w g) : ML v = ML w := by
  obtain ⟨hg, σ, ε, hε, hv⟩ := h
  have e : v = fun i => g * (ε i * w (σ i)) := funext hv
  have h1 := nf_ML_smul g (by omega) (fun i => ε i * w (σ i))
  have h2 := nf_ML_signs ε (fun i => w (σ i)) hε
  have h3 := nf_ML_perm σ w
  rw [e]
  exact h1.trans (h2.trans h3)

theorem SPS.trans {v w u : Fin 4 → ℤ} {g h k : ℤ} (h1 : SPS v w g) (h2 : SPS w u h)
    (hk : k = g * h) : SPS v u k := by
  obtain ⟨hg, σ, ε, hε, hv⟩ := h1
  obtain ⟨hh, σ', ε', hε', hw⟩ := h2
  refine ⟨by rw [hk]; nlinarith, σ' * σ, fun i => ε i * ε' (σ i), ?_, ?_⟩
  · intro i
    rcases hε i with a | a <;> rcases hε' (σ i) with b | b <;> simp [a, b]
  · intro i
    rw [hv i, hw (σ i), hk]
    simp only [Equiv.Perm.mul_apply]
    ring

theorem SPS.nonzero_of_pos {v w : Fin 4 → ℤ} {g : ℤ} (hv : ∀ i, 0 < v i) (h : SPS v w g) :
    ∀ j, w j ≠ 0 := by
  obtain ⟨hg, σ, ε, hε, he⟩ := h
  intro j hj
  have h0 := hv (σ.symm j)
  rw [he (σ.symm j)] at h0
  simp [hj] at h0

theorem SPS.injective {v w : Fin 4 → ℤ} {g : ℤ} (hv : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (h : SPS v w g) : Function.Injective w := by
  obtain ⟨hg, σ, ε, hε, he⟩ := h
  intro j k hjk
  have hj := hv (σ.symm j)
  have hk := hv (σ.symm k)
  have ej := he (σ.symm j)
  have ek := he (σ.symm k)
  simp only [Equiv.apply_symm_apply] at ej ek
  have : σ.symm j = σ.symm k := by
    apply hinj
    rw [ej] at hj ⊢
    rw [ek, ← hjk] at hk ⊢
    rcases hε (σ.symm j) with a | a <;> rcases hε (σ.symm k) with b | b <;>
      rw [a] at hj ⊢ <;> rw [b] at hk ⊢ <;> first | rfl | (exfalso; nlinarith)
  exact σ.symm.injective this

/-! ## Sign reduction on `U1`, scaling, and the Weyl moves on `U2` -/

theorem SPS_U1_abs (A B : ℤ) : SPS (U1v A B) (U1v |A| |B|) 1 := by
  rcases le_or_gt 0 A with hA | hA <;> rcases le_or_gt 0 B with hB | hB
  · refine ⟨le_rfl, 1, ![1, 1, 1, 1], ?_, ?_⟩
    · intro i; fin_cases i <;> simp
    · intro i; fin_cases i <;> simp [U1v, abs_of_nonneg hA, abs_of_nonneg hB]
  · refine ⟨le_rfl, 1, ![1, 1, 1, -1], ?_, ?_⟩
    · intro i; fin_cases i <;> simp
    · intro i; fin_cases i <;> simp [U1v, abs_of_nonneg hA, abs_of_neg hB]
  · refine ⟨le_rfl, 1, ![-1, -1, -1, 1], ?_, ?_⟩
    · intro i; fin_cases i <;> simp
    · intro i; fin_cases i <;> simp [U1v, abs_of_neg hA, abs_of_nonneg hB]
  · refine ⟨le_rfl, 1, ![-1, -1, -1, -1], ?_, ?_⟩
    · intro i; fin_cases i <;> simp
    · intro i; fin_cases i <;> simp [U1v, abs_of_neg hA, abs_of_neg hB]

theorem SPS_U1_scale (d A B : ℤ) (hd : 1 ≤ d) : SPS (U1v (d * A) (d * B)) (U1v A B) d := by
  refine ⟨hd, 1, fun _ => 1, fun _ => Or.inl rfl, ?_⟩
  intro i; fin_cases i <;> simp [U1v] <;> ring

theorem SPS_U2_scale (d A B : ℤ) (hd : 1 ≤ d) : SPS (U2v (d * A) (d * B)) (U2v A B) d := by
  refine ⟨hd, 1, fun _ => 1, fun _ => Or.inl rfl, ?_⟩
  intro i; fin_cases i <;> simp [U2v] <;> ring

/-- Reflection in the short root: `(a, b) ↦ (-a, 2a+b)`. -/
theorem SPS_U2_s1 (a b : ℤ) : SPS (U2v a b) (U2v (-a) (2 * a + b)) 1 := by
  refine ⟨le_rfl, Equiv.swap 1 3, ![-1, 1, 1, 1], ?_, ?_⟩
  · intro i; fin_cases i <;> simp
  · intro i
    fin_cases i <;> simp [U2v, Equiv.swap_apply_def] <;> ring

/-- Reflection in the long root: `(a, b) ↦ (a+b, -b)`. -/
theorem SPS_U2_s2 (a b : ℤ) : SPS (U2v a b) (U2v (a + b) (-b)) 1 := by
  refine ⟨le_rfl, Equiv.swap 0 2, ![1, -1, 1, 1], ?_, ?_⟩
  · intro i; fin_cases i <;> simp
  · intro i
    fin_cases i <;> simp [U2v, Equiv.swap_apply_def] <;> ring

/-- Sign change: `(a, b) ↦ (-a, -b)`. -/
theorem SPS_U2_neg (a b : ℤ) : SPS (U2v a b) (U2v (-a) (-b)) 1 := by
  refine ⟨le_rfl, 1, fun _ => -1, fun _ => Or.inr rfl, ?_⟩
  intro i; fin_cases i <;> simp [U2v] <;> ring

theorem U2_to_pos_bpos (a b : ℤ) (hb : 0 < b) (h1 : a ≠ 0) (h3 : a + b ≠ 0) (h4 : 2 * a + b ≠ 0) :
    ∃ a' b' : ℤ, 1 ≤ a' ∧ 1 ≤ b' ∧ SPS (U2v a b) (U2v a' b') 1 := by
  rcases lt_or_gt_of_ne h1 with ha | ha
  · rcases lt_or_gt_of_ne h4 with h4n | h4p
    · rcases lt_or_gt_of_ne h3 with h3n | h3p
      · -- s1, s2, s1
        refine ⟨-(-a + (2 * a + b)) , 2 * (-a + (2 * a + b)) + -(2 * a + b), by omega, by omega, ?_⟩
        have e1 := SPS_U2_s1 a b
        have e2 := SPS_U2_s2 (-a) (2 * a + b)
        have e3 := SPS_U2_s1 (-a + (2 * a + b)) (-(2 * a + b))
        exact SPS.trans (g := 1) (h := 1) e1 (SPS.trans (g := 1) (h := 1) e2 e3 (by norm_num))
          (by norm_num)
      · -- s1, s2
        refine ⟨-a + (2 * a + b), -(2 * a + b), by omega, by omega, ?_⟩
        exact (SPS_U2_s1 a b).trans (SPS_U2_s2 (-a) (2 * a + b)) (by norm_num)
    · -- s1
      exact ⟨-a, 2 * a + b, by omega, by omega, SPS_U2_s1 a b⟩
  · exact ⟨a, b, by omega, by omega, SPS.refl _⟩

/-- Every line of the torus `U2` with nonzero entries is a signed permutation of a line with positive
parameters. -/
theorem U2_to_pos (a b : ℤ) (h1 : a ≠ 0) (h2 : b ≠ 0) (h3 : a + b ≠ 0) (h4 : 2 * a + b ≠ 0) :
    ∃ a' b' : ℤ, 1 ≤ a' ∧ 1 ≤ b' ∧ SPS (U2v a b) (U2v a' b') 1 := by
  rcases lt_or_gt_of_ne h2 with hb | hb
  · obtain ⟨a', b', ha', hb', h⟩ := U2_to_pos_bpos (-a) (-b) (by omega) (by omega) (by omega) (by omega)
    exact ⟨a', b', ha', hb', (SPS_U2_neg a b).trans h (by norm_num)⟩
  · exact U2_to_pos_bpos a b hb h1 h3 h4

theorem exists_coprime_split (A B : ℤ) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∃ d A' B' : ℤ, 1 ≤ d ∧ 1 ≤ A' ∧ 1 ≤ B' ∧ IsCoprime A' B' ∧ A = d * A' ∧ B = d * B' := by
  have hg : 0 < Int.gcd A B := Int.gcd_pos_of_ne_zero_left B (by omega)
  obtain ⟨g, A', B', hg0, hgcd, hA', hB'⟩ := Int.exists_gcd_one' hg
  refine ⟨g, A', B', by exact_mod_cast hg0, ?_, ?_, Int.isCoprime_iff_gcd_eq_one.mpr hgcd,
    by rw [hA']; ring, by rw [hB']; ring⟩
  · by_contra hlt
    have : A' ≤ 0 := by omega
    have hgpos : (0 : ℤ) < g := by exact_mod_cast hg0
    nlinarith
  · by_contra hlt
    have : B' ≤ 0 := by omega
    have hgpos : (0 : ℤ) < g := by exact_mod_cast hg0
    nlinarith

/-! ## The normal form -/

/-- `v` lies on one of the two critical tori, in the general sense: up to a common integer factor and a
signed permutation of the coordinates it is `(A, 2A, 3A, B)` or `(a, b, a+b, 2a+b)` for integers. -/
def OnCritTorus (v : Fin 4 → ℤ) : Prop :=
  ∃ A B g : ℤ, SPS v (U1v A B) g ∨ SPS v (U2v A B) g

theorem normal_form (v : Fin 4 → ℤ) (hpos : ∀ i, 0 < v i) (hT : OnCritTorus v) :
    ∃ A B g : ℤ, 1 ≤ A ∧ 1 ≤ B ∧ IsCoprime A B ∧ (SPS v (U1v A B) g ∨ SPS v (U2v A B) g) := by
  obtain ⟨A, B, g, h | h⟩ := hT
  · have nz := h.nonzero_of_pos hpos
    have hA : A ≠ 0 := by simpa [U1v] using nz 0
    have hB : B ≠ 0 := by simpa [U1v] using nz 3
    have h1 : SPS v (U1v |A| |B|) g := h.trans (SPS_U1_abs A B) (by ring)
    obtain ⟨d, A', B', hd, hA', hB', hc, eA, eB⟩ :=
      exists_coprime_split |A| |B| (by have := abs_pos.mpr hA; omega) (by have := abs_pos.mpr hB; omega)
    rw [eA, eB] at h1
    exact ⟨A', B', g * d, hA', hB', hc, Or.inl (h1.trans (SPS_U1_scale d A' B' hd) rfl)⟩
  · have nz := h.nonzero_of_pos hpos
    have n1 : A ≠ 0 := by simpa [U2v] using nz 0
    have n2 : B ≠ 0 := by simpa [U2v] using nz 1
    have n3 : A + B ≠ 0 := by simpa [U2v] using nz 2
    have n4 : 2 * A + B ≠ 0 := by simpa [U2v] using nz 3
    obtain ⟨a, b, ha, hb, hs⟩ := U2_to_pos A B n1 n2 n3 n4
    have h1 : SPS v (U2v a b) g := h.trans hs (by ring)
    obtain ⟨d, A', B', hd, hA', hB', hc, eA, eB⟩ := exists_coprime_split a b ha hb
    rw [eA, eB] at h1
    exact ⟨A', B', g * d, hA', hB', hc, Or.inr (h1.trans (SPS_U2_scale d A' B' hd) rfl)⟩

/-- **The hypotheses of `four_tails` hold for every positive vector on a critical torus.** -/
theorem four_tails_of_torus (v : Fin 4 → ℤ) (hpos : ∀ i, 0 < v i) (hT : OnCritTorus v)
    (hlt : ML v < 1 / 4) :
    ∃ j : ℤ, 2 ≤ j ∧ j ≠ 3 ∧ ML v = (j : ℝ) / (4 * (j : ℝ) + 2) := by
  obtain ⟨A, B, g, hA, hB, hc, h | h⟩ := normal_form v hpos hT
  · have hml := h.ML_eq
    rw [hml] at hlt ⊢
    exact four_tails _ ⟨A, B, hA, hB, hc, Or.inl rfl⟩ hlt
  · have hml := h.ML_eq
    rw [hml] at hlt ⊢
    exact four_tails _ ⟨A, B, hA, hB, hc, Or.inr rfl⟩ hlt

/-- **The exact list of the quadruples covered.**  A vector of four distinct positive integers on a critical
torus with `ML v < 1/4` is `g` times a signed permutation of `(1, 2, 3, 4j)` with `j ≥ 1`, or of
`(a, b, a+b, 2a+b)` with `a, b ≥ 1` coprime and `a ≠ b`; in both cases `ML v = j'/(4j'+2)`. -/
theorem crit_torus_list (v : Fin 4 → ℤ) (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v)
    (hT : OnCritTorus v) (hlt : ML v < 1 / 4) :
    (∃ g j : ℤ, 1 ≤ j ∧ SPS v (U1v 1 (4 * j)) g) ∨
    (∃ g a b : ℤ, 1 ≤ a ∧ 1 ≤ b ∧ IsCoprime a b ∧ a ≠ b ∧ SPS v (U2v a b) g) := by
  obtain ⟨A, B, g, hA, hB, hc, h | h⟩ := normal_form v hpos hT
  · left
    have hml := h.ML_eq
    rw [hml] at hlt
    by_cases hex : A = 1 ∧ 4 ∣ B
    · obtain ⟨hA1, j, hj⟩ := hex
      subst hA1
      subst hj
      exact ⟨g, j, by omega, h⟩
    · exact absurd hlt (not_lt.2 (U1_ge_quarter A B hA hB hc hex))
  · right
    have hi := h.injective hpos hinj
    refine ⟨g, A, B, hA, hB, hc, ?_, h⟩
    intro hAB
    have : (0 : Fin 4) = 1 := hi (by simp [U2v, hAB])
    exact absurd this (by decide)

/-! ## Non-vacuity of the hypotheses -/

theorem example_U1_ML : ML (U1v 1 4) = 1 / 5 := by
  have h := U1_exc_exact 1 le_rfl
  norm_num at h
  rw [h]

/-- `(40, 10, 30, 20)`: distinct positive, a signed (indeed unsigned) permutation of `10 · (1, 2, 3, 4)`. -/
theorem example_onTorus : OnCritTorus ![40, 10, 30, 20] ∧ (∀ i, 0 < (![40, 10, 30, 20] : Fin 4 → ℤ) i) ∧
    Function.Injective (![40, 10, 30, 20] : Fin 4 → ℤ) := by
  refine ⟨⟨1, 4, 10, Or.inl ⟨by norm_num,
    Equiv.ofBijective (![3, 0, 2, 1] : Fin 4 → Fin 4) (by decide),
    fun _ => 1, fun _ => Or.inl rfl, ?_⟩⟩, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [U1v, Equiv.ofBijective_apply]
  · intro i; fin_cases i <;> simp
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢

end L4Tail
end LRSpectrumFull
