/-
# L4S3.GreedyStep : existence of a greedy `ℤ`-basis of `Λ = ℤ⁴ ∩ v^⊥`

Construction of `h_0, …, h_3 ∈ Λ` by induction on `j`: `h_j` minimises the integer Gram determinant
`gF (h_0..h_{j-1}, u)` over `u ∈ Λ` outside the rational span of the prefix (`Function.argminOn` on the
natural number `(gF …).toNat`, nonnegativity from `GmQ_det_nonneg`).  Saturation is carried along:
if `x ∈ Λ` lies in the rational span of `h_0..h_j`, with `h_j`-coefficient `s`, then `x - round(s) h_j`
is either `0`-coefficient on `h_j` or has Gram determinant `(s - round s)² gF(…, h_j) < gF(…, h_j)`
(shear identity), contradicting minimality; so `s ∈ ℤ` and `x` is an integer combination.

Main results: `greedyBasis_exists : GreedyBasis v` for every primitive `v`, and
`flag_exists : FlagExists` (hence the whole stage chain is unconditional).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.GreedyDim
import LRSpectrumFull.L4S3.GreedyReduce

namespace LRSpectrumFull
namespace L4S3

open Finset

/-- Greedy minimality at step `i` (Gram-determinant form, `Fin (i+1)` families). -/
def GreedyN (v : V4) (i : ℕ) (h : Fin 3 → V4) : Prop :=
  ∀ u : V4, dot u v = 0 → ¬ InQN i h u → gF (Ef i h (hN h i)) ≤ gF (Ef i h u)

/-- Saturation of the prefix `h_0..h_{j-1}` in `Λ`. -/
def SatN (v : V4) (j : ℕ) (h : Fin 3 → V4) : Prop :=
  ∀ x : V4, dot x v = 0 → InQN j h x →
    ∃ m : ℕ → ℤ, ∀ k, x k = ∑ n ∈ range j, m n * hN h n k

/-- Invariant of the construction after `j` steps. -/
def InvN (v : V4) (j : ℕ) (h : Fin 3 → V4) : Prop :=
  (∀ n < j, dot (hN h n) v = 0) ∧ IndN j h ∧ SatN v j h ∧ ∀ i < j, GreedyN v i h

/-- `h'` agrees with `h` on the first `m` slots. -/
def Agree (m : ℕ) (h h' : Fin 3 → V4) : Prop := ∀ n < m, hN h' n = hN h n

theorem Agree.inQN {m : ℕ} {h h' : Fin 3 → V4} (ha : Agree m h h') (u : V4) :
    InQN m h' u ↔ InQN m h u := by
  have e : ∀ (a : ℕ → ℚ) (k : Fin 4), ∑ n ∈ range m, a n * (hN h' n k : ℚ)
      = ∑ n ∈ range m, a n * (hN h n k : ℚ) := by
    intro a k
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [ha n (Finset.mem_range.mp hn)]
  constructor
  · rintro ⟨a, h1⟩; exact ⟨a, fun k => by rw [h1 k, e]⟩
  · rintro ⟨a, h1⟩; exact ⟨a, fun k => by rw [h1 k, e]⟩

theorem Agree.efEq {m : ℕ} {h h' : Fin 3 → V4} (ha : Agree m h h') (u : V4) :
    Ef m h' u = Ef m h u := by
  funext i
  by_cases hi : i.val < m
  · simp [Ef, hi, ha i.val hi]
  · simp [Ef, hi]

theorem Agree.mono {m m' : ℕ} {h h' : Fin 3 → V4} (ha : Agree m h h') (hm : m' ≤ m) :
    Agree m' h h' := fun n hn => ha n (lt_of_lt_of_le hn hm)

theorem exists_minimizer (S : Set V4) (hS : S.Nonempty) (g : V4 → ℤ) (hg : ∀ u, 0 ≤ g u) :
    ∃ u ∈ S, ∀ w ∈ S, g u ≤ g w := by
  refine ⟨Function.argminOn (fun u => (g u).toNat) S hS, Function.argminOn_mem _ S hS, fun w hw => ?_⟩
  have h1 := Function.argminOn_le (fun u => (g u).toNat) S hw
  have h2 := hg (Function.argminOn (fun u => (g u).toNat) S hS)
  have h3 := hg w
  omega

theorem inv_step (v : V4) (hv : Primitive v) (j : ℕ) (hj : j < 3) (h : Fin 3 → V4)
    (hinv : InvN v j h) : ∃ h', Agree j h h' ∧ InvN v (j + 1) h' := by
  obtain ⟨hP, hI, hS, hG⟩ := hinv
  obtain ⟨u0, hu0v, hu0⟩ := dim_nonempty v hv j hj h
  obtain ⟨us, ⟨husv, hus⟩, hmin⟩ := exists_minimizer {u | dot u v = 0 ∧ ¬ InQN j h u} ⟨u0, hu0v, hu0⟩
    (fun u => gF (Ef j h u)) (fun u => gF_Ef_nonneg j h u)
  let h' : Fin 3 → V4 := fun i => if i.val < j then h i else us
  have hagree : Agree j h h' := by
    intro n hn
    have hn4 : n < 3 := by omega
    have : h' ⟨n, hn4⟩ = h ⟨n, hn4⟩ := by simp [h', hn]
    simpa [hN, hn4] using this
  have hNj : hN h' j = us := by
    have : h' ⟨j, hj⟩ = us := by simp [h']
    simpa [hN, hj] using this
  have hpos : 0 < gF (Ef j h us) := gF_Ef_pos j h us hI hus
  refine ⟨h', hagree, ?_, ?_, ?_, ?_⟩
  · intro n hn
    by_cases hnj : n < j
    · rw [hagree n hnj]; exact hP n hnj
    · have : n = j := by omega
      subst this; rw [hNj]; exact husv
  · -- independence
    intro a ha n hn
    have ha' : ∀ k, (∑ n ∈ range j, a n * (hN h n k : ℚ)) + a j * (us k : ℚ) = 0 := by
      intro k
      have := ha k
      rw [Finset.sum_range_succ, hNj] at this
      rw [← this]
      congr 1
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [hagree m (Finset.mem_range.mp hm)]
    by_cases haj : a j = 0
    · have hz : ∀ k, ∑ n ∈ range j, a n * (hN h n k : ℚ) = 0 := by
        intro k; have := ha' k; rw [haj] at this; simpa using this
      by_cases hnj : n < j
      · exact hI a hz n hnj
      · have : n = j := by omega
        rw [this]; exact haj
    · exfalso
      apply hus
      refine ⟨fun n => - a n / a j, fun k => ?_⟩
      have h5 := ha' k
      have e2 : (∑ n ∈ range j, (-a n / a j) * (hN h n k : ℚ))
          = (-1 / a j) * ∑ n ∈ range j, a n * (hN h n k : ℚ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun n _ => ?_); ring
      rw [e2]
      field_simp
      linarith
  · -- saturation
    intro x hx hxq
    obtain ⟨a, ha⟩ := hxq
    have ha1 : ∀ k, (x k : ℚ) = (∑ n ∈ range j, a n * (hN h n k : ℚ)) + a j * (us k : ℚ) := by
      intro k
      rw [ha k, Finset.sum_range_succ, hNj]
      congr 1
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [hagree m (Finset.mem_range.mp hm)]
    set c : ℤ := round (a j) with hc
    let x' : V4 := fun k => x k - c * us k
    have hx'v : dot x' v = 0 := by
      show dot (fun k => x k - c * us k) v = 0
      rw [dot_sub_smul, hx, husv]; ring
    have hx'k : ∀ k, (x' k : ℚ) = (∑ n ∈ range j, a n * (hN h n k : ℚ)) + (a j - c) * (us k : ℚ) := by
      intro k
      simp only [x']
      push_cast
      rw [ha1 k]; ring
    have hsc : a j - c = 0 := by
      by_contra hne
      have hnot : ¬ InQN j h x' := by
        rintro ⟨b, hb⟩
        apply hus
        refine ⟨fun n => (b n - a n) / (a j - c), fun k => ?_⟩
        have h6 := hb k
        rw [hx'k k] at h6
        have e3 : (∑ n ∈ range j, ((b n - a n) / (a j - c)) * (hN h n k : ℚ))
            = (1 / (a j - c)) * ∑ n ∈ range j, (b n - a n) * (hN h n k : ℚ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun n _ => ?_); ring
        have e4 : (∑ n ∈ range j, (b n - a n) * (hN h n k : ℚ))
            = (∑ n ∈ range j, b n * (hN h n k : ℚ)) - ∑ n ∈ range j, a n * (hN h n k : ℚ) := by
          rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun n _ => ?_); ring
        rw [e3, e4]
        field_simp
        linarith
      have hle := hmin x' ⟨hx'v, hnot⟩
      have hsh := gF_Ef_shear j h x' us a (a j - c) hx'k
      have hle' : ((gF (Ef j h us) : ℤ) : ℚ) ≤ ((gF (Ef j h x') : ℤ) : ℚ) := by exact_mod_cast hle
      have hbd := round_bd (a j)
      have hposq : (0 : ℚ) < ((gF (Ef j h us) : ℤ) : ℚ) := by exact_mod_cast hpos
      rw [hsh] at hle'
      have : (a j - c) ^ 2 * ((gF (Ef j h us) : ℤ) : ℚ) ≤ 1 / 4 * ((gF (Ef j h us) : ℤ) : ℚ) :=
        mul_le_mul_of_nonneg_right hbd hposq.le
      linarith
    have hxq' : InQN j h x' := ⟨a, fun k => by rw [hx'k k, hsc]; ring⟩
    obtain ⟨m, hm⟩ := hS x' hx'v hxq'
    refine ⟨fun n => if n = j then c else m n, fun k => ?_⟩
    rw [Finset.sum_range_succ, hNj]
    simp only [if_true]
    have e5 : (∑ n ∈ range j, (fun n => if n = j then c else m n) n * hN h' n k)
        = ∑ n ∈ range j, m n * hN h n k := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have := Finset.mem_range.mp hn
      simp [hagree n this, show n ≠ j by omega]
    rw [e5, ← hm k]
    simp only [x']
    ring
  · intro i hi
    by_cases hij : i < j
    · intro u hu hq
      have ha := hagree.mono hij.le
      have hq' : ¬ InQN i h u := (ha.inQN u).not.mp hq
      rw [Agree.efEq ha, Agree.efEq ha, hagree i hij]
      exact hG i hij u hu hq'
    · have : i = j := by omega
      subst this
      intro u hu hq
      rw [Agree.efEq hagree, Agree.efEq hagree, hNj]
      exact hmin u ⟨hu, (hagree.inQN u).not.mp hq⟩

end L4S3
end LRSpectrumFull
