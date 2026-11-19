/-
# L4S4.Sym : the signed-permutation group acts on the four-speed tree data

The tree stores only class representatives
(chain classes, leaf classes), under the group of order 384 = 2^4 * 4! of signed permutations of `ℤ^4`, the Rust type `G`
(`(g.apply x) i = e_i * x_{p_i}`).  Here:

* `SP` : the group element (`σ`, signs `ε`), `SP.act` (= Rust `G.apply`), `SP.inv` (= Rust `G.apply_inv`), `SP.mul`;
* `dot_act`, `act_inv_act`, `act_act_inv`, `primitive_act`, `nz_act`, `ML_act` (`ML (g v) = ML v`), self-contained
  (no other `ML`-invariance module is imported: `ML_perm`, `ML_signs` are re-proved in two lines each);
* `FlagData.act` : the image flag of `act g v`; `leadMinor`, `Dq`, `Sk`, `StageWitness`, `Mlat` are invariant;
* `greedy_act` : `Greedy v F.h` is transported;  `accepted_act` : the image of a greedy flag of a near-tight `v`
  is `Accepted` (all filters of the generator hold for the image flag).  So the symmetry quotient of the tree is
  sound on the Lean side: nothing has to be re-proved for the images.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S3.Accepted
import LRSpectrumFull.L4S3.GreedyFlip
import LRSpectrumFull.L4S4.Chain

namespace LRSpectrumFull
namespace L4S4

open Matrix Finset LRSpectrumFull.L4S3

/-- A signed permutation of the five coordinates (Rust `G { p, e }`). -/
structure SP where
  σ : Equiv.Perm (Fin 4)
  ε : Fin 4 → ℤ
  hε : ∀ i, ε i = 1 ∨ ε i = -1

/-- The action `(g x) i = ε i * x (σ i)` (Rust `G.apply`). -/
def SP.act (g : SP) (x : V4) : V4 := fun i => g.ε i * x (g.σ i)

/-- The inverse element (Rust `apply_inv`: `y_{p_i} = e_i x_i`). -/
def SP.inv (g : SP) : SP where
  σ := g.σ.symm
  ε := fun j => g.ε (g.σ.symm j)
  hε := fun j => g.hε _

theorem eps_sq (g : SP) (i : Fin 4) : g.ε i * g.ε i = 1 := by
  rcases g.hε i with h | h <;> rw [h] <;> norm_num

theorem eps_ne (g : SP) (i : Fin 4) : g.ε i ≠ 0 := by
  rcases g.hε i with h | h <;> rw [h] <;> norm_num

theorem act_inv_act (g : SP) (x : V4) : g.inv.act (g.act x) = x := by
  funext j
  simp only [SP.act, SP.inv, Equiv.apply_symm_apply]
  have := eps_sq g (g.σ.symm j)
  calc g.ε (g.σ.symm j) * (g.ε (g.σ.symm j) * x j) = (g.ε (g.σ.symm j) * g.ε (g.σ.symm j)) * x j := by ring
    _ = x j := by rw [this, one_mul]

theorem act_act_inv (g : SP) (y : V4) : g.act (g.inv.act y) = y := by
  funext i
  simp only [SP.act, SP.inv, Equiv.symm_apply_apply]
  have := eps_sq g i
  calc g.ε i * (g.ε i * y i) = (g.ε i * g.ε i) * y i := by ring
    _ = y i := by rw [this, one_mul]

/-- Composition `g ∘ h` (apply `h` first). -/
def SP.mul (g h : SP) : SP where
  σ := g.σ.trans h.σ
  ε := fun i => g.ε i * h.ε (g.σ i)
  hε := fun i => by
    rcases g.hε i with a | a <;> rcases h.hε (g.σ i) with b | b <;> rw [a, b] <;> norm_num

theorem act_mul (g h : SP) (x : V4) : (g.mul h).act x = g.act (h.act x) := by
  funext i
  simp only [SP.act, SP.mul, Equiv.trans_apply]
  ring

theorem dot_act (g : SP) (a b : V4) : dot (g.act a) (g.act b) = dot a b := by
  unfold dot SP.act
  have h : ∀ i, g.ε i * a (g.σ i) * (g.ε i * b (g.σ i)) = a (g.σ i) * b (g.σ i) := by
    intro i
    have := eps_sq g i
    calc g.ε i * a (g.σ i) * (g.ε i * b (g.σ i)) = (g.ε i * g.ε i) * (a (g.σ i) * b (g.σ i)) := by ring
      _ = a (g.σ i) * b (g.σ i) := by rw [this, one_mul]
  simp only [h]
  exact Equiv.sum_comp g.σ (fun i => a i * b i)

theorem act_smul_add (g : SP) (c : ℤ) (x y : V4) : g.act (fun k => c * x k + y k) = fun k => c * g.act x k + g.act y k := by
  funext k; simp only [SP.act]; ring

theorem act_zero (g : SP) : g.act (fun _ => 0) = fun _ => 0 := by
  funext k; simp [SP.act]

theorem primitive_act {v : V4} (hv : Primitive v) (g : SP) : Primitive (g.act v) := by
  intro d hd
  apply hv d
  intro j
  have h1 := hd (g.σ.symm j)
  have h2 : v j = g.inv.act (g.act v) j := by rw [act_inv_act]
  rw [h2]
  show d ∣ g.ε (g.σ.symm j) * g.act v (g.σ.symm j)
  exact dvd_mul_of_dvd_right h1 _

theorem nz_act {v : V4} (hnz : ∀ i, v i ≠ 0) (g : SP) : ∀ i, g.act v i ≠ 0 := by
  intro i
  simp only [SP.act]
  exact mul_ne_zero (eps_ne g i) (hnz _)

/-! ## `ML` is invariant -/

theorem nid_eps (e : ℤ) (he : e = 1 ∨ e = -1) (y : ℝ) : nearestIntDist ((e : ℝ) * y) = nearestIntDist y := by
  rcases he with rfl | rfl
  · simp
  · have : ((-1 : ℤ) : ℝ) * y = -y := by push_cast; ring
    rw [this, nearestIntDist_neg]

theorem gap_act (g : SP) (v : V4) (t : ℝ) : gap (g.act v) t = gap v t := by
  apply le_antisymm
  · apply le_gap v t
    intro i
    have h := gap_le (g.act v) t (g.σ.symm i)
    have e : (((g.act v) (g.σ.symm i) : ℤ) : ℝ) * t
        = (g.ε (g.σ.symm i) : ℝ) * ((v i : ℝ) * t) := by
      simp only [SP.act, Equiv.apply_symm_apply]; push_cast; ring
    rw [e, nid_eps _ (g.hε _)] at h
    exact h
  · apply le_gap (g.act v) t
    intro i
    have h := gap_le v t (g.σ i)
    have e : (((g.act v) i : ℤ) : ℝ) * t = (g.ε i : ℝ) * ((v (g.σ i) : ℝ) * t) := by
      simp only [SP.act]; push_cast; ring
    rw [e, nid_eps _ (g.hε _)]
    exact h

/-- **`ML (g v) = ML v`** for a signed permutation `g`. -/
theorem ML_act (g : SP) (v : V4) : ML (g.act v) = ML v := by
  have h : gap (g.act v) = gap v := funext (gap_act g v)
  simp only [ML, h]

/-! ## The image flag -/

/-- The image of a flag of `v` is a flag of `g v` (rows `g h_i`, right inverse `ε_k R_{σ k, j}`, same LDL data). -/
def _root_.LRSpectrumFull.L4S3.FlagData.act {v : V4} (F : FlagData v) (g : SP) : FlagData (g.act v) where
  h := fun i => g.act (F.h i)
  R := fun k j => g.ε k * F.R (g.σ k) j
  hv := fun i => by rw [dot_act]; exact F.hv i
  hR := fun i j => by
    have h1 := F.hR i j
    have e : ∀ k : Fin 4, g.act (F.h i) k * (g.ε k * F.R (g.σ k) j) = F.h i (g.σ k) * F.R (g.σ k) j := by
      intro k
      have := eps_sq g k
      simp only [SP.act]
      calc g.ε k * F.h i (g.σ k) * (g.ε k * F.R (g.σ k) j)
          = (g.ε k * g.ε k) * (F.h i (g.σ k) * F.R (g.σ k) j) := by ring
        _ = _ := by rw [this, one_mul]
    simp only [e]
    rw [Equiv.sum_comp g.σ (fun k => F.h i k * F.R k j)]
    exact h1
  Lq := F.Lq
  Dq := F.Dq
  hLunit := F.hLunit
  hLlow := F.hLlow
  hDpos := F.hDpos
  hLDL := fun i j => by rw [dot_act]; exact F.hLDL i j

theorem gram_act {v : V4} (F : FlagData v) (g : SP) : gram (F.act g) = gram F := by
  ext i j
  simp only [gram, Matrix.of_apply, L4S3.FlagData.act, dot_act]

theorem leadMinor_act {v : V4} (F : FlagData v) (g : SP) (j : ℕ) :
    leadMinor (gram (F.act g)) j = leadMinor (gram F) j := by rw [gram_act]

theorem Dq_act {v : V4} (F : FlagData v) (g : SP) (i : Fin 3) : (F.act g).Dq i = F.Dq i := rfl

theorem Sk_act {v : V4} (F : FlagData v) (g : SP) (k : ℕ) : Sk (F.act g) k = Sk F k := rfl

/-- The action on real vectors (for stage witnesses). -/
def SP.actR (g : SP) (x : Fin 4 → ℝ) : Fin 4 → ℝ := fun i => (g.ε i : ℝ) * x (g.σ i)

theorem fmin_actR (g : SP) (x : Fin 4 → ℝ) : fmin (g.actR x) = fmin x := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro i _
    have h := fmin_le_nd (g.actR x) (g.σ.symm i)
    have e : g.actR x (g.σ.symm i) = (g.ε (g.σ.symm i) : ℝ) * x i := by
      simp [SP.actR]
    rw [e, nid_eps _ (g.hε _)] at h
    exact h
  · apply Finset.le_inf'
    intro i _
    have h := fmin_le_nd x (g.σ i)
    have e : g.actR x i = (g.ε i : ℝ) * x (g.σ i) := rfl
    rw [e, nid_eps _ (g.hε _)]
    exact h

theorem stage_actR {v : V4} (F : FlagData v) (g : SP) (k : ℕ) (x : Fin 4 → ℝ) :
    StageWitness (F.act g) k (g.actR x) ↔ StageWitness F k x := by
  have key : ∀ i : Fin 3, ∑ j, ((F.act g).h i j : ℝ) * g.actR x j = ∑ j, (F.h i j : ℝ) * x j := by
    intro i
    have e : ∀ j : Fin 4, ((F.act g).h i j : ℝ) * g.actR x j = (F.h i (g.σ j) : ℝ) * x (g.σ j) := by
      intro j
      have := eps_sq g j
      have h2 : (g.ε j : ℝ) * (g.ε j : ℝ) = 1 := by exact_mod_cast this
      simp only [L4S3.FlagData.act, SP.act, SP.actR]
      push_cast
      calc (g.ε j : ℝ) * (F.h i (g.σ j) : ℝ) * ((g.ε j : ℝ) * x (g.σ j))
          = ((g.ε j : ℝ) * (g.ε j : ℝ)) * ((F.h i (g.σ j) : ℝ) * x (g.σ j)) := by ring
        _ = _ := by rw [h2, one_mul]
    simp only [e]
    exact Equiv.sum_comp g.σ (fun j => (F.h i j : ℝ) * x j)
  constructor
  · intro h i hi
    obtain ⟨n, hn⟩ := h i hi
    exact ⟨n, by rw [← key i]; exact hn⟩
  · intro h i hi
    obtain ⟨n, hn⟩ := h i hi
    exact ⟨n, by rw [key i]; exact hn⟩

theorem actR_actR_inv (g : SP) (x : Fin 4 → ℝ) : g.actR (g.inv.actR x) = x := by
  funext i
  simp only [SP.actR, SP.inv, Equiv.symm_apply_apply]
  have h2 : (g.ε i : ℝ) * (g.ε i : ℝ) = 1 := by exact_mod_cast eps_sq g i
  calc (g.ε i : ℝ) * ((g.ε i : ℝ) * x i) = ((g.ε i : ℝ) * (g.ε i : ℝ)) * x i := by ring
    _ = x i := by rw [h2, one_mul]

/-- `M(L_k)` is invariant: the stage data of the image flag are those of the flag. -/
theorem Mlat_act {v : V4} (F : FlagData v) (g : SP) (k : ℕ) : Mlat (F.act g) k = Mlat F k := by
  unfold Mlat
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨g.inv.actR x, ?_, ?_⟩
    · rw [← stage_actR F g k, actR_actR_inv]; exact hx
    · rw [← fmin_actR g (g.inv.actR x), actR_actR_inv]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g.actR x, (stage_actR F g k x).2 hx, (fmin_actR g x).symm⟩

/-! ## `Greedy` and `Accepted` are transported -/

theorem hN_act (h : Fin 3 → V4) (g : SP) (n : ℕ) :
    hN (fun i => g.act (h i)) n = g.act (hN h n) := by
  unfold hN
  by_cases hn : n < 3
  · simp [hn]
  · simp [hn, act_zero]

theorem Ef_act (j : ℕ) (h : Fin 3 → V4) (g : SP) (w : V4) :
    Ef j (fun i => g.act (h i)) (g.act w) = fun i => g.act (Ef j h w i) := by
  funext i
  unfold Ef
  by_cases hi : i.val < j
  · simp [hi, hN_act]
  · simp [hi]

theorem gF_act {n : ℕ} (g : SP) (f : Fin n → V4) : gF (fun i => g.act (f i)) = gF f := by
  unfold gF
  simp only [dot_act]

theorem inQN_fwd (j : ℕ) (g : SP) (h : Fin 3 → V4) (u : V4) (hq : InQN j h u) :
    InQN j (fun i => g.act (h i)) (g.act u) := by
  obtain ⟨a, ha⟩ := hq
  refine ⟨a, fun k => ?_⟩
  have e1 : (g.act u k : ℚ) = (g.ε k : ℚ) * (u (g.σ k) : ℚ) := by simp [SP.act]
  rw [e1, ha (g.σ k), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [hN_act]
  simp only [SP.act]
  push_cast; ring

theorem inQN_act (j : ℕ) (h : Fin 3 → V4) (g : SP) (u : V4) :
    InQN j (fun i => g.act (h i)) (g.act u) ↔ InQN j h u := by
  constructor
  · intro hq
    have := inQN_fwd j g.inv _ _ hq
    simpa [act_inv_act] using this
  · exact inQN_fwd j g h u

theorem greedy_act {v : V4} (F : FlagData v) (g : SP) (hg : Greedy v F.h) :
    Greedy (g.act v) (F.act g).h := by
  intro j hj u' hu' hq
  set u := g.inv.act u' with hu
  have hau : g.act u = u' := act_act_inv g u'
  have hdot : dot u v = 0 := by
    have := dot_act g u v
    rw [hau] at this
    rw [← this]; exact hu'
  have hq1 : ¬ InQN j (F.act g).h u' := (inQSpanPrefix_iff _ j hj.le u').not.mp hq
  have hq2 : ¬ InQN j F.h u := by
    intro hh
    exact hq1 (by rw [← hau]; exact (inQN_act j F.h g u).2 hh)
  have hq3 : ¬ InQSpanPrefix F.h j u := (inQSpanPrefix_iff _ j hj.le u).not.mpr hq2
  have hgl := hg j hj u hdot hq3
  rw [take_succ_eq j hj, take_append_eq j hj.le, gramDetList_ofFn, gramDetList_ofFn] at hgl
  rw [take_succ_eq j hj, take_append_eq j hj.le, gramDetList_ofFn, gramDetList_ofFn]
  have e1 : (F.act g).h ⟨j, hj⟩ = g.act (F.h ⟨j, hj⟩) := rfl
  have e2 : (F.act g).h = fun i => g.act (F.h i) := rfl
  rw [e1, e2, ← hau, Ef_act, Ef_act, gF_act, gF_act]
  exact hgl

/-- The image of a greedy flag of a near-tight `v` under any signed permutation is accepted. -/
theorem accepted_act {v : V4} (hv : Primitive v) (hnz : ∀ i, v i ≠ 0) (hlt : ML v < 1 / 4)
    (F : FlagData v) (hg : Greedy v F.h) (g : SP) : Accepted (F.act g) :=
  accepted_of_greedy (F.act g) (primitive_act hv g) (nz_act hnz g)
    (by rw [ML_act]; exact hlt) (greedy_act F g hg)

end L4S4
end LRSpectrumFull
