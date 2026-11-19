/-
# L4S4.ChainRep : a flag whose first rows are prescribed node rows

The node rows `l_0, l_1, l_2` of the tree (size-reduced lifts) differ from the rows of
the greedy flag `F` of a near-tight `v` by a lower-triangular unimodular change (`l_i = ± h_i + ∑_{m<i} a_{im} h_m`).
Instead of transferring each filter (`PrimChild`, `NoCoord`, `ShortestFirst/Second`, `NodeBound`) from flag rows to node
rows one by one, we build the flag of `v` whose first `d` rows ARE the node rows:

* `gF_Ef_chain`      : `det Gram (h_0..h_{j-1}, w)` is an invariant of the chain (not only of the prefix lattice);
* `greedy_chain`     : `Greedy v F.h` is invariant under change of flag with the same chain at every level;
* `exists_flag_prefix` : if `r_i ∈ L_{i+1}(F)` and `h_i ∈ L_{i+1}(r)` for `i < d`, there is a flag `F'` of the same `v`
  with `F'.h i = r i` for `i < d` and `SameChain F F' k` for all `k ≤ 3`;
* `accepted_prefix`  : the near-tight `v` with greedy flag `F` and such rows `r` has an ACCEPTED flag whose first `d`
  rows are `r`.  Hence every Accepted-type property (stated for the rows of a flag)
  applies literally to the node rows.  No separate transfer of the filters is needed.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S4.Sym

namespace LRSpectrumFull
namespace L4S4

open Matrix Finset LRSpectrumFull.L4S3

/-! ## The Gram determinant `gF (Ef j h w)` is a chain invariant -/

theorem Ef_self (j : ℕ) (hj : j < 3) (h : Fin 3 → V4) :
    Ef j h (h ⟨j, hj⟩) = fun i : Fin (j + 1) => hN h i.val := by
  funext i
  unfold Ef
  by_cases hi : i.val < j
  · simp [hi]
  · have : i.val = j := by omega
    simp [hi, this, hN, hj]

theorem gF_Ef_self {v : V4} (F : FlagData v) (j : ℕ) (hj : j < 3) :
    gF (Ef j F.h (F.h ⟨j, hj⟩)) = leadMinor (gram F) (j + 1) := by
  rw [Ef_self, leadMinor_eq_gF F (j + 1) (by omega)]

theorem gF_Ef_chain {v : V4} (F F' : FlagData v) (j : ℕ) (hj : j ≤ 3) (h : SameChain F F' j) (w : V4) :
    gF (Ef j F'.h w) = gF (Ef j F.h w) := by
  obtain ⟨T, hT⟩ := coeff_matrix F F' j h.1
  have hpos : 0 < gF (fun i : Fin j => hN F.h i.val) := by
    rw [← leadMinor_eq_gF F j hj]; exact leadMinor_pos' F j
  have hdet : T.det ^ 2 = 1 := by
    have e1 := gF_shear (fun i : Fin j => hN F.h i.val) (fun i : Fin j => hN F'.h i.val) T hT
    have e2 := leadMinor_chain F F' j hj h
    rw [leadMinor_eq_gF F' j hj, leadMinor_eq_gF F j hj] at e2
    have h3 : (T.det ^ 2 - 1) * gF (fun i : Fin j => hN F.h i.val) = 0 := by
      linear_combination e1.symm.trans e2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · linarith
    · exact absurd h4 (ne_of_gt hpos)
  let Te : Matrix (Fin (j + 1)) (Fin (j + 1)) ℤ := Matrix.of fun a b =>
    if ha : a.val < j then (if hb : b.val < j then T ⟨a.val, ha⟩ ⟨b.val, hb⟩ else 0)
    else (if a = b then 1 else 0)
  have hrow : ∀ a c, Ef j F'.h w a c = ∑ m, Te a m * Ef j F.h w m c := by
    intro a c
    rw [Fin.sum_univ_castSucc]
    refine Fin.lastCases ?_ (fun a => ?_) a
    · have hne : ∀ m : Fin j, Fin.last j ≠ Fin.castSucc m := fun m => (Fin.castSucc_lt_last m).ne'
      simp [Te, Ef, hne]
    · have := hT a c
      simp only [Ef, Fin.coe_castSucc, a.2, if_true, Te, Matrix.of_apply, dif_pos a.2, Fin.val_last,
        lt_irrefl, if_false]
      rw [this]
      simp [Fin.sum_univ_castSucc]
  have hdetE : Te.det = T.det := by
    rw [Matrix.det_succ_row Te (Fin.last j), Finset.sum_eq_single (Fin.last j)]
    · have hsub : Te.submatrix (Fin.last j).succAbove (Fin.last j).succAbove = T := by
        ext a b
        simp [Te, Fin.succAbove_last, a.2, b.2]
      rw [hsub]
      have : ((-1 : ℤ)) ^ ((Fin.last j : ℕ) + (Fin.last j : ℕ)) = 1 := by
        rw [← two_mul, pow_mul]; simp
      simp [Te, this]
    · intro b _ hb
      have : Te (Fin.last j) b = 0 := by
        simp [Te, Ne.symm hb]
      simp [this]
    · simp
  have := gF_shear (Ef j F.h w) (Ef j F'.h w) Te hrow
  rw [this, hdetE, hdet, one_mul]

/-! ## `Greedy` is invariant under change of flag with the same chains -/

theorem inQN_chain {v : V4} (F F' : FlagData v) (j : ℕ) (h : SameChain F F' j) (u : V4)
    (hq : InQN j F'.h u) : InQN j F.h u := by
  obtain ⟨a, ha⟩ := hq
  have hc : ∀ n ∈ range j, ∃ c : ℕ → ℤ, ∀ a', hN F'.h n a' = ∑ m ∈ range j, c m * hN F.h m a' := by
    intro n hn
    exact h.1 n (mem_range.1 hn)
  choose! c hc using hc
  refine ⟨fun m => ∑ n ∈ range j, a n * (c n m : ℚ), fun k => ?_⟩
  rw [ha k]
  have e : ∀ n ∈ range j, a n * (hN F'.h n k : ℚ)
      = ∑ m ∈ range j, (a n * (c n m : ℚ)) * (hN F.h m k : ℚ) := by
    intro n hn
    have := congrArg (fun z : ℤ => (z : ℚ)) (hc n hn k)
    simp only [Int.cast_sum, Int.cast_mul] at this
    rw [this, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_mul]

theorem greedy_chain {v : V4} (F F' : FlagData v) (hc : ∀ k ≤ 3, SameChain F F' k)
    (hg : Greedy v F.h) : Greedy v F'.h := by
  intro j hj u hu hq
  have hq1 : ¬ InQN j F'.h u := (inQSpanPrefix_iff _ j hj.le u).not.mp hq
  have hq2 : ¬ InQN j F.h u := fun hh => hq1 (inQN_chain F' F j (hc j hj.le).symm u hh)
  have hq3 : ¬ InQSpanPrefix F.h j u := (inQSpanPrefix_iff _ j hj.le u).not.mpr hq2
  have hgl := hg j hj u hu hq3
  rw [take_succ_eq j hj, take_append_eq j hj.le, gramDetList_ofFn, gramDetList_ofFn] at hgl
  rw [take_succ_eq j hj, take_append_eq j hj.le, gramDetList_ofFn, gramDetList_ofFn]
  rw [gF_Ef_chain F F' j hj.le (hc j hj.le) u, gF_Ef_self F' j hj,
    leadMinor_chain F F' (j + 1) (by omega) (hc _ (by omega)), ← gF_Ef_self F j hj]
  exact hgl

/-! ## A flag with prescribed first rows -/

/-- `x` lies in the `ℤ`-span of the first `k` rows of the family `r`. -/
def LatRows (r : Fin 3 → V4) (k : ℕ) (x : V4) : Prop :=
  ∃ c : ℕ → ℤ, ∀ a, x a = ∑ m ∈ range k, c m * hN r m a

/-- The rows `r_0..r_{d-1}` have the same chain of lattices as the rows of `F` (levels `1..d`). -/
def PrefixEq {v : V4} (F : FlagData v) (r : Fin 3 → V4) (d : ℕ) : Prop :=
  ∀ i < d, LatRows F.h (i + 1) (hN r i) ∧ LatRows r (i + 1) (hN F.h i)

theorem tri_sum' (h : Fin 3 → V4) (T : Matrix (Fin 3) (Fin 3) ℤ)
    (hT : ∀ a m, a < m → T a m = 0) (i : ℕ) (hi : i < 3) (k : ℕ) (hik : i < k) (hk : k ≤ 3)
    (a : Fin 4) :
    ∑ b : Fin 3, T ⟨i, hi⟩ b * h b a
      = ∑ m ∈ range k, (if hm : m < 3 then T ⟨i, hi⟩ ⟨m, hm⟩ else 0) * hN h m a := by
  have e1 : ∑ b : Fin 3, T ⟨i, hi⟩ b * h b a
      = ∑ m ∈ range 3, (if hm : m < 3 then T ⟨i, hi⟩ ⟨m, hm⟩ else 0) * hN h m a := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => (if hm : m < 3 then T ⟨i, hi⟩ ⟨m, hm⟩ else 0) *
      hN h m a) 3]
    exact Finset.sum_congr rfl (fun b _ => by simp [hN, b.2])
  rw [e1]
  symm
  apply Finset.sum_subset (range_mono hk)
  intro m hm hm'
  have hm4 : m < 3 := mem_range.1 hm
  have hmk : ¬ m < k := fun h => hm' (mem_range.2 h)
  have : T ⟨i, hi⟩ ⟨m, hm4⟩ = 0 := hT _ _ (by show i < m; omega)
  simp [hm4, this]

/-- The triangular matrix of coefficients: row `a < d` expresses `x_a` as `∑_{m ≤ a} c a m y_m`; rows `≥ d` are the identity. -/
def mkT (d : ℕ) (c : ℕ → ℕ → ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun a b => if a.val < d then (if b.val ≤ a.val then c a.val b.val else 0)
    else (if a = b then 1 else 0)

theorem mkT_tri (d : ℕ) (c : ℕ → ℕ → ℤ) : ∀ a m, a < m → mkT d c a m = 0 := by
  intro a m hlt
  have this' : ¬ (m ≤ a) := not_le.2 hlt
  have h2 : a ≠ m := ne_of_lt hlt
  by_cases ha : a.val < d <;> simp [mkT, ha, this', h2]

theorem mkT_row_lt (d : ℕ) (c : ℕ → ℕ → ℤ) (h : Fin 3 → V4) (a : ℕ) (ha4 : a < 3) (had : a < d)
    (x : V4) (hx : ∀ a', x a' = ∑ m ∈ range (a + 1), c a m * hN h m a') (k : Fin 4) :
    ∑ b : Fin 3, mkT d c ⟨a, ha4⟩ b * h b k = x k := by
  rw [tri_sum' h (mkT d c) (mkT_tri d c) a ha4 (a + 1) (Nat.lt_succ_self a) (by omega) k, hx k]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm' : m < a + 1 := mem_range.1 hm
  have hm4 : m < 3 := by omega
  simp [mkT, hm4, had, show m ≤ a by omega]

theorem mkT_row_ge (d : ℕ) (c : ℕ → ℕ → ℤ) (h : Fin 3 → V4) (a : Fin 3) (had : ¬ a.val < d) (k : Fin 4) :
    ∑ b : Fin 3, mkT d c a b * h b k = h a k := by
  simp [mkT, had]

theorem exists_flag_prefix {v : V4} (F : FlagData v) (r : Fin 3 → V4) (d : ℕ) (hd : d ≤ 3)
    (hP : PrefixEq F r d) :
    ∃ F' : FlagData v, (∀ i : Fin 3, i.val < d → F'.h i = r i) ∧ ∀ k ≤ 3, SameChain F F' k := by
  choose! c hc using fun i (hi : i < d) => (hP i hi).1
  choose! c' hc' using fun i (hi : i < d) => (hP i hi).2
  set T := mkT d c with hTdef
  set T' := mkT d c' with hT'def
  let R' : Fin 3 → V4 := fun a => if a.val < d then r a else F.h a
  have hRr : ∀ m : ℕ, m < d → hN R' m = hN r m := by
    intro m hm
    funext k
    simp [hN, R', show m < 3 by omega, hm]
  have hTH : ∀ a k, ∑ b, T a b * F.h b k = R' a k := by
    intro a k
    by_cases ha : a.val < d
    · have := mkT_row_lt d c F.h a.val a.2 ha (r a) (fun a' => by
        have h1 := hc a.val ha a'
        simpa [hN, a.2] using h1) k
      simpa [R', ha] using this
    · simpa [R', ha] using mkT_row_ge d c F.h a ha k
  have hT'R : ∀ a k, ∑ b, T' a b * R' b k = F.h a k := by
    intro a k
    by_cases ha : a.val < d
    · have h1 := mkT_row_lt d c' R' a.val a.2 ha (F.h a) (fun a' => by
        have h2 := hc' a.val ha a'
        have h3 : ∀ m ∈ range (a.val + 1), c' a.val m * hN R' m a' = c' a.val m * hN r m a' := by
          intro m hm
          rw [hRr m (by have := mem_range.1 hm; omega)]
        rw [Finset.sum_congr rfl h3, ← h2]
        simp [hN, a.2]) k
      exact h1
    · simpa [R', ha] using mkT_row_ge d c' R' a ha k
  -- T' T = 1 via the right inverse of the rows of F
  have hHR : ∀ a j : Fin 3, ∑ k, F.h a k * F.R k j = if a = j then 1 else 0 := fun a j => F.hR a j
  have hT'T : T' * T = 1 := by
    ext a j
    rw [Matrix.one_apply]
    have e1 : ∀ k, F.h a k = ∑ m, (T' * T) a m * F.h m k := by
      intro k
      rw [← hT'R a k]
      simp only [Matrix.mul_apply, Finset.sum_mul]
      have : ∀ b, T' a b * R' b k = ∑ m, T' a b * T b m * F.h m k := by
        intro b
        rw [← hTH b k, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m _ => by ring)
      simp only [this]
      rw [Finset.sum_comm]
    have e2 : (if a = j then (1 : ℤ) else 0) = ∑ m, (T' * T) a m * (if m = j then 1 else 0) := by
      rw [← hHR a j]
      simp only [e1, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [← hHR m j, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [e2]
    simp
  have hTT' : T * T' = 1 := mul_eq_one_comm.1 hT'T
  obtain ⟨F', hF'⟩ := exists_change F T T' hTT'
  have hrow : ∀ a k, F'.h a k = ∑ b, T a b * F.h b k := hF'
  refine ⟨F', ?_, fun k hk => sameChain_of_tri F F' T T' hTT' (mkT_tri d c) (mkT_tri d c') hrow k hk⟩
  intro i hi
  funext k
  rw [hrow, hTH]
  simp [R', hi]

/-- **Transfer to prescribed node rows.**  A greedy flag `F` of `v` and rows `r` of the same chain (levels `1..d`) give an ACCEPTED
flag of `v` whose first `d` rows are exactly `r`. -/
theorem accepted_prefix {v : V4} (hv : Primitive v) (hnz : ∀ i, v i ≠ 0) (hlt : ML v < 1 / 4)
    (F : FlagData v) (hg : Greedy v F.h) (r : Fin 3 → V4) (d : ℕ) (hd : d ≤ 3) (hP : PrefixEq F r d) :
    ∃ F' : FlagData v, Accepted F' ∧ Greedy v F'.h ∧ (∀ i : Fin 3, i.val < d → F'.h i = r i) := by
  obtain ⟨F', hrows, hchain⟩ := exists_flag_prefix F r d hd hP
  have hg' := greedy_chain F F' hchain hg
  exact ⟨F', accepted_of_greedy F' hv hnz hlt hg', hg', hrows⟩

/-- Symmetry and rows together: the image of a greedy flag under `g`, re-based on prescribed rows `r`. -/
theorem accepted_act_prefix {v : V4} (hv : Primitive v) (hnz : ∀ i, v i ≠ 0) (hlt : ML v < 1 / 4)
    (F : FlagData v) (hg : Greedy v F.h) (g : SP) (r : Fin 3 → V4) (d : ℕ) (hd : d ≤ 3)
    (hP : PrefixEq (F.act g) r d) :
    ∃ F' : FlagData (g.act v), Accepted F' ∧ Greedy (g.act v) F'.h ∧
      (∀ i : Fin 3, i.val < d → F'.h i = r i) :=
  accepted_prefix (primitive_act hv g) (nz_act hnz g) (by rw [ML_act]; exact hlt)
    (F.act g) (greedy_act F g hg) r d hd hP

end L4S4
end LRSpectrumFull
