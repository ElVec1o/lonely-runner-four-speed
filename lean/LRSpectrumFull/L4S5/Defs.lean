/-
# L4S5.Defs : the checkers of the four-speed certificate: decoding, leaf records, child list

Written against `L4S4.StreamHyp4` and the frozen certificate format.

* Data layout: a leaf record is 46 fields, field `f` stored as the byte `f + 128`; `recOf bl j` is record `j` of a list of blobs
  of 100 records (little endian `ℕ`), `fld R k` the field `k` of a record (the signed permutation is decoded by `spOf`).
* `LeafOk r lf` (decidable): the lifts `b_j · y = t_j`, the `K_2` certificate `LeafBQP`, then kind 1: `CritEq` of the two basis
  vectors under `lf.g`, or kind 0: the witness data with the STRICT test `W2 < 4 wMin` (`A2 > 0`).
* `passB` : the Boolean child filter of `ChildPass4` (`qform` through the explicit adjugate `qB`); `goB` : the merge of the
  candidate stream with the stored `t` stream; `nodeB` = coverage of the `t0` range by chunks plus all chunk checks.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L4S4.Time4

namespace LRSpectrumFull
namespace L4S5

open Matrix Finset LRSpectrumFull.L4S3 LRSpectrumFull.L4S4

noncomputable section

/-! ## 1. Data layout and decoding -/

structure Chunk where
  lo : ℤ
  hi : ℤ
  cnt : ℕ
  bl : List ℕ

/-- Field `k` of a packed record. -/
def fld (R : ℕ) (k : ℕ) : ℤ := (((R >>> (8 * k)) % 256 : ℕ) : ℤ) - 128

/-- Record `j` (46 fields, 368 bits) of a list of blobs of 100 records. -/
def recOf (bl : List ℕ) (j : ℕ) : ℕ := ((bl.getD (j / 100) 0) >>> (368 * (j % 100))) % 2 ^ 368

def v4At (R k : ℕ) : V4 := fun i => fld R (k + i.val)

def permOf (f : Fin 4 → ℤ) : Equiv.Perm (Fin 4) :=
  if h : Function.Injective (fun i => (⟨(f i).toNat % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4)) then
    Equiv.ofBijective _ (Finite.injective_iff_bijective.mp h) else 1

/-- The signed permutation of a record; an invalid encoding decodes to the identity (the checks then decide on the
decoded `g` whatever it is, so no validity lemma is needed). -/
def spOf (σf εf : Fin 4 → ℤ) : SP :=
  if h : ∀ i, εf i = 1 ∨ εf i = -1 then ⟨permOf σf, εf, h⟩ else ⟨1, fun _ => 1, fun _ => Or.inl rfl⟩

def decLeaf (R : ℕ) : LeafRec4 where
  t := fun i => fld R i.val
  y := v4At R 3
  kind := (fld R 7).toNat
  x2 := v4At R 8
  W2 := fld R 12
  k := fun j => v4At R (13 + 4 * j.val)
  q := fun j => v4At R (21 + 4 * j.val)
  p := fun a j => fld R (29 + 2 * a.val + j.val)
  ck := if fld R 37 = 1 then 1 else 0
  g := spOf (fun i => fld R (38 + i.val)) (fun i => fld R (42 + i.val))

/-! ## 2. Leaf records -/

instance (h : V4) (lf : LeafRec4) : Decidable (LeafBQP h lf) := by unfold LeafBQP; infer_instance
instance (k : Fin 2) (u : V4) : Decidable (CritEq k u) := by unfold CritEq; infer_instance
instance (r : T1Rec4) : Decidable (T1Chk r) := by unfold T1Chk; infer_instance

/-- Noncritical data with the STRICT test `A2 = 4 wMin(x2, W2) - W2 > 0`. -/
def NcB (h : V4) (lf : LeafRec4) : Prop :=
  0 < lf.W2 ∧ lf.W2 ∣ dot h lf.x2 ∧ lf.W2 ∣ dot lf.y lf.x2 ∧ lf.W2 < 4 * wMin lf.x2 lf.W2

instance (h : V4) (lf : LeafRec4) : Decidable (NcB h lf) := by unfold NcB; infer_instance

def LeafOk (r : T1Rec4) (lf : LeafRec4) : Prop :=
  (∀ j : Fin 3, dot (r.b j) lf.y = lf.t j) ∧ LeafBQP r.h lf ∧
  ((lf.kind = 1 ∧ ∀ j : Fin 2, CritEq lf.ck (lf.g.act (lf.k j))) ∨ (lf.kind = 0 ∧ NcB r.h lf))

instance (r : T1Rec4) (lf : LeafRec4) : Decidable (LeafOk r lf) := by unfold LeafOk; infer_instance

def leafB (r : T1Rec4) (R : ℕ) : Bool := decide (LeafOk r (decLeaf R))

theorem toNode_row0 (r : T1Rec4) (c : T1Chk r) : hN (r.toNode c).rows 0 = r.h := by
  simp [T1Rec4.toNode, hN]

theorem toNode_A1 (r : T1Rec4) (c : T1Chk r) : A1 (r.toNode c) = 4 * wMin r.x1 r.W1 - r.W1 := by
  simp [A1, T1Rec4.toNode]

theorem toNode_W1 (r : T1Rec4) (c : T1Chk r) : ((r.toNode c).wit 1).2 = r.W1 := by
  simp [T1Rec4.toNode]

theorem toNode_G1 (r : T1Rec4) (c : T1Chk r) : G1 (r.toNode c) = dot r.h r.h := by
  simp [G1, toNode_row0]

/-- A checked leaf record is a `LeafRel4` leaf once the line claim is supplied (kind 0). -/
theorem leafRel_of_ok (C : Certificate4) (r : T1Rec4) (c : T1Chk r) (lf : LeafRec4) (h : LeafOk r lf)
    (hl : lf.kind = 0 → LinesOk C (r.toNode c) lf) : LeafRel4 C (r.toNode c) lf := by
  obtain ⟨-, hb, hcase⟩ := h
  rw [← toNode_row0 r c] at hb
  refine ⟨hb, ?_⟩
  rcases hcase with hc | ⟨hk, hW, hd0, hd1, hlt⟩
  · exact Or.inl hc
  · refine Or.inr ⟨hk, ⟨hW, by rw [toNode_row0]; exact hd0, hd1, ?_⟩, hl hk⟩
    have hWq : (0 : ℚ) < lf.W2 := by exact_mod_cast hW
    have h4 : (lf.W2 : ℚ) < 4 * (wMin lf.x2 lf.W2 : ℚ) := by exact_mod_cast hlt
    rw [cOf, le_div_iff₀ hWq]
    simp only []
    nlinarith

/-! ## 3. The child filter and the stream merge -/

instance (t : Fin 3 → ℤ) : Decidable (FirstPos t) := by unfold FirstPos; infer_instance
instance {d : ℕ} (t : Fin d → ℤ) : Decidable (GcdOne t) := by unfold GcdOne; infer_instance
instance {d : ℕ} (b : Fin d → V4) (t : Fin d → ℤ) : Decidable (eiBad b t) := by unfold eiBad; infer_instance

structure Ctx4 where
  b : Fin 3 → V4
  G : ℤ
  A : ℤ
  W : ℤ

def ctxR (r : T1Rec4) : Ctx4 := ⟨r.b, dot r.h r.h, 4 * wMin r.x1 r.W1 - r.W1, r.W1⟩

def Ctx4.gm (c : Ctx4) (i k : Fin 3) : ℤ := dot (c.b i) (c.b k)

/-- `tᵀ adj(g) t`, the entries of `adj` written as in `Matrix.adjugate_fin_three`. -/
def qB (g : Fin 3 → Fin 3 → ℤ) (t : Fin 3 → ℤ) : ℤ :=
  t 0 * ((g 1 1 * g 2 2 - g 1 2 * g 2 1) * t 0 + (-(g 0 1 * g 2 2) + g 0 2 * g 2 1) * t 1 + (g 0 1 * g 1 2 - g 0 2 * g 1 1) * t 2) +
  t 1 * ((-(g 1 0 * g 2 2) + g 1 2 * g 2 0) * t 0 + (g 0 0 * g 2 2 - g 0 2 * g 2 0) * t 1 + (-(g 0 0 * g 1 2) + g 0 2 * g 1 0) * t 2) +
  t 2 * ((g 1 0 * g 2 1 - g 1 1 * g 2 0) * t 0 + (-(g 0 0 * g 2 1) + g 0 1 * g 2 0) * t 1 + (g 0 0 * g 1 1 - g 0 1 * g 1 0) * t 2)

theorem qform_eq3 (b : Fin 3 → V4) (y : V4) : qform b y = qB (fun i k => dot (b i) (b k)) (tvec b y) := by
  simp [qform, Matrix.adjugate_fin_three, gramK, dotProduct, Matrix.mulVec, Fin.sum_univ_three, qB]
  try ring

/-- The Boolean form of `ChildPass4` (a function of `t` only). -/
def passB (c : Ctx4) (t : Fin 3 → ℤ) : Bool :=
  decide (FirstPos t) && decide (GcdOne t) && !decide (eiBad c.b t) &&
  decide (qB c.gm t * (3 * c.A ^ 2) < 28 * c.W ^ 2 * c.G) &&
  decide (3 * c.G * qB c.gm t < 12 * qB c.gm t + 28 * c.G ^ 2) &&
  decide (3 * c.G ^ 2 ≤ 4 * qB c.gm t)

theorem det_gramK4 (n : NodeW 1 3) : (gramK n.b).det = dot (hN n.rows 0) (hN n.rows 0) := by
  have h := gF_compl (by norm_num) n.id
  have e : (gramK n.b).det = gF n.b := rfl
  rw [e, h]
  unfold gF
  rw [Matrix.det_unique]
  simp [Matrix.of_apply]

theorem passB_of_pass (r : T1Rec4) (c : T1Chk r) (y : V4) (hp : ChildPass4 (r.toNode c) y) :
    passB (ctxR r) (tvec r.b y) = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  have hq : qform (r.toNode c).b y = qB (ctxR r).gm (tvec r.b y) := qform_eq3 r.b y
  have hd := det_gramK4 (r.toNode c)
  rw [toNode_row0] at hd
  rw [hq, hd, toNode_A1, toNode_W1] at h4
  rw [hq, toNode_G1] at h5 h6
  have e1 : tvec (r.toNode c).b y = tvec r.b y := rfl
  rw [e1] at h1 h2 h3
  unfold passB
  simp only [ctxR, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  exact ⟨⟨⟨⟨⟨h2, h1⟩, h3⟩, h4⟩, h5⟩, h6⟩

abbrev Tri := ℤ × ℤ × ℤ

def goB (c : Ctx4) : List Tri → List Tri → Bool
  | [], _ => true
  | x :: cs, st =>
    if passB c ![x.1, x.2.1, x.2.2] then
      (match st with
       | [] => false
       | s :: st' => (s == x) && goB c cs st')
    else goB c cs st

theorem goB_sound (c : Ctx4) : ∀ (cs st : List Tri), goB c cs st = true →
    ∀ x ∈ cs, passB c ![x.1, x.2.1, x.2.2] = true → x ∈ st := by
  intro cs
  induction cs with
  | nil => intro st _ x hx; simp at hx
  | cons a cs ih =>
    intro st h x hx hpx
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp only [goB, hpx, if_true] at h
      cases st with
      | nil => simp at h
      | cons s st' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        simp [h.1]
    · by_cases hpa : passB c ![a.1, a.2.1, a.2.2] = true
      · simp only [goB, hpa, if_true] at h
        cases st with
        | nil => simp at h
        | cons s st' =>
          simp only [Bool.and_eq_true] at h
          exact List.mem_cons_of_mem _ (ih st' h.2 x hx' hpx)
      · have hf : passB c ![a.1, a.2.1, a.2.2] = false := by simpa using hpa
        simp only [goB, hf] at h
        · exact ih st h x hx' hpx

def rngZ (lo hi : ℤ) : List ℤ := (List.range (hi + 1 - lo).toNat).map fun k : ℕ => lo + (k : ℤ)

theorem mem_rngZ {lo hi x : ℤ} : x ∈ rngZ lo hi ↔ lo ≤ x ∧ x ≤ hi := by
  unfold rngZ
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have : (k : ℤ) < (hi + 1 - lo).toNat := by exact_mod_cast hk
    have h2 : ((hi + 1 - lo).toNat : ℤ) = max (hi + 1 - lo) 0 := Int.toNat_eq_max _
    omega
  · intro ⟨h1, h2⟩
    exact ⟨(x - lo).toNat, by omega, by omega⟩

/-- Half-width of the `t_i`-box (`childPass_box4`). -/
def tmB (c : Ctx4) (i : Fin 3) : ℤ := isqrtI (28 * c.W ^ 2 * c.gm i i / (3 * c.A ^ 2))

/-- The candidate stream of the `t0`-range `[lo, hi]`, in loop order (lexicographic). -/
def cands (c : Ctx4) (lo hi : ℤ) : List Tri :=
  (rngZ lo hi).flatMap fun a => (rngZ (-tmB c 1) (tmB c 1)).flatMap fun b =>
    (rngZ (-tmB c 2) (tmB c 2)).map fun d => (a, b, d)

/-- The stored `t` stream of a chunk. -/
def stOf (bl : List ℕ) (cnt : ℕ) : List Tri :=
  (List.range cnt).map fun j => (fld (recOf bl j) 0, fld (recOf bl j) 1, fld (recOf bl j) 2)

def chunkB (r : T1Rec4) (ch : Chunk) : Bool :=
  goB (ctxR r) (cands (ctxR r) ch.lo ch.hi) (stOf ch.bl ch.cnt) &&
  (List.range ch.cnt).all fun j => leafB r (recOf ch.bl j)

def covB : ℤ → List Chunk → ℤ → Bool
  | nxt, [], T => decide (nxt = T + 1)
  | nxt, ch :: cs, T => decide (ch.lo = nxt) && decide (ch.lo ≤ ch.hi) && covB (ch.hi + 1) cs T

theorem covB_sound : ∀ (cs : List Chunk) (nxt T : ℤ), covB nxt cs T = true → ∀ t0, nxt ≤ t0 → t0 ≤ T →
    ∃ ch ∈ cs, ch.lo ≤ t0 ∧ t0 ≤ ch.hi
  | [], nxt, T, h, t0, h1, h2 => by simp [covB] at h; omega
  | ch :: cs, nxt, T, h, t0, h1, h2 => by
      simp only [covB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hlo, hle⟩, hrest⟩ := h
      by_cases ht : t0 ≤ ch.hi
      · exact ⟨ch, List.mem_cons_self, by omega, ht⟩
      · obtain ⟨ch', hch', a, b⟩ := covB_sound cs (ch.hi + 1) T hrest t0 (by omega) h2
        exact ⟨ch', List.mem_cons_of_mem _ hch', a, b⟩

def nodeB (r : T1Rec4) (cs : List Chunk) : Bool :=
  covB (-(tmB (ctxR r) 0)) cs (tmB (ctxR r) 0) && cs.all (chunkB r)

/-- **Child-list completeness.**  If `nodeB` accepts the chunks of the node `r`, every `y` passing `ChildPass4` has a stored,
checked leaf record with the same coordinates `t`. -/
theorem node_sound (r : T1Rec4) (c : T1Chk r) (cs : List Chunk) (h : nodeB r cs = true) (y : V4)
    (hp : ChildPass4 (r.toNode c) y) :
    ∃ ch ∈ cs, ∃ j < ch.cnt, (decLeaf (recOf ch.bl j)).t = tvec r.b y ∧ LeafOk r (decLeaf (recOf ch.bl j)) := by
  have hA : 0 < A1 (r.toNode c) := by
    rw [toNode_A1]
    have := c.2.2.2.2.2
    omega
  have hpass := passB_of_pass r c y hp
  have hbox : ∀ i : Fin 3, |tvec r.b y i| ≤ tmB (ctxR r) i := fun i => by
    have := childPass_box4 (r.toNode c) y hp hA i
    rw [toNode_A1, toNode_W1] at this
    exact this
  simp only [nodeB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hcov, hch⟩ := h
  have hb0 := abs_le.1 (hbox 0)
  obtain ⟨ch, hch', hlo, hhi⟩ := covB_sound cs _ _ hcov (tvec r.b y 0) hb0.1 hb0.2
  have hc := hch ch hch'
  simp only [chunkB, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hgo, hleaf⟩ := hc
  have hb1 := abs_le.1 (hbox 1)
  have hb2 := abs_le.1 (hbox 2)
  have hx : (tvec r.b y 0, tvec r.b y 1, tvec r.b y 2) ∈ cands (ctxR r) ch.lo ch.hi := by
    unfold cands
    simp only [List.mem_flatMap, List.mem_map, mem_rngZ]
    exact ⟨tvec r.b y 0, ⟨hlo, hhi⟩, tvec r.b y 1, ⟨hb1.1, hb1.2⟩, tvec r.b y 2, ⟨hb2.1, hb2.2⟩, rfl⟩
  have ht : (![(tvec r.b y 0, tvec r.b y 1, tvec r.b y 2).1, (tvec r.b y 0, tvec r.b y 1, tvec r.b y 2).2.1,
      (tvec r.b y 0, tvec r.b y 1, tvec r.b y 2).2.2] : Fin 3 → ℤ) = tvec r.b y := by
    funext i; fin_cases i <;> rfl
  have hmem := goB_sound _ _ _ hgo _ hx (by rw [ht]; exact hpass)
  unfold stOf at hmem
  simp only [List.mem_map, List.mem_range] at hmem
  obtain ⟨j, hj, hjt⟩ := hmem
  refine ⟨ch, hch', j, hj, ?_, ?_⟩
  · funext i
    have e0 := congrArg Prod.fst hjt
    have e1 := congrArg (fun p => p.2.1) hjt
    have e2 := congrArg (fun p => p.2.2) hjt
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
  · have := hleaf j (List.mem_range.2 hj)
    simpa [leafB] using this

end

end L4S5
end LRSpectrumFull
