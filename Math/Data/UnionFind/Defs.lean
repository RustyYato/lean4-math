import Math.Type.Notation
import Math.Data.WellFounded.Basic
import Math.Data.Setoid.Basic

namespace UnionFind.Pre

end UnionFind.Pre

structure UnionFind where
  indices: Array ℕ
  -- the indicies are well formed when all indices are in bounds of the array
  inBounds: ∀i ∈ indices, i < indices.size
  -- and when following the chain of indices until you find a root (an indices whihc points to itself)
  -- is well founded. This the smallest relation which allows implementing `UnionFind.find`
  wellFormed: ∀idx: Fin indices.size, Acc (fun i j: Fin indices.size => i = indices[j] ∧ i ≠ j) idx

namespace UnionFind

def size (uf: UnionFind) := uf.indices.size

def step (uf: UnionFind) (i: ℕ) (hi: i < uf.size := by get_elem_tactic) : Fin uf.size where
  val := uf.indices[i]
  isLt := by
    apply uf.inBounds
    apply Array.getElem_mem

@[simp] def mk_step (a: Array ℕ) {b c} (i: ℕ) (hi: i < a.size) : (UnionFind.mk a b c).step i = a[i] := rfl
@[simp] def mk_size (a: Array ℕ) {b c} : (UnionFind.mk a b c).size = a.size := rfl

def step_congr (uf uf': UnionFind) (i: ℕ) (hi: i < uf.size) (h: uf = uf'):
  uf.step i = (uf'.step i (h ▸ hi)).cast (by rw [h]) := by
  subst h
  rfl

def stepped_from (uf: UnionFind) : ℕ -> ℕ -> Prop :=
  fun i j: ℕ => ∃hj: j < uf.size, i = uf.step j ∧ i ≠ j

def lt (uf: UnionFind) : ℕ -> ℕ -> Prop := Relation.TransGen uf.stepped_from

def le (uf: UnionFind) : ℕ -> ℕ -> Prop :=
  Relation.or_eqv uf.lt (· = ·)

instance (uf: UnionFind) : Relation.IsWellFounded uf.stepped_from where
  wf := by
    apply WellFounded.intro
    intro a
    if ha:a < uf.size then
      generalize ha':Fin.mk a ha = a'
      induction uf.wellFormed a' generalizing a with
      | _ a' _ ih =>
      subst a'
      apply Acc.intro
      rintro b ⟨a_inb, rfl, ne⟩
      apply ih ⟨_, _⟩
      apply And.intro
      rfl
      intro h; apply ne
      rw [←Fin.val_inj] at h
      assumption
      rfl
    else
      apply Acc.intro
      intro _ ⟨_, _, _⟩
      contradiction

instance (uf: UnionFind) : Relation.IsWellFounded uf.lt :=
  inferInstanceAs (Relation.IsWellFounded (Relation.TransGen _))

instance (uf: UnionFind) : Relation.IsStrictPartialOrder uf.lt where
  trans := Relation.TransGen.trans

instance (uf: UnionFind) : Relation.IsLawfulNonstrict uf.le uf.lt (· = ·) :=
  inferInstanceAs (Relation.IsLawfulNonstrict (Relation.or_eqv _ _) _ _)

instance (uf: UnionFind) : Relation.IsLawfulStrict uf.le uf.lt :=
  inferInstanceAs (Relation.IsLawfulStrict (Relation.or_eqv _ _) _)

instance (uf: UnionFind) : Relation.IsPartialOrder uf.le (· = ·) :=
  inferInstanceAs (Relation.IsPartialOrder (Relation.or_eqv _ _) _)

def isRoot (uf: UnionFind) (i: ℕ) (hi: i < uf.size := by get_elem_tactic) : Prop := uf.step i = i

instance (uf: UnionFind) (i: ℕ) (hi: i < uf.size) : Decidable (uf.isRoot i) :=
  inferInstanceAs (Decidable (_ = _))

def findAt (uf: UnionFind) (i: Fin uf.size) : Fin uf.size :=
  if uf.isRoot i then
    i
  else
    uf.findAt (uf.step i)
termination_by WellFounded.wrap i (uf.wellFormed i)
decreasing_by
  apply And.intro
  rfl
  simp [WellFounded.wrap]
  rw [←Fin.val_inj]
  assumption

def find (i: ℕ) : UnionFind -> ℕ :=
  fun uf =>
    if hi:i < uf.size then
      uf.findAt ⟨i, hi⟩
    else
      i

def find_eq_findAt (uf: UnionFind) (i: ℕ) (hi: i < uf.size := by get_elem_tactic) : uf.find i = uf.findAt ⟨i, hi⟩ := by
  rw [find, dif_pos hi]

def findAt_step (uf: UnionFind) (i: Fin uf.size) : uf.findAt i = uf.findAt (uf.step i) := by
  conv => { lhs; unfold findAt }
  split
  · rename_i h
    conv => { rhs; arg 2; rw [Fin.val_inj.mp h] }
    unfold findAt
    rw [if_pos h]
  · rfl

def find_step (uf: UnionFind) (i: ℕ) (hi: i < uf.size) : uf.find i = uf.find (uf.step i) := by
  unfold find
  rw [dif_pos hi, dif_pos (Fin.isLt _)]
  rw [findAt_step]

def find_lt_size (i: ℕ) (uf: UnionFind) (hi: i < uf.size) : uf.find i < uf.size := by
  unfold find
  rw [dif_pos hi]
  apply Fin.isLt

macro_rules
| `(tactic|get_elem_tactic) => `(tactic|apply find_lt_size <;> assumption)

def findAt_root (uf: UnionFind) (i: Fin uf.size) : uf.isRoot (uf.findAt i) := by
  induction i using findAt.induct uf with
  | case1 i hi =>
    simp [findAt, hi]
  | case2 i hi ih =>
    unfold findAt
    conv => { lhs; arg 1; rw [if_neg hi] }
    assumption

def find_root (i: ℕ) (uf: UnionFind) (hi: i < uf.size := by get_elem_tactic) : uf.isRoot (uf.find i) := by
  unfold find
  simp [hi]
  apply findAt_root

def new (n: ℕ) : UnionFind where
  indices := Array.ofFn (n := n) Fin.val
  inBounds := by
    intro i hi
    rw [Array.mem_ofFn] at hi
    obtain ⟨i, rfl⟩ := hi
    rw [Array.size_ofFn]
    apply i.isLt
  wellFormed := by
    intro ⟨i, hi⟩
    apply Acc.intro
    intro ⟨j, hj⟩ h
    simp at h

def size_new (n: ℕ) : (new n).size = n := by simp [new]

macro_rules
| `(tactic|get_elem_tactic) => `(tactic|rw [size_new]; get_elem_tactic)

private def mergeRoot (uf: UnionFind) (i j: ℕ)
  (hi: i < uf.size := by get_elem_tactic) (hj: j < uf.size := by get_elem_tactic)
  (gj: uf.isRoot j) : UnionFind where
  indices := uf.indices.set i j
  inBounds := by
    intro x hx
    rw [Array.size_set]
    rw [Array.mem_def] at hx
    rcases List.mem_or_eq_of_mem_set hx with h | h
    apply uf.inBounds
    refine Array.mem_def.mpr ?_
    assumption
    rwa [h]
  wellFormed := by
    intro ⟨x, hx⟩
    rw [Array.size_set] at hx
    generalize hx₀:Fin.mk x hx = x₀
    induction (uf.wellFormed x₀) generalizing x with
    | _ x₀ h ih =>
    subst x₀
    apply Acc.intro
    intro ⟨y, yLt⟩ h₀
    simp at h₀
    rw [Array.getElem_set] at h₀
    split at h₀ <;> rename_i h₁
    · subst x
      cases h₀.left
      replace h₀ := h₀.right
      apply Acc.intro
      intro ⟨y, yLt⟩ h₂
      simp at h₂
      rw [Array.getElem_set] at h₂
      rw [if_neg] at h₂
      replace h₂ : y = uf.step j ∧ _ := h₂
      rw [gj] at h₂
      simp at h₂
      rintro rfl
      contradiction
    · replace h₀ : y = uf.step x _ ∧ y ≠ x := h₀
      cases h₀.left
      apply ih ⟨uf.step x _, _⟩
      apply And.intro
      rfl
      intro h
      have := Fin.val_inj.mpr h
      apply h₀.right
      simpa using this
      rfl
      conv at yLt => { rhs; rw [Array.size_set] }
      assumption

def Policy (uf: UnionFind) := ∀i j: ℕ, ∀(hi: i < uf.size) (hj: j < uf.size), uf.isRoot i -> uf.isRoot j -> Bool

def alwaysLeft (uf: UnionFind) : uf.Policy := fun _ _ _ _ _ _ => true

def mergeAtAux (uf: UnionFind) (setLeftToRight: uf.Policy) (i j: ℕ) : UnionFind × Option Bool :=
  if h:i < uf.size ∧ j < uf.size then by
    let i' := uf.findAt ⟨i, h.left⟩
    let j' := uf.findAt ⟨j, h.right⟩
    have hi' : uf.isRoot i' := by apply findAt_root
    have hj' : uf.isRoot j' := by apply findAt_root
    have b := setLeftToRight i' j' (by get_elem_tactic) (by get_elem_tactic) hi' hj'
    refine (bif b then
      uf.mergeRoot i' j' (by get_elem_tactic) _ hj'
    else
      uf.mergeRoot j' i' (by get_elem_tactic) _ hi', b)
  else
    (uf, .none)

def mergeAt (uf: UnionFind) (setLeftToRight: uf.Policy) (i j: ℕ) : UnionFind :=
  (mergeAtAux uf setLeftToRight i j).fst

@[simp]
def size_mergeRoot (uf: UnionFind) {i j hi hj gj} : (uf.mergeRoot i j hi hj gj).size = uf.size := by
  simp [UnionFind.mergeRoot, size]

@[simp]
def size_mergeAt (uf: UnionFind) {policy i j} : (uf.mergeAt policy i j).size = uf.size := by
  unfold mergeAt mergeAtAux
  split
  simp
  unfold cond
  split
  simp
  simp
  rfl

macro_rules
| `(tactic|get_elem_tactic) => `(tactic|rw [size_mergeAt]; get_elem_tactic)

instance (uf: UnionFind) (i: ℕ) (hi: i < uf.size) : Decidable (uf.isRoot i) := by
  delta isRoot
  infer_instance

def setoid (uf: UnionFind) : Setoid ℕ := Setoid.eqSetoid.comap uf.find
def eqv (uf: UnionFind) : ℕ -> ℕ -> Prop := uf.setoid.r

scoped notation x:50 " ≈[" uf "] " y:51 => eqv uf x y

instance (uf: UnionFind) : Relation.IsEquiv (· ≈[uf] ·) where
  refl := uf.setoid.refl
  symm := uf.setoid.symm
  trans := uf.setoid.trans

def step_le (uf: UnionFind) (i: ℕ) (hi: i < uf.size) : uf.le (uf.step i) i := by
  refine if h:uf.isRoot i then  ?_ else ?_
  rw [h]
  left
  apply Relation.TransGen.single
  refine ⟨hi, rfl, ?_⟩
  assumption

def findAt_le (uf: UnionFind) (i: Fin uf.size) : uf.le (uf.findAt i) i := by
  obtain ⟨i, hi⟩ := i
  induction i using Relation.wfInduction uf.stepped_from with
  | _ i ih =>
  unfold findAt
  split
  rfl
  suffices uf.stepped_from (uf.step i) i by
    apply Relation.trans'
    · apply ih
      assumption
    · show uf.le (uf.step i) i
      left; apply Relation.TransGen.single
      assumption
  show uf.stepped_from (uf.step i) i
  refine ⟨hi, rfl, ?_⟩
  assumption

def find_le (uf: UnionFind) (i: ℕ) : uf.le (uf.find i) i := by
  unfold find
  split
  apply findAt_le
  rfl

def mergeAt_cond (uf: UnionFind) (policy: uf.Policy) (i j: ℕ) (hi: i < uf.size) (hj: j < uf.size) := policy (uf.findAt ⟨i, hi⟩) (uf.findAt ⟨j, hj⟩) (by simp) (by simp) (findAt_root uf ⟨i, hi⟩) (findAt_root uf ⟨j, hj⟩)

def mergeAt_left (uf: UnionFind) (policy: uf.Policy) (i j: ℕ) (hi: i < uf.size) (hj: j < uf.size) (h: uf.mergeAt_cond policy i j hi hj = true) :
  uf.mergeAt policy i j = uf.mergeRoot (uf.findAt ⟨i, hi⟩) (uf.findAt ⟨j, hj⟩) (by simp) (by simp) (findAt_root uf ⟨j, hj⟩) := by
  unfold mergeAt mergeAtAux
  unfold mergeAt_cond at h
  simp [hi, hj, cond, h]

def mergeAt_right (uf: UnionFind) (policy: uf.Policy) (i j: ℕ) (hi: i < uf.size) (hj: j < uf.size) (h: uf.mergeAt_cond policy i j hi hj = false) :
  uf.mergeAt policy i j = uf.mergeRoot (uf.findAt ⟨j, hj⟩) (uf.findAt ⟨i, hi⟩) (by simp) (by simp) (findAt_root uf ⟨i, hi⟩) := by
  unfold mergeAt mergeAtAux
  unfold mergeAt_cond at h
  simp [hi, hj, cond, h]

def mergeAt_stepped_from (uf: UnionFind) {policy} (i j a b: ℕ) (h: uf.stepped_from a b) : (uf.mergeAt policy i j).stepped_from a b := by
  obtain ⟨bLt, rfl, ne⟩ := h
  refine ⟨?_, ?_, ne⟩
  get_elem_tactic
  refine if h:i < uf.size ∧ j < uf.size then ?_ else ?_
  · match g:uf.mergeAt_cond policy i j h.left h.right with
    | true =>
      rw (occs := [2]) [step_congr _ _ _ _ (by
        rw [mergeAt_left (h := g)])]
      simp [UnionFind.mergeRoot]
      rw [Array.getElem_set]
      split
      · subst b
        rw [findAt_root] at ne
        contradiction
      · rfl
    | false =>
      rw (occs := [2]) [step_congr _ _ _ _ (by
        rw [mergeAt_right (h := g)])]
      simp [UnionFind.mergeRoot]
      rw [Array.getElem_set]
      split
      · subst b
        rw [findAt_root] at ne
        contradiction
      · rfl

  · unfold mergeAt mergeAtAux
    rw (occs := [2]) [step_congr _ _ _ _ (by rw [dif_neg h])]
    simp

def mergeAt_lt (uf: UnionFind) {policy} {i j a b: ℕ} (h: uf.lt a b) : (uf.mergeAt policy i j).lt a b := by
  induction h with
  | single =>
    apply Relation.TransGen.single
    apply mergeAt_stepped_from
    assumption
  | tail =>
    apply Relation.TransGen.tail
    assumption
    apply mergeAt_stepped_from
    assumption

def mergeAt_le (uf: UnionFind) {policy} {i j a b: ℕ} (h: uf.le a b) : (uf.mergeAt policy i j).le a b := by
  rcases h with h | rfl
  left
  apply mergeAt_lt
  assumption
  rfl

@[symm]
def eqv_symm {uf: UnionFind} {a b: ℕ} : a ≈[uf] b -> b ≈[uf] a := Relation.symm

def eqv_step (uf: UnionFind) (a: ℕ) (ha: a < uf.size := by get_elem_tactic) : a ≈[uf] (uf.step a) := by
  by_cases h:uf.step a = a
  rw [h]
  show _ = _
  simp
  unfold find
  rw [dif_pos, dif_pos, findAt, if_neg]
  assumption
  assumption

def eqv_of_lt (uf: UnionFind) (i j: ℕ) (h: uf.lt i j): uf.eqv i j := by
  induction h with
  | @single i' h =>
    rcases h with ⟨_, rfl, _⟩
    symm; apply eqv_step
  | tail i h ih =>
    apply Relation.trans' ih
    clear ih
    rcases h with ⟨_, rfl, _⟩
    symm; apply eqv_step

def eqv_of_le (uf: UnionFind) (i j: ℕ) (h: uf.le i j): uf.eqv i j := by
  rcases h with h | rfl
  · apply uf.eqv_of_lt
    assumption
  · rfl

def eqv_findAt (uf: UnionFind) (a: Fin uf.size) : a ≈[uf] uf.findAt a := by
  symm; apply eqv_of_le
  apply findAt_le

def eqv_find (uf: UnionFind) (a: ℕ) : a ≈[uf] uf.find a := by
  symm; apply eqv_of_le
  apply find_le

def eqv_mergeAt_lift (uf: UnionFind) {policy} (i j: ℕ) (h: i₀ ≈[uf] j₀)  : i₀ ≈[uf.mergeAt policy i j] j₀ := by
  apply Relation.trans'
  symm; apply eqv_of_le
  apply mergeAt_le
  apply find_le
  apply flip Relation.trans'
  apply eqv_of_le
  apply mergeAt_le
  apply find_le
  replace h : _ = _ := h
  simp at h
  rw [h]

def mergeAt_spec (uf: UnionFind) {policy} (i j: ℕ) (hi: i < uf.size) (hj: j < uf.size) : i ≈[uf.mergeAt policy i j] j := by
  apply Relation.trans'
  apply eqv_mergeAt_lift
  apply eqv_find
  apply flip Relation.trans'
  apply eqv_mergeAt_lift
  symm; apply eqv_find
  refine if hij:uf.find i = uf.find j then ?_ else ?_
  rw [hij]
  generalize huf':uf.mergeAt policy i j = uf'
  cases hc:uf.mergeAt_cond policy i j hi hj
  · rw [mergeAt_right (h := hc)] at huf'
    apply eqv_of_lt
    apply Relation.TransGen.single
    refine ⟨?_, ?_, ?_⟩
    subst uf'; simp [UnionFind.mergeRoot]
    apply find_lt_size
    assumption
    subst uf'
    simp [UnionFind.mergeRoot]
    conv => { rhs; arg 2; rw [find_eq_findAt _ j] }
    simp
    apply find_eq_findAt
    assumption
  · rw [mergeAt_left (h := hc)] at huf'
    symm; apply eqv_of_lt
    apply Relation.TransGen.single
    refine ⟨?_, ?_, ?_⟩
    subst uf'; simp [UnionFind.mergeRoot]
    apply find_lt_size
    assumption
    subst uf'
    simp [UnionFind.mergeRoot]
    conv => { rhs; arg 2; rw [find_eq_findAt _ i] }
    simp
    apply find_eq_findAt
    symm
    assumption

def new_root (n i: ℕ) (hi: i < n) : (UnionFind.new n).isRoot i := by
  simp [new, isRoot]

def root_spec (uf: UnionFind) (i j: ℕ) (hi: i < uf.size) (hj: j < uf.size) :
  uf.isRoot i -> uf.isRoot j ->
  i ≈[uf] j -> i = j := by
  intro ri rj h
  replace h : _ = _ := h
  simp at h
  unfold find findAt at h
  simpa [hi, hj, ri, rj] using h

def new_spec (n i j: ℕ) (hi: i < n) (hj: j < n) : i ≈[UnionFind.new n] j -> i = j := by
  apply root_spec
  apply new_root
  assumption
  apply new_root
  assumption

end UnionFind
