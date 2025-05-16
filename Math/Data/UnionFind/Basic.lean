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

def get (uf: UnionFind) (i: ℕ) (hi: i < uf.size := by get_elem_tactic) : Fin uf.size where
  val := uf.indices[i]
  isLt := by
    apply uf.inBounds
    apply Array.getElem_mem

instance : GetElem UnionFind ℕ ℕ (fun uf n => n < uf.size) where
  getElem uf i h := uf.get i

@[simp] def mk_getElem (a: Array ℕ) {b c} (i: ℕ) (hi: i < a.size) : (UnionFind.mk a b c)[i]'(hi) = a[i]'(hi) := rfl

def findAt (uf: UnionFind) (i: Fin uf.size) : Fin uf.size :=
  if uf[i] = i then
    i
  else
    uf.findAt (uf.get i)
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

def step (uf: UnionFind) (i: ℕ) : ℕ :=
  if hi:i < uf.size then
    uf[i]
  else
    i

def find_step (uf: UnionFind) : uf.find i = uf.find (uf.step i) := by
  unfold find step
  split
  · rw [dif_pos]
    rw [findAt]
    split
    rw [findAt, if_pos]
    symm; assumption
    simp
    congr
    apply uf.inBounds
    apply Array.getElem_mem
    rfl
  · rfl

def find_lt_size (i: ℕ) (uf: UnionFind) (hi: i < uf.size) : uf.find i < uf.size := by
  unfold find
  rw [dif_pos hi]
  apply Fin.isLt

def StrictStep (uf: UnionFind) : Fin uf.size -> Fin uf.size -> Prop := fun i j: Fin uf.size => i = uf.get j ∧ i ≠ j
abbrev StrictPath (uf: UnionFind) : Fin uf.size -> Fin uf.size -> Prop := Relation.TransGen uf.StrictStep

instance (uf: UnionFind) : Relation.IsWellFounded uf.StrictStep where
  wf := by
    apply WellFounded.intro
    intro a
    induction uf.wellFormed a with
    | _ a h ih =>
    clear h
    apply Acc.intro
    intro b hb
    apply ih
    apply And.intro _ hb.right
    replace hb := hb.left
    rw [hb]
    rfl

inductive Path (uf: UnionFind) : ℕ -> ℕ -> Prop where
| refl (i: ℕ) : Path uf i i
| step (i j: ℕ) (hi: i < uf.size) : Path uf uf[i] j -> Path uf i j

macro_rules
| `(tactic|get_elem_tactic) => `(tactic|apply find_lt_size <;> assumption)

def isRoot (uf: UnionFind) (i: ℕ) (hi : i < uf.size := by get_elem_tactic) := uf[i] = i

def findAt_root (uf: UnionFind) (i: Fin uf.size) : uf[uf.findAt i] = uf.findAt i := by
  induction i using findAt.induct uf with
  | case1 i hi =>
    simp [findAt, hi]
  | case2 i hi ih =>
    unfold findAt
    replace hi : uf[i] ≠ i.val := hi
    conv => { lhs; lhs; rw [if_neg hi] }
    rw [ih]
    rw [if_neg hi]

def find_root (i: ℕ) (uf: UnionFind) (hi: i < uf.size := by get_elem_tactic) : uf.isRoot (uf.find i) := by
  unfold isRoot find
  conv => { lhs; lhs; rw [dif_pos hi] }
  conv => { rhs; rw [dif_pos hi] }
  apply findAt_root

def findAt_root' (uf: UnionFind) (i: Fin uf.size) : uf.isRoot (uf.findAt i) := by
  conv => {
    lhs; rw [show uf.findAt i = uf.find i.val from (by
      unfold find
      rw [dif_pos])]
  }
  apply find_root
  exact i.isLt

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
      replace h₂ : y = uf[j] ∧ _ := h₂
      rw [gj] at h₂
      simp at h₂
      rintro rfl
      contradiction
    · replace h₀ : y = uf[x]'_ ∧ y ≠ x := h₀
      cases h₀.left
      apply ih ⟨uf[x]'_, _⟩
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
    have hi' : uf.isRoot i' := by apply findAt_root'
    have hj' : uf.isRoot j' := by apply findAt_root'
    let b := setLeftToRight i' j' (by get_elem_tactic) (by get_elem_tactic) hi' hj'
    refine (bif setLeftToRight i' j' (by get_elem_tactic) (by get_elem_tactic) hi' hj' then
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

def getElem_inbounds (uf: UnionFind) (x: ℕ) (hx: x < uf.size) : uf[x] < uf.size  := by
  apply uf.inBounds
  apply Array.getElem_mem

macro_rules
| `(tactic|get_elem_tactic) => `(tactic|apply getElem_inbounds <;> get_elem_tactic)

def getElem_eq_self_of_find_eq_self (uf: UnionFind) (x: ℕ) (hx: x < uf.size) : uf.find x = x -> uf[x] = x := by
  intro h
  apply Decidable.byContradiction
  intro g
  have : uf.StrictPath (uf.get x) ⟨x, hx⟩ := by
    apply Relation.TransGen.single
    apply And.intro
    rfl
    intro h; apply g
    apply Fin.val_inj.mpr h
  have : uf.Path uf[x] x := by
    conv => { rhs; rw [←h] }
    clear h this
    unfold find
    rw [dif_pos hx]
    unfold findAt
    rw [if_neg]
    simp


    sorry


  have := Acc.inv (y := ⟨uf[x], (by get_elem_tactic)⟩) (uf.wellFormed ⟨x, hx⟩) ⟨rfl, by
    intro h
    have := Fin.val_inj.mpr h
    contradiction⟩



  sorry

def mergeAt_inbounds (uf: UnionFind) {policy i j} (x: ℕ) : x < uf.size -> x < (uf.mergeAt policy i j).size  := by simp

macro_rules
| `(tactic|get_elem_tactic) => `(tactic|apply mergeAt_inbounds <;> get_elem_tactic)

def mergeAt_cond (uf: UnionFind) (policy: uf.Policy) (i j: ℕ) (hi: i < uf.size) (hj: j < uf.size) := policy (uf.findAt ⟨i, hi⟩) (uf.findAt ⟨j, hj⟩) (by simp) (by simp) (findAt_root' uf ⟨i, hi⟩) (findAt_root' uf ⟨j, hj⟩)

def getElem_mergeAt_left (uf: UnionFind) (policy: uf.Policy) (i j: ℕ) (hi: i < uf.size) (hj: j < uf.size) (h: uf.mergeAt_cond policy i j hi hj = true) :
  uf.mergeAt policy i j = uf.mergeRoot (uf.findAt ⟨i, hi⟩) (uf.findAt ⟨j, hj⟩) (by simp) (by simp) (findAt_root' uf ⟨j, hj⟩) := by
  unfold mergeAt mergeAtAux
  unfold mergeAt_cond at h
  simp [hi, hj, cond, h]

def getElem_mergeAt_right (uf: UnionFind) (policy: uf.Policy) (i j: ℕ) (hi: i < uf.size) (hj: j < uf.size) (h: uf.mergeAt_cond policy i j hi hj = false) :
  uf.mergeAt policy i j = uf.mergeRoot (uf.findAt ⟨j, hj⟩) (uf.findAt ⟨i, hi⟩) (by simp) (by simp) (findAt_root' uf ⟨i, hi⟩) := by
  unfold mergeAt mergeAtAux
  unfold mergeAt_cond at h
  simp [hi, hj, cond, h]

@[simp]
def findAt_idempot (uf: UnionFind) (x: Fin uf.size) : uf.findAt (uf.findAt x) = uf.findAt x := by
  induction x using findAt.induct with
  | case1 x h =>
    generalize hx':uf.findAt x = x'
    unfold findAt at hx'
    simp [h] at hx'
    subst x
    unfold findAt
    simp [h]
  | case2 x h ih =>
    generalize hx':uf.findAt x = x'
    unfold findAt at hx'
    rw [if_neg h] at hx'
    subst x'
    assumption

def inbounds_of_find_ne (uf: UnionFind) (x) (h: uf.find x ≠ x) : x < uf.size := by
  unfold find at h
  split at h
  assumption
  contradiction

macro_rules
| `(tactic|get_elem_tactic) => `(tactic|apply inbounds_of_find_ne <;> assumption)

def getElem_mergeAt_of_not_root (uf: UnionFind) {policy i j x} (h: uf.find x ≠ x) : (uf.mergeAt policy i j)[x] = uf[x] := by
  refine if g:i < uf.size ∧ j < uf.size then ?_ else ?_
  · match g₀:uf.mergeAt_cond policy i j g.left g.right with
    | false =>
      conv => { lhs; arg 1; rw [getElem_mergeAt_right (h := g₀)] }
      simp [mergeRoot]
      rw [Array.getElem_set]
      split
      rename_i h₀
      unfold find at h
      split at h
      · subst x
        rename_i h₀ h₁
        simp at h₀
      · contradiction
      · rfl
    | true =>
      conv => { lhs; arg 1; rw [getElem_mergeAt_left (h := g₀)] }
      simp [mergeRoot]
      rw [Array.getElem_set]
      split
      rename_i h₀
      unfold find at h
      split at h
      · subst x
        rename_i h₀ h₁
        simp at h₀
      · contradiction
      · rfl
  · unfold mergeAt mergeAtAux
    simp [g]

def getElem_mergeAt_of_ne (uf: UnionFind) {policy i j x} (hi: x ≠ i) (hj: x ≠ j) (hx: x < uf.size) : (uf.mergeAt policy i j)[x] = uf[x] := by
  suffices uf.find x = x -> (uf.mergeAt policy i j)[x] = uf[x]  by
    by_cases hx₀:uf.find x = x
    · apply this
      assumption
    · apply getElem_mergeAt_of_not_root
      assumption
  intro hx₀


def mergeAt_path (uf: UnionFind) (a b: ℕ) : uf.Path a b -> ∀policy i j, (uf.mergeAt policy i j).Path a b := by
  intro h
  induction h with
  | refl =>
    intros
    apply Path.refl
  | step a b ha path ih =>
    intro policy i j
    apply Path.step a b (by simpa)
    rw [getElem_mergeAt]
    sorry
    sorry
    -- apply ih

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

@[symm]
def eqv_symm {uf: UnionFind} {a b: ℕ} : a ≈[uf] b -> b ≈[uf] a := Relation.symm

def eqv_getElem (uf: UnionFind) (a: ℕ) (ha: a < uf.size := by get_elem_tactic) : a ≈[uf] uf[a] := by
  by_cases h:uf[a] = a
  rw [h]
  show _ = _
  simp
  unfold find
  rw [dif_pos, dif_pos, findAt, if_neg]
  rfl
  assumption
  assumption

def eqv_step (uf: UnionFind) (a: ℕ) : a ≈[uf] uf.step a := by
  unfold step
  split
  apply eqv_getElem
  rfl

def eqv_findAt (uf: UnionFind) (a: Fin uf.size) : a ≈[uf] uf.findAt a := by
  induction a using findAt.induct with
  | case1 _ h =>
    unfold findAt
    rw [if_pos h]
  | case2 x h ih =>
    rw [findAt, if_neg h]
    apply Relation.trans' _ ih
    apply eqv_getElem

def eqv_find (uf: UnionFind) (a: ℕ) : a ≈[uf] uf.find a := by
  unfold find
  split
  apply eqv_findAt _ ⟨_, _⟩
  rfl

def eqv_of_path (uf: UnionFind) (a b: ℕ) (h: uf.Path a b) : a ≈[uf] b := by
  induction h with
  | refl => rfl
  | step i j hi gj ih =>
    apply Relation.trans' _ ih
    apply eqv_getElem

def lift_eqv_mergeAt (uf: UnionFind) (policy: uf.Policy) (i j: ℕ) (h: i₀ ≈[uf] j₀) : i₀ ≈[uf.mergeAt policy i j] j₀ := by
  replace h : _ = _ := h
  simp at h
  unfold find at h
  split at h
  · split at h
    · rename_i h₀ h₁
      generalize hi₁:Fin.mk i₀ h₀ = i₁
      show _ = _
      simp
      unfold find
      rw [dif_pos (by simpa), dif_pos (by simpa)]
      induction uf.wellFormed i₁ generalizing i₀ j₀ with
      | _ i₁ h ih =>
      refine if g₀:i₀ = j₀ then ?_ else ?_
      subst j₀; rfl
      subst i₁; clear h
      refine if g:uf.findAt ⟨i₀, h₀⟩ = i₀ then ?_ else ?_
      rw [g] at h
      · conv => { rhs; unfold findAt }
        rw [if_neg]
        simp
        congr
        · sorry
        · intro g₁
          simp at g₁
          rw [←g₁] at g₀

          sorry
      · sorry


    --   rename_i i₂ g; subst hi₁; clear g
    --   unfold findAt
    --   split <;> split <;> simp
    --   · rename_i g₀ g₁
    --     unfold findAt at h
    --     rw [if_pos, if_pos] at h
    --     assumption
    --     simp

    --     sorry
    --     sorry
    --   repeat sorry
    · rename_i h₀ h₁
      rw [← h] at h₁
      exfalso
      apply h₁
      apply Fin.isLt
  · sorry

def eqv_mergeAt (uf: UnionFind) (policy: uf.Policy) (i j: ℕ) (hi: i < uf.size) (hj: j < uf.size) : i ≈[uf.mergeAt policy i j] j := by
  apply Relation.trans'
  apply lift_eqv_mergeAt
  apply eqv_findAt (a := ⟨i, hi⟩)
  apply flip Relation.trans'
  symm
  apply lift_eqv_mergeAt
  apply eqv_findAt (a := ⟨j, hj⟩)
  unfold mergeAt mergeAtAux
  simp
  let i' := uf.findAt ⟨i, hi⟩
  let j' := uf.findAt ⟨j, hj⟩
  rw [dif_pos (by trivial)]
  unfold cond
  split
  · simp
    conv => {
      rhs
      rw [show uf.findAt ⟨j, hj⟩ = (uf.mergeRoot (uf.findAt ⟨i, hi⟩) (uf.findAt ⟨j, hj⟩)
        (Fin.isLt _) (Fin.isLt _) (by exact findAt_root' uf ⟨j, hj⟩))[uf.findAt ⟨i, hi⟩]'(by rw [size_mergeRoot]; apply Fin.isLt) from (by
        simp [UnionFind.mergeRoot])]
    }
    apply eqv_getElem
  · simp
    conv => {
      lhs
      rw [show uf.findAt ⟨i, hi⟩ = (uf.mergeRoot (uf.findAt ⟨j, hj⟩) (uf.findAt ⟨i, hi⟩)
        (Fin.isLt _) (Fin.isLt _) (by exact findAt_root' uf ⟨i, hi⟩))[uf.findAt ⟨j, hj⟩]'(by rw [size_mergeRoot]; apply Fin.isLt) from (by
        simp [UnionFind.mergeRoot])]
    }
    symm
    apply eqv_getElem

end UnionFind
