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

instance : GetElem UnionFind ℕ ℕ (fun uf n => n < uf.size) where
  getElem uf i h := uf.indices[i]

def findAt (uf: UnionFind) (i: Fin uf.size) : Fin uf.size :=
  if uf[i] = i then
    i
  else
    uf.findAt ⟨uf[i], by
      apply uf.inBounds
      apply Array.getElem_mem⟩
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

def find_lt_size (i: ℕ) (uf: UnionFind) (hi: i < uf.size) : uf.find i < uf.size := by
  unfold find
  rw [dif_pos hi]
  apply Fin.isLt

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
    refine bif setLeftToRight i' j' (by get_elem_tactic) (by get_elem_tactic) hi' hj' then
      (uf.mergeRoot i' j' (by get_elem_tactic) _ hj', true)
    else
      (uf.mergeRoot j' i' (by get_elem_tactic) _ hi', false)
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

@[simp] def mk_getElem (a: Array ℕ) {b c} (i: ℕ) (hi: i < a.size) : (UnionFind.mk a b c)[i]'(hi) = a[i]'(hi) := rfl

def eqv_step (uf: UnionFind) (a: ℕ) (ha: a < uf.size := by get_elem_tactic) : a ≈[uf] uf[a] := by
  by_cases h:uf[a] = a
  rw [h]
  show _ = _
  simp
  unfold find
  rw [dif_pos, dif_pos, findAt, if_neg]
  rfl
  assumption
  assumption

def eqv_findAt (uf: UnionFind) (a: Fin uf.size) : a ≈[uf] uf.findAt a := by
  induction a using findAt.induct with
  | case1 _ h =>
    unfold findAt
    rw [if_pos h]
  | case2 x h ih =>
    rw [findAt, if_neg h]
    apply Relation.trans' _ ih
    apply eqv_step

def eqv_find (uf: UnionFind) (a: ℕ) : a ≈[uf] uf.find a := by
  unfold find
  split
  apply eqv_findAt _ ⟨_, _⟩
  rfl

end UnionFind
