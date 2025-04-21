import Math.Logic.Equiv.Basic

structure Function.Vector (α: Type*) (n: Nat) where
  ofFun :: toFun : Fin n -> α

namespace Function.Vector

def nil : Vector α 0 := .ofFun nofun
def cons : α -> Vector α n -> Vector α (n + 1) :=
  fun a f => .ofFun fun
  | 0 => a
  | ⟨n + 1, h⟩ => f.toFun ⟨n, Nat.lt_of_succ_lt_succ h⟩

instance : GetElem (Vector α n) (Fin n) α (fun _ _ => True) where
  getElem v x _ := v.toFun x

def Nodup (v: Vector α n) := Function.Injective v.toFun

scoped infixr:67 "::ᵥ" => Vector.cons
instance : EmptyCollection (Vector α 0) where
  emptyCollection := nil

@[simp]
def getElem_ofFun (f: Fin n -> α) : (ofFun f)[i] = f i := rfl

@[simp]
def getElem_cons_zero (a: α) (v: Vector α n) :
  (a::ᵥv)[(0: Fin (n + 1))] = a := rfl

@[simp]
def getElem_cons_succ (a: α) (v: Vector α n) (i: Fin n) :
  (a::ᵥv)[i.succ] = v[i] := rfl

def getElem_cons (a: α) (v: Vector α n) (i: Fin (n + 1)) :
  (a::ᵥv)[i] = if h:i = 0 then a else v[i.pred h] := by
  cases i using Fin.cases
  rfl
  rfl

@[ext]
def ext (a b: Vector α n) : (∀i: Fin n, a[i] = b[i]) -> a = b := by
  intro h
  cases a; cases b; congr
  ext i; apply h

def hext (a: Vector α n) (b: Vector α m) (h: n = m) : (∀i: Fin n, a[i] = b[i.cast h]) -> HEq a b := by
  cases h
  simp; apply ext

instance : Subsingleton (Vector α 0) where
  allEq a b := by ext i; exact i.elim0

def head (v: Vector α (n + 1)) : α := v[(0: Fin (n + 1))]

def tail (v: Vector α n) : Vector α (n - 1) :=
  match n with
  | 0 => .nil
  | n + 1 => .ofFun fun i: Fin n => v[i.succ]

@[simp]
def cons_head_tail (v: Vector α (n + 1)) : v.head::ᵥv.tail = v := by
  ext i; dsimp at i
  cases i using Fin.cases
  rfl
  rfl

@[induction_eliminator]
def recCons {motive: ∀{n}, Vector α n -> Sort*}
  (nil: motive .nil)
  (cons: ∀{n} (a: α) (v: Vector α n), motive v -> motive (a ::ᵥ v)) :
  ∀{n} (v: Vector α n), motive v
| 0 => fun v => cast (by rw [Subsingleton.allEq .nil v]) nil
| n + 1 => fun v => cast (by simp) (cons v.head v.tail (recCons nil cons _))

@[cases_eliminator]
def casesCons {motive: ∀{n}, Vector α n -> Sort*}
  (nil: motive .nil)
  (cons: ∀{n} (a: α) (v: Vector α n), motive (a ::ᵥ v)) :
  ∀{n} (v: Vector α n), motive v
| 0 => fun v => cast (by rw [Subsingleton.allEq .nil v]) nil
| n + 1 => fun v => cast (by simp) (cons v.head v.tail)

def cast (v: Vector α n) (h: n = m) : Vector α m := .ofFun fun i => v[i.cast h.symm]

inductive Perm : Vector α n -> Vector α m -> Prop where
| nil : Perm .nil .nil
| cons : Perm a b -> Perm (x::ᵥa) (x::ᵥb)
| swap (a b: α) (x: Vector α n) :  Perm (a::ᵥb::ᵥx) (b::ᵥa::ᵥx)
| trans {a: Vector α n₀} {b: Vector α n₁} {c: Vector α n₂} : Perm a b -> Perm b c -> Perm a c

@[refl]
def Perm.refl (v: Vector α n) : Perm v v := by
  induction v with
  | nil => apply Perm.nil
  | cons => apply Perm.cons; assumption

@[symm]
def Perm.symm (h: Perm a b) : Perm b a := by
  induction h with
  | nil => apply Perm.nil
  | swap => apply Perm.swap
  | cons => apply Perm.cons; assumption
  | trans => apply Perm.trans <;> assumption

@[symm]
def Perm.length_eq {a: Vector α n} {b: Vector α m} (h: Perm a b) : n = m := by
  induction h with
  | nil => rfl
  | swap => rfl
  | cons => congr
  | trans _ _ ih₀ ih₁ => rw [ih₀, ih₁]

def set (v: Vector α n) (i: Fin n) (a: α) : Vector α n where
  toFun x := if x = i then a else v[x]

def getElem_set (v: Vector α n) (i x: Fin n) (a: α) :
  (v.set i a)[x] = if x = i then a else v[x] := rfl

@[simp]
def set_cons_zero (v: Vector α n) (a x: α) : ((x::ᵥv).set 0 a) = a::ᵥv := by
  ext i; cases i using Fin.cases
  simp [getElem_set]
  rfl
@[simp]
def set_cons_succ (v: Vector α n) (a x: α) (i: Fin n) : ((x::ᵥv).set i.succ a) = x::ᵥ(v.set i a) := by
  ext i; cases i using Fin.cases
  simp [getElem_set]
  exact nofun
  simp [getElem_set]

def swap (v: Vector α n) (i j: Fin n) :=
  (v.set i v[j]).set j v[i]

@[simp]
def getElem_swap_equiv_swap (v: Vector α n) (i j k: Fin n) :
  (v.swap i j)[Equiv.swap i j k] = v[k] := by
  unfold swap
  rw [Equiv.swap]
  simp [getElem_set]
  split <;> rename_i h
  rw [Equiv.apply_set] at h
  simp at h
  by_cases hk:k = i
  subst k; rfl
  have := h hk
  split at this
  subst i; contradiction
  contradiction
  split <;> rename_i h₁
  rw [Equiv.apply_set] at h₁
  simp at h₁
  split at h₁
  subst i k; rfl
  split at h₁
  subst k; rfl
  subst i; contradiction
  rw [Equiv.apply_set]
  split
  subst k
  rw[ Equiv.apply_set] at h₁
  simp at h₁
  rw [Equiv.apply_set] at h
  simp at h
  split <;> rename_i h₂
  simp at h₂
  subst h₂
  rw [Equiv.apply_set] at h
  simp at h
  rw [Equiv.apply_set] at h₁
  simp at h₁
  rfl

def swap_comm (v: Vector α n) (i j: Fin n) : v.swap i j = v.swap j i := by
  ext x
  unfold swap
  simp [getElem_set]
  split; split; subst x i; rfl
  rfl; split; rfl; rfl

@[simp]
def swap_self (v: Vector α n) (i: Fin n) : v.swap i i = v := by
  ext x
  unfold swap
  simp [getElem_set]
  split; subst x; rfl; rfl

@[simp]
def swap_cons_succ_succ (a: α) (v: Vector α n) (i j: Fin n) : (a::ᵥv).swap i.succ j.succ = a::ᵥ(v.swap i j) := by
  ext x
  unfold swap
  cases x using Fin.cases
  simp
  simp

def append (as: Vector α n) (bs: Vector α m) : Vector α (n + m) where
  toFun i := match Equiv.finSum.symm i with
    | .inl i => as[i]
    | .inr i => bs[i]

instance : HAppend (Vector α n) (Vector α m) (Vector α (n + m)) := ⟨.append⟩

def _root_.Equiv.sigma_vector_equiv_list : (Σn, Vector α n) ≃ List α where
  toFun x := List.ofFn x.snd.toFun
  invFun x := ⟨x.length, .ofFun (x[·])⟩
  leftInv x := by
    simp
    ext; simp
    simp
    refine hext _ _ ?_ ?_
    simp
    intro i
    rfl
  rightInv x := by
    simp; apply List.ext_getElem
    simp
    intro i; simp

def toList (v: Vector α n) : List α :=
  Equiv.sigma_vector_equiv_list ⟨_, v⟩

@[simp]
def legnth_toList (v: Vector α n) : v.toList.length = n :=
  List.length_ofFn

def ofList (l: List α) : Vector α l.length :=
  (Equiv.sigma_vector_equiv_list.symm l).snd

@[simp]
def ofList_ofFn (f: Fin n -> α) : ofList (List.ofFn f) = (ofFun f).cast (by simp) := by
  ext i
  show (List.ofFn _)[i]'_ = _
  simp
  rfl

def toList_inj : Function.Injective (toList (α := α) (n := n)) := by
  unfold toList
  intro x y h
  simpa using Sigma.mk.inj (Equiv.sigma_vector_equiv_list.inj h)

def toList_ofList (l: List α) : toList (ofList l) = l := by
  unfold ofList toList
  apply Equiv.symm_coe

@[simp]
def toList_cast (v: Vector α n) (h: n = m) : (v.cast h).toList = v.toList := by
  cases h
  rfl

def ofList_toList (v: Vector α n) : ofList (toList v) = v.cast (by simp) := by
  apply toList_inj
  rw [toList_ofList, toList_cast]

@[simp] def toList_nil : toList (α := α) .nil = [] := rfl
@[simp] def toList_cons (a: α) (as: Vector α n) : toList (a::ᵥas) = a::as.toList := by
  apply List.ext_getElem
  simp
  unfold toList Equiv.sigma_vector_equiv_list
  intro i h₀ h₁
  simp
  rfl

@[simp] def ofList_nil : ofList (α := α) [] = .nil := by ext i; exact i.elim0
@[simp] def ofList_cons (a: α) (as: List α) : ofList (a::as) = a::ᵥofList as := by
  ext i;
  cases i using Fin.cases
  rfl; rfl

def cast_perm_cast
  {as: Vector α n₀}
  {bs: Vector α m₀}
  (hn: n₀ = n₁) (hm: m₀ = m₁) :
  (as.cast hn).Perm (bs.cast hm) ↔ as.Perm bs := by
  subst hn hm; rfl

def Perm.iff_toList_perm {as: Vector α n} {bs: Vector α m} : as.toList.Perm bs.toList ↔ as.Perm bs := by
  apply Iff.intro
  · intro h
    rw [←cast_perm_cast,
      ←ofList_toList as,
      ←ofList_toList bs]
    revert h
    generalize as.toList = as
    generalize bs.toList = bs
    rename_i as₀ as₁; clear as₀ as₁
    intro h
    induction h with
    | nil => simp; rfl
    | cons => simp; apply Perm.cons; assumption
    | swap => simp; apply Perm.swap
    | trans => apply Perm.trans <;> assumption
  · intro h
    induction h with
    | nil => simp
    | cons => simp; assumption
    | swap => simp; apply List.Perm.swap
    | trans => apply List.Perm.trans <;> assumption

def Perm.iff_ofList_perm {as bs: List α} : (ofList as).Perm (ofList bs) ↔ as.Perm bs := by
  apply Iff.trans iff_toList_perm.symm
  rw [toList_ofList, toList_ofList]

def Perm.cons_inv (h: Perm (a::ᵥas) (a::ᵥbs)) : Perm as bs := by
  have := iff_toList_perm.mpr h
  simp at this
  rwa [iff_toList_perm] at this

private def perm_swap_zero (a: α) (as: Vector α n) (j: Fin n) : (a::ᵥas).Perm ((a::ᵥas).swap 0 j.succ) := by
  unfold swap
  simp
  induction as with
  | nil => exact j.elim0
  | cons a' as ih =>
  cases j using Fin.cases with
  | zero =>
    simp
    apply Perm.swap
  | succ j =>
    simp
    apply Perm.trans
    apply Perm.swap
    apply flip Perm.trans
    apply Perm.swap
    apply Perm.cons
    apply ih

def perm_swap (a: Vector α n) (i j: Fin n) : Perm a (a.swap i j) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases a with | cons a as =>
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simp; rfl
      | succ j => apply perm_swap_zero
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        rw [swap_comm]
        apply perm_swap_zero
      | succ j =>
        simp; apply Perm.cons
        apply ih

def perm_of_equiv (a: Vector α n) (b: Vector α m) (eqv: Fin n ≃ Fin m) (h: ∀i, a[i] = b[eqv i]) : Perm a b := by
  cases Fin.eq_of_equiv eqv
  induction a with
  | nil => rw [Subsingleton.allEq b]
  | cons a as ih =>
    rename_i n
    let i := eqv 0
    let eqv' := (eqv.trans (Equiv.swap 0 i))
    have eqv'_zero : eqv' 0 = 0 := by
      unfold eqv' i
      simp
      rw [Equiv.swap, Equiv.apply_set]
      split
      assumption
      simp
    have eqv'_pos (i: Fin n) : 0 < eqv' i.succ := by
      apply Nat.zero_lt_of_ne_zero
      intro g
      replace g : eqv' i.succ = (0: Fin (n + 1)).val := g
      rw [Fin.val_inj, ←eqv'_zero, eqv'.inj.eq_iff] at g
      nomatch g
    have eqv'_symm_pos (i: Fin n) : 0 < eqv'.symm i.succ := by
      apply Nat.zero_lt_of_ne_zero
      intro g
      replace g : eqv'.symm i.succ = (0: Fin (n + 1)).val := g
      rw [Fin.val_inj, ←eqv'.inj.eq_iff, eqv'_zero] at g
      simp at g
      nomatch g
    replace ih := ih (b.swap 0 i).tail {
      toFun x := ⟨(eqv' x.succ).pred (by
        intro h
        rw [←eqv'_zero, eqv'.inj.eq_iff] at h
        nomatch h), by
        have := x.pos
        simp
        apply Nat.lt_of_le_of_ne
        omega
        intro
        omega⟩
      invFun x := ⟨(eqv'.symm x.succ).pred (by
        intro h
        rw [←eqv'.inj.eq_iff, eqv'_zero] at h
        simp at h
        nomatch h), by
        have := x.pos
        simp
        apply Nat.lt_of_le_of_ne
        omega
        intro
        omega⟩
      rightInv x := by
        ext; simp
        conv in _ - _ + 1 => {
          rw [Nat.sub_add_cancel (by
              apply Nat.succ_le_of_lt
              have := eqv'_symm_pos x
              omega)]
        }
        simp
      leftInv x := by
        ext; simp
        conv in _ - _ + 1 => {
          rw [Nat.sub_add_cancel (by
              apply Nat.succ_le_of_lt
              have := eqv'_pos x
              omega)]
        }
        simp
    } ?_
    replace ih := ih.cons (x := a)
    have : (b.swap 0 i).head = a := by
      have := h 0
      simp at this
      rw [this]; clear this
      show _ = b[i]
      unfold head
      rw [b.swap_comm]
      simp [swap]
      rw [getElem_set]
      rw [if_pos rfl]
    rw (occs := [2]) [←this] at ih
    simp at ih
    apply ih.trans
    clear ih this
    apply Perm.symm
    apply perm_swap
    intro x
    simp
    unfold tail
    simp
    have := h x.succ
    simp at this
    conv in _ - 1 + 1 => {
      rw [Nat.sub_add_cancel (by
        apply Nat.succ_le_of_lt
        apply eqv'_pos)]
    }
    simp
    unfold eqv'
    simp
    assumption

def map (a: Vector α n) (f: α -> β) : Vector β n where
  toFun i := f a[i]

def reindex (a: Vector α n) (f: Fin m -> Fin n) : Vector α m where
  toFun i := a[f i]

@[simp]
def getElem_map (a: Vector α n) (f: α -> β) (i: Fin n) : (a.map f)[i] = f a[i] := rfl

@[simp]
def getElem_reindex (a: Vector α n) (f: Fin m -> Fin n) (i: Fin m) : (a.reindex f)[i] = a[f i] := rfl

@[simp]
def map_cons (a: α) (as: Vector α n) (f: α -> β) : (a::ᵥas).map f = f a::ᵥas.map f := by
  ext i; cases i using Fin.cases
  rfl
  rfl


end Function.Vector
