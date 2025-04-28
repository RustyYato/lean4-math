import Math.Logic.Equiv.Basic
import Math.Relation.Defs

structure LazyList (α: Sort u) : Sort (max 1 u) where
  ofFun ::
  size: ℕ
  getElem : Fin size -> α

private def fin_val_eq_of_heq (a: Fin n) (b: Fin m) (g: n = m) (h: HEq a b) : a.val = b.val := by
  cases g
  cases h
  rfl

namespace LazyList

instance : GetElem (LazyList α) Nat α (fun l i => i < l.size) where
  getElem xs i h := xs.getElem ⟨i, h⟩

instance : GetElem (LazyList α) (Fin n) α (fun l i => i < l.size) where
  getElem xs i h := xs[i.val]

@[simp]
def mk_getElem_nat {n: ℕ} (i: Nat) (h: i < n) {f: Fin n -> α} : (LazyList.ofFun n f)[i] = f ⟨i, h⟩ := rfl

@[simp]
def mk_getElem_fin {n k: ℕ} (i: Fin k) (h: i < n) {f: Fin n -> α} : (LazyList.ofFun n f)[i] = f ⟨i, h⟩ := rfl

@[simp]
def getElem_eq (l: LazyList α) (i: Fin l.size) : l.getElem i = l[i] := rfl

@[ext]
def ext (as bs: LazyList α) (hsize: as.size = bs.size) (h: ∀(i: ℕ) (ha: i < as.size) (hb: i < bs.size), as.getElem ⟨i, ha⟩ = bs.getElem ⟨i, hb⟩) : as = bs := by
  obtain ⟨asize, afn⟩ := as
  obtain ⟨bsize, bfn⟩ := bs
  congr
  apply Function.hfunext
  congr
  intro a b j'
  have := fin_val_eq_of_heq _ _ (by assumption) j'
  simp
  have := h a.val
  simp at this
  rw [this]
  congr
  omega

end LazyList

namespace Equiv

def lazy_list_eqv_list {α: Type*} : LazyList α ≃ List α where
  toFun l := (List.finRange l.size).map l.getElem
  invFun l := {
    size := l.length
    getElem i := l[i]
  }
  leftInv x := by
    ext
    simp
    simp
  rightInv x := by
    simp
    apply List.ext_getElem?
    intro i; simp
    by_cases h:i < x.length
    rw [
      List.getElem?_eq_getElem,
      List.getElem_finRange]
    simp; simpa
    rw [List.getElem?_eq_none]
    simp; omega
    simp; omega

def congrLazyList {α β: Sort*} (h: α ≃ β) : LazyList α ≃ LazyList β where
  toFun l := {
    size := l.size
    getElem i := h (l.getElem i)
  }
  invFun l := {
    size := l.size
    getElem i := h.symm (l.getElem i)
  }
  leftInv x := by simp
  rightInv x := by simp

def liftList : (LazyList α ≃ LazyList β) ≃ (List α ≃ List β) :=
  (Equiv.congrEquiv Equiv.lazy_list_eqv_list Equiv.lazy_list_eqv_list)

def congrList (h: α ≃ β) : List α ≃ List β := Equiv.liftList (Equiv.congrLazyList h)

def lazy_list_eqv_list_plift {α: Sort*} : LazyList α ≃ List (PLift α) :=
  (congrLazyList (Equiv.plift _).symm).trans Equiv.lazy_list_eqv_list

end Equiv

namespace LazyList

variable {α β: Sort*}

def nil : LazyList α where
  size := 0
  getElem := Fin.elim0

@[simp]
def size_nil : (nil (α := α)).size = 0 := rfl

def cons (a: α) (as: LazyList α) : LazyList α where
  size := as.size + 1
  getElem i := i.cases a as.getElem

@[simp]
def size_cons (a: α) (as: LazyList α) : (cons a as).size = as.size + 1 := rfl

def getElem_cons' (a: α) (as: LazyList α) (i: Nat) (h: i < as.size + 1) : (cons a as).getElem ⟨i, h⟩ = if h:i = 0 then a else as.getElem ⟨i - 1, by omega⟩ := by
  split ; subst i; rfl
  match i with
  | i + 1 => rfl

@[simp]
def getElem_cons_zero' (a: α) (as: LazyList α) : (cons a as).getElem (0: Fin (as.size + 1)) = a := rfl

@[simp]
def getElem_cons_succ' (a: α) (as: LazyList α) (i: Fin as.size) : (cons a as).getElem i.succ = as.getElem i := rfl

def getElem_cons {α: Type*} (a: α) (as: LazyList α) (i: Nat) (h: i < as.size + 1) : (cons a as)[i] = if h:i = 0 then a else as[i - 1] := by
  apply getElem_cons'

@[simp]
def getElem_cons_zero {α: Type*} (a: α) (as: LazyList α) : (cons a as)[(0: Nat)] = a := rfl

@[simp]
def getElem_cons_succ {α: Type*} (a: α) (as: LazyList α) (i: Nat) (h: i < as.size) : (cons a as)[i + 1]'(by simp; omega) = as[i] := rfl

@[induction_eliminator]
def rec' {motive: LazyList α -> Sort*} (nil: motive .nil) (cons: ∀a as, motive as -> motive (.cons a as)) (list: LazyList α) : motive list :=
  list.size.rec (motive := fun size => ∀list: Fin size -> α, motive (LazyList.ofFun size list))
    (fun _ => cast (α := motive LazyList.nil) (by
      congr; ext i; rfl
      simp; contradiction) nil)
    (fun n ih => fun f =>
      have := ih (f ∘ Fin.succ)
      cast (α := motive (LazyList.cons (f 0) (LazyList.ofFun _ (f ∘ Fin.succ)))) (by
        simp [LazyList.cons]
        congr; ext i
        cases i using Fin.cases
        rfl; rfl) (cons _ _ (ih _)))
    list.getElem

@[cases_eliminator]
def cases {motive: LazyList α -> Sort*} (nil: motive .nil) (cons: ∀a as, motive (.cons a as)) (list: LazyList α) : motive list :=
  match list with
  | .ofFun 0 f => cast (α := motive LazyList.nil) (by
      congr; ext i; rfl
      simp; contradiction) nil
  | .ofFun (size + 1) f =>
    cast (α := motive (LazyList.cons (f 0) (LazyList.ofFun _ (f ∘ Fin.succ)))) (by
        simp [LazyList.cons]
        congr; ext i
        cases i using Fin.cases
        rfl; rfl) (cons _ _)

def append (as bs: LazyList α) : LazyList α where
  size := as.size + bs.size
  getElem i :=
    match Equiv.finSum.symm i with
    | .inl x => as.getElem x
    | .inr x => bs.getElem x

@[simp]
def size_append (as bs: LazyList α) : (append as bs).size = as.size + bs.size := rfl

def getElem_append' (as bs: LazyList α) (i: Nat) (h: i < as.size + bs.size) : (append as bs).getElem ⟨i, h⟩  = if h:i < as.size then as.getElem ⟨i, h⟩ else bs.getElem ⟨i - as.size, by omega⟩ := by
  unfold append
  simp; rw [Equiv.symm_apply_finSum]
  simp; symm
  split
  rfl
  rfl

def getElem_append {α: Type*} (as bs: LazyList α) (i: Nat) (h: i < as.size + bs.size) : (append as bs)[i] = if h:i < as.size then as[i] else bs[i - as.size] := by
  apply getElem_append'

def Nodup (as: LazyList α) := Function.Injective as.getElem

inductive Perm : LazyList α -> LazyList α -> Prop where
| nil : Perm .nil .nil
| cons : Perm as bs -> Perm (.cons a as) (.cons a bs)
| swap : Perm (.cons a (.cons b c)) (.cons b (.cons a c))
| trans : Perm a b -> Perm b c -> Perm a c

instance : Relation.IsEquiv (Perm (α := α)) where
  trans := Perm.trans
  refl a := by
    induction a with
    | nil => exact .nil
    | cons a as ih => exact ih.cons
  symm h := by
    induction h with
    | nil => exact .nil
    | cons _ ih => exact ih.cons
    | swap => exact .swap
    | trans _ _ iha ihb => exact ihb.trans iha

@[simp]
def llepl_length (as: LazyList α) : (Equiv.lazy_list_eqv_list_plift as).length = as.size := by
  show (List.map _ _).length = _
  simp; rfl

def llepl_getElem (as: LazyList α) (i: ℕ) (h: i < as.size) : (Equiv.lazy_list_eqv_list_plift as)[i]'(by simpa) = PLift.up (as.getElem ⟨i, h⟩) := by
  show (List.map _ _)[_]'_ = _
  simp
  rfl

@[simp]
def llepl_nil : Equiv.lazy_list_eqv_list_plift .nil = ([]: List (PLift α)) := rfl
@[simp]
def llepl_cons (a: α) (as: LazyList α) : Equiv.lazy_list_eqv_list_plift (.cons a as) = (PLift.up a::Equiv.lazy_list_eqv_list_plift as) := by
  apply List.ext_getElem
  simp; intro i h₀ h₁
  rw [llepl_getElem _ _ (by simpa using h₀)]
  cases i
  simp
  simp [cons]
  rw [llepl_getElem]

@[simp]
def llepl_symm_nil : Equiv.lazy_list_eqv_list_plift.symm ([]: List (PLift α)) = .nil := by
  symm; apply Equiv.eq_symm_of_coe_eq
  rfl
@[simp]
def llepl_symm_cons (a: PLift α) (as: List (PLift α)) : Equiv.lazy_list_eqv_list_plift.symm (a::as) = (.cons a.down (Equiv.lazy_list_eqv_list_plift.symm as)) := by
  symm; apply Equiv.eq_symm_of_coe_eq
  simp

@[simp]
def nil_append (as: LazyList α) : append .nil as = as := by
  ext i; simp
  simp [append]
  rw [Equiv.symm_apply_finSum]
  simp

@[simp]
def append_nil (as: LazyList α) : append as .nil = as := by
  ext i; simp
  simp [append]
  rw [Equiv.symm_apply_finSum]
  simp
  rw [dif_pos]
  assumption

@[simp]
def cons_append (a: α) (as bs: LazyList α) : append (cons a as) bs = cons a (append as bs) := by
  ext i ha hb; simp; omega
  simp [getElem_append', getElem_cons']
  simp at ha hb
  match i with
  | 0 => simp
  | i + 1 => simp

def append_assoc (as bs cs: LazyList α) : append (append as bs) cs = append as (append bs cs) := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih]

def map (as: LazyList α) (f: α -> β) : LazyList β where
  size := as.size
  getElem i := f (as.getElem i)

@[simp]
def size_map (as: LazyList α) (f: α -> β) : (as.map f).size = as.size := rfl
@[simp]
def getElem_map' (as: LazyList α) (f: α -> β) (i: ℕ) (h: i < as.size) : (as.map f).getElem ⟨i, by get_elem_tactic⟩ = f (as.getElem ⟨i, by get_elem_tactic⟩) := rfl
@[simp]
def getElem_map {α β: Type*} (as: LazyList α) (f: α -> β) (i: ℕ) (h: i < as.size) : (as.map f)[i] = f as[i] := rfl

@[simp]
def nil_map (f: α -> β) : map nil f = nil := by
  ext; simp
  contradiction

@[simp]
def cons_map (a: α) (as: LazyList α) (f: α -> β) : (cons a as).map f = cons (f a) (as.map f) := by
  ext i; simp
  simp
  cases i
  rfl
  rfl

def reindex (as: LazyList α) (f: Fin n -> Fin as.size) : LazyList α where
  size := n
  getElem i := as.getElem (f i)

def size_reindex (as: LazyList α) (f: Fin n -> Fin as.size) : (as.reindex f).size = n := rfl
@[simp]
def getElem_reindex' (as: LazyList α) (f: Fin n -> Fin as.size) (i: ℕ) (h: i < n) : (as.reindex f).getElem ⟨i, by get_elem_tactic⟩ = as.getElem (f ⟨i, by get_elem_tactic⟩) := rfl
@[simp]
def getElem_reindex {α: Type*} (as: LazyList α) (f: Fin n -> Fin as.size) (i: ℕ) (h: i < n) : (as.reindex f)[i] = as[f ⟨i, by get_elem_tactic⟩] := rfl

def sum {α: Type*} [Add α] [Zero α] (as: LazyList α) : α :=
  as.rec' (motive := fun _ => α) 0 (fun a _ ih => a + ih)

@[simp] def sum_nil {α: Type*} [Add α] [Zero α] : sum (α := α) nil = 0 := rfl
@[simp] def sum_cons {α: Type*} [Add α] [Zero α] (a: α) (as: LazyList α) : sum (cons a as) = a + sum as := rfl

def getChunk (as: LazyList (LazyList α)) (i: ℕ) (hi: i < (as.map LazyList.size).sum) :
  Σ'(a: LazyList α) (i: Fin as.size) (j: ℕ), as.getElem i = a ∧ j < a.size :=
  as.rec' (motive := fun as => ∀(i: ℕ), i < (as.map LazyList.size).sum -> Σ'(a: LazyList α) (i: Fin as.size) (j: ℕ), as.getElem i = a ∧ j < a.size) (fun _ h => by contradiction)
    (fun a as ih i hi =>
      if h:i < a.size then
        ⟨a, ⟨0, by simp⟩, i, by rw [getElem_cons']; simp, h⟩
      else
        have ⟨b, i', j, hi', hj⟩ := ih (i - a.size) (by
          simp at hi
          omega)
        ⟨b, i'.succ, j, by simpa [cons ], hj⟩) i hi

def getChunk_cons (a: LazyList α) (as: LazyList (LazyList α)) (i) (hi) :
  getChunk (cons a as) i hi =
  if h:i < a.size then
    ⟨a, ⟨0, by simp⟩, i, by rw [getElem_cons']; simp, h⟩
  else
    have ⟨b, i', j, hi', hj⟩ := getChunk as (i - a.size) (by
      simp at hi
      omega)
    ⟨b, i'.succ, j, by simpa [cons ], hj⟩ := rfl

def flatten (as: LazyList (LazyList α)) : LazyList α where
  size := (as.map LazyList.size).sum
  getElem i :=
    have ⟨a, _, _, _, hj⟩ := getChunk as i.val i.isLt
    a.getElem ⟨_, hj⟩

@[simp]
def flatten_size (as: LazyList (LazyList α)) : (flatten as).size = (as.map LazyList.size).sum := rfl

@[simp]
def flatten_nil : flatten nil = nil (α := α) := by
  ext; simp
  simp [flatten]
  contradiction

@[simp]
def flatten_cons (a: LazyList α) (as: LazyList (LazyList α)) : flatten (cons a as) = append a (flatten as) := by
  ext i ha hb; simp
  conv => { lhs; unfold flatten }
  simp
  rw [getChunk_cons, getElem_append']
  by_cases h:i < a.size
  rw [dif_pos h, dif_pos h]
  rw [dif_neg h, dif_neg h]
  unfold flatten; simp
  generalize as.getChunk (i - a.size) (by simp at ha; omega) = a'
  obtain ⟨_, _, _, _, _⟩ := a'
  rfl

def flatMap (as: LazyList α) (f: α -> LazyList β) : LazyList β := (as.map f).flatten

@[simp] def flatMap_nil (f: α -> LazyList β) : flatMap nil f = nil := by simp [flatMap]
@[simp] def flatMap_cons (a: α) (as: LazyList α) (f: α -> LazyList β) : flatMap (cons a as) f = append (f a) (flatMap as f) := by simp [flatMap]

def mem (a: α) (as: LazyList α) := ∃i, a = as.getElem i

@[simp]
def nodup_nil : Nodup (nil (α := α)) := by intro i; exact i.elim0

def nodup_cons_iff (a: α) (as: LazyList α) : ¬as.mem a ∧ as.Nodup ↔ (cons a as).Nodup := by
  apply Iff.intro
  · intro ⟨h₀, g⟩
    intro x y h
    cases x using Fin.cases
    cases y using Fin.cases
    rfl
    simp at h
    have := h₀ ⟨_, h⟩
    contradiction
    cases y using Fin.cases
    simp at h
    have := h₀ ⟨_, h.symm⟩
    contradiction
    congr
    simp at h
    exact g h
  · intro h
    apply And.intro
    rintro ⟨k, rfl⟩
    have := @h ⟨0, by simp⟩ k.succ (by simp)
    rw [←Fin.val_inj] at this
    simp at this
    intro x y g
    exact Fin.succ_inj.mp (@h x.succ y.succ g)

def nodup_cons_head {a: α} {as: LazyList α} : (cons a as).Nodup -> ¬as.mem a := by
  intro h
  rw [←nodup_cons_iff] at h
  exact h.left

def nodup_cons_tail {a: α} {as: LazyList α} : (cons a as).Nodup -> as.Nodup := by
  intro h
  rw [←nodup_cons_iff] at h
  exact h.right

def nodup_cons {a: α} {as: LazyList α} : ¬as.mem a -> as.Nodup -> (cons a as).Nodup := by
  intro h g
  rw [←nodup_cons_iff]
  trivial

def nodup_map (as: LazyList α) (f: α -> β) (hf: Function.Injective f) (ha: as.Nodup) : (as.map f).Nodup := by
  apply Function.Injective.comp (g := f)
  assumption
  assumption

@[simp]
def not_mem_nil {a: α} : ¬mem a nil := nofun
@[simp]
def mem_cons {a: α} {as: LazyList α} : ∀{x}, (cons a as).mem x ↔ x = a ∨ as.mem x := by
  intro x
  apply Iff.intro
  rintro ⟨i, rfl⟩
  cases i using Fin.cases
  left; rfl; right; simp; rename_i i; exists i
  intro h
  rcases h with rfl | h
  exists ⟨0, by simp⟩
  obtain ⟨i, rfl⟩ := h
  rw [←getElem_cons_succ']
  refine ⟨_, rfl⟩

@[simp]
def mem_map {as: LazyList α} {f: α -> β} : ∀{x}, (as.map f).mem x ↔ ∃a, as.mem a ∧ x = f a := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih]

@[simp]
def mem_append {as bs: LazyList α} : ∀{x}, (append as bs).mem x ↔ as.mem x ∨ bs.mem x := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih, or_assoc]

def nodup_append (as bs: LazyList α) (ha: as.Nodup) (hb: bs.Nodup) (nocomm: ∀x, as.mem x -> bs.mem x -> False) : (append as bs).Nodup := by
  induction as with
  | nil => simpa
  | cons a as ih =>
    simp
    apply nodup_cons
    · intro h
      simp at h
      cases h
      have := nodup_cons_head ha
      contradiction
      apply nocomm a
      simp; assumption
    apply ih
    apply nodup_cons_tail
    assumption
    · intro x ha hb
      apply nocomm x
      simp [ha]
      assumption

@[simp]
def mem_flatten {as: LazyList (LazyList α)} : ∀{x}, as.flatten.mem x ↔ ∃a, as.mem a ∧ a.mem x := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih]

def getElem_flatten_idx (as: LazyList (LazyList α)) := Σx: Fin as.size, Fin (as.getElem x).size

def getElem_flatten (as: LazyList (LazyList α)) (idx: as.getElem_flatten_idx) :=
  (as.getElem idx.fst).getElem idx.snd

def truncate (as: LazyList α) (n: ℕ) : LazyList α :=
  as.reindex (Fin.castLE (n := min as.size n) (Nat.min_le_left _ _))

@[simp]
def truncate_size (as: LazyList α) (n: ℕ) : (as.truncate n).size = min as.size n := rfl

@[simp]
def truncate_zero (as: LazyList α) : truncate as 0 = nil := by
  ext; simp
  contradiction

@[simp]
def truncate_nil (n: ℕ) : truncate nil n = nil (α := α) := by
  ext; simp
  contradiction

@[simp]
def truncate_cons_succ (a: α) (as: LazyList α) (n: ℕ) : truncate (cons a as) (n + 1) = cons a (truncate as n) := by
  ext i ha; simp
  simp [truncate]
  cases i
  simp
  erw [getElem_cons_succ' (i := ⟨_, _⟩)]
  intro; simp at ha
  omega

@[simp]
def truncate_map (as: LazyList α) (f: α -> β) (n: ℕ) : (truncate as n).map f = truncate (as.map f) n := by
  induction as generalizing n with
  | nil => simp
  | cons a as ih =>
    cases n
    simp
    simp [ih]

def drop (as: LazyList α) (n: ℕ) : LazyList α :=
  as.reindex (fun x: Fin (as.size - n) => ⟨x.val + n, by omega⟩)

@[simp]
def drop_size (as: LazyList α) (n: ℕ) : (as.drop n).size = as.size - n := rfl

@[simp]
def drop_nil : drop nil n = nil (α := α) := by
  ext; simp
  contradiction

@[simp]
def drop_zero (as: LazyList α) : drop as 0 = as := by
  ext; simp
  simp [drop]

@[simp]
def drop_cons_succ (a: α) (as: LazyList α) (n: ℕ) : drop (cons a as) (n + 1) = drop as n := by
  ext i ha; simp
  simp [drop]
  erw [getElem_cons_succ' (i := ⟨_, _⟩)]
  intro; simp at ha;
  show i + n < _; omega

def truncate_append_drop (as: LazyList α) (n: ℕ) : append (truncate as n) (drop as n) = as := by
  induction as generalizing n with
  | nil => simp
  | cons a as ih =>
    cases n
    simp
    simp [ih]

def nodup_flatten (as: LazyList (LazyList α))
  -- as has no duplicates
  (h₀: as.Nodup)
  -- as has no duplicates
  (h₁: ∀a, as.mem a -> a.Nodup)
  -- and if any two elements share any elements, they must be the same list
  (h₂: ∀a b: LazyList α, as.mem a -> as.mem b -> ∀x: α, a.mem x -> b.mem x -> a = b) : as.flatten.Nodup := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp
    apply nodup_append
    apply h₁; simp
    apply ih
    apply nodup_cons_tail h₀
    intro x hx
    apply h₁
    simp [hx]
    intro x y hx hy z hzx hzy
    apply h₂
    simp [hx]
    simp [hy]
    assumption
    assumption
    intro x y h
    simp at h
    obtain ⟨b, b_in_as, x_in_b⟩ := h
    cases h₂ a b (by simp) (by simp [b_in_as]) x (by assumption) (by assumption)
    have := nodup_cons_head h₀
    contradiction

def nodup_flatMap (as: LazyList α) (f: α -> LazyList β)
  (h₀: as.Nodup)
  (h₁: ∀a, as.mem a -> (f a).Nodup)
  (h₂: ∀a b: α, as.mem a -> as.mem b -> ∀x: β, (f a).mem x -> (f b).mem x -> f a = f b)
  (h₃: Function.Injective f) : (as.flatMap f).Nodup := by
  apply nodup_flatten
  apply nodup_map
  assumption
  assumption
  intro x;
  simp
  rintro y hy rfl
  apply h₁
  assumption
  simp
  rintro a b x hx rfl y hy rfl z
  apply h₂
  assumption
  assumption

def perm_iff_list_perm {as bs: LazyList α} : as.Perm bs ↔ (Equiv.lazy_list_eqv_list_plift as).Perm (Equiv.lazy_list_eqv_list_plift bs) := by
  apply Iff.intro
  intro h
  induction h with
  | nil => simp
  | cons => simpa
  | swap => simp; apply List.Perm.swap
  | trans _ _ iha ihb => apply iha.trans ihb
  conv => { rhs; rw [←Equiv.lazy_list_eqv_list_plift.coe_symm as, ←Equiv.lazy_list_eqv_list_plift.coe_symm bs] }
  generalize Equiv.lazy_list_eqv_list_plift as = A
  generalize Equiv.lazy_list_eqv_list_plift bs = B
  intro h
  induction h with
  | nil => simp; exact .nil
  | cons _ _ ih => simp; apply ih.cons
  | swap => simp; apply Perm.swap
  | trans _ _ iha ihb => apply iha.trans ihb

def perm_iff_list_perm' {as bs: List (PLift α)} : as.Perm bs ↔ (Equiv.lazy_list_eqv_list_plift.symm as).Perm (Equiv.lazy_list_eqv_list_plift.symm bs) := by
  rw [perm_iff_list_perm]
  simp

def Perm.cons_inv (a: α) (as bs: LazyList α) : (LazyList.cons a as).Perm (LazyList.cons a bs) -> as.Perm bs := by
  rw [perm_iff_list_perm, perm_iff_list_perm]
  simp

end LazyList
