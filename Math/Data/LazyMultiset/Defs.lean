import Math.Data.LazyList.Defs

def LazyMultiset (α: Sort*) := Quotient (Relation.setoid (LazyList.Perm (α := α)))

namespace LazyMultiset

variable {α: Sort*}

def ofList : LazyList α -> LazyMultiset α := Quotient.mk _
def nil : LazyMultiset α := ofList .nil
def cons (a: α) : LazyMultiset α -> LazyMultiset α := by
  refine Quotient.lift (ofList ∘ LazyList.cons a) ?_
  intro x y h
  apply Quotient.sound
  apply h.cons
def mem (a: α) : LazyMultiset α -> Prop := by
  refine Quotient.lift (LazyList.mem a) ?_
  intro a b h
  simp; apply h.mem_iff
def Nodup : LazyMultiset α -> Prop := by
  refine Quotient.lift LazyList.Nodup ?_
  intro a b h
  simp; apply h.nodup_iff

def ind
  {motive: LazyMultiset α -> Prop}
  (ofList: ∀l, motive (ofList l))
  (m: LazyMultiset α) : motive m := by
  induction m using Quotient.ind with | _ m =>
  apply ofList

@[induction_eliminator]
def induction
  {motive: LazyMultiset α -> Prop}
  (nil: motive .nil)
  (cons: ∀a as, motive as -> motive (.cons a as))
  (m: LazyMultiset α) : motive m := by
  induction m using Quotient.ind with | _ m =>
  induction m with
  | nil => apply nil
  | cons a as ih => apply cons a (Quotient.mk _ as) ih

@[simp] def not_mem_nil {a: α} : ¬mem a nil := LazyList.not_mem_nil (a := a)
@[simp] def mem_cons {a: α} {as: LazyMultiset α} : ∀{x}, (cons a as).mem x ↔ x = a ∨ as.mem x := by
  induction as using ind with | _ a =>
  apply LazyList.mem_cons

def append : LazyMultiset α -> LazyMultiset α -> LazyMultiset α := by
  refine Quotient.lift₂ (fun a b => ofList (a.append b)) ?_
  intro a b c d ac bd
  apply Quotient.sound
  apply LazyList.Perm.append
  assumption
  assumption

@[simp] def mem_append {as bs: LazyMultiset α} : ∀{x}, (append as bs).mem x ↔ as.mem x ∨ bs.mem x := by
  induction as using ind with | _ a =>
  induction bs using ind with | _ b =>
  apply LazyList.mem_append

def append_comm (as bs: LazyMultiset α) : append as bs = append bs as := by
  induction as using ind with | _ a =>
  induction bs using ind with | _ b =>
  apply Quotient.sound
  apply LazyList.perm_append_comm

def append_assoc (as bs cs: LazyMultiset α) : append (append as bs) cs = append as (append bs cs) := by
  induction as using ind with | _ a =>
  induction bs using ind with | _ b =>
  induction cs using ind with | _ c =>
  apply Quotient.sound
  rw [LazyList.append_assoc]

def map (f: α -> β) : LazyMultiset α -> LazyMultiset β := by
  refine Quotient.lift (ofList ∘ (LazyList.map · f)) ?_
  intro a b h
  simp; apply Quotient.sound
  apply LazyList.Perm.map
  assumption

@[simp] def mem_map {as: LazyMultiset α} {f: α -> β} : ∀{x}, (as.map f).mem x  ↔ ∃a, as.mem a ∧ x = f a := by
  induction as using ind
  apply LazyList.mem_map

private def preFlatten (l: LazyList (LazyMultiset α)) : LazyMultiset α :=
  l.rec' (motive := fun _ => LazyMultiset α) nil (fun a _ ih => append a ih)

@[simp] private def preFlatten_nil : preFlatten (α := α) .nil = nil := rfl
@[simp] private def preFlatten_cons : preFlatten (α := α) (.cons a as) = append a (preFlatten as) := rfl

unsafe def flatten_impl (m: LazyMultiset (LazyMultiset α)) : LazyMultiset α :=
  let m : LazyList (LazyList α) := cast lcProof m
  cast lcProof m.flatten

@[implemented_by flatten_impl]
def flatten : LazyMultiset (LazyMultiset α) -> LazyMultiset α := by
  refine Quotient.lift preFlatten ?_
  intro a b h
  induction h with
  | nil => simp
  | cons h ih => simp; congr
  | swap => simp [←append_assoc, append_comm]
  | trans _ _ iha ihb => rw [iha, ihb]

@[simp] def flatten_nil : flatten (α := α) nil = nil := rfl
@[simp] def flatten_cons (a: LazyMultiset α) (as: LazyMultiset (LazyMultiset α)) : flatten (cons a as) = append a (flatten as) := by
  induction as using ind
  rfl

@[simp] def mem_flatten {as: LazyMultiset (LazyMultiset α)} : ∀{x}, as.flatten.mem x ↔ ∃a, as.mem a ∧ a.mem x := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih]

def flatMap (f: α -> LazyMultiset β) (as: LazyMultiset α) : LazyMultiset β :=
  (as.map f).flatten

@[simp] def mem_flatMap {f: α -> LazyMultiset β} {as: LazyMultiset α} : ∀{x}, (as.flatMap f).mem x ↔ ∃a, as.mem a ∧ (f a).mem x := by
  simp [flatMap]
  intro x
  apply Iff.intro
  rintro ⟨_, ⟨x, _, rfl⟩, _⟩
  exists x
  intro ⟨x, hx, h⟩
  exists f x
  apply And.intro
  exists x
  assumption

end LazyMultiset
