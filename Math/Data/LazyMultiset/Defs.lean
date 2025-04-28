import Math.Data.LazyList.Defs

def LazyMultiset (α: Type*) := Quotient (Relation.setoid (LazyList.Perm (α := α)))

namespace LazyMultiset

variable {α: Type*}

def ofList : LazyList α -> LazyMultiset α := Quotient.mk _
def nil : LazyMultiset α := ofList .nil
def cons (a: α) : LazyMultiset α -> LazyMultiset α := by
  refine Quotient.lift (ofList ∘ LazyList.cons a) ?_
  intro x y h
  apply Quotient.sound
  apply h.cons
def mem (a: α) : LazyMultiset α -> Prop := by
  refine Quotient.lift (a ∈ ·) ?_
  intro a b h
  simp; apply h.mem_iff
def Nodup : LazyMultiset α -> Prop := by
  refine Quotient.lift LazyList.Nodup ?_
  intro a b h
  simp; apply h.nodup_iff
def size : LazyMultiset α -> ℕ := by
  refine Quotient.lift LazyList.size ?_
  intro a b h
  apply h.size_eq

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

@[cases_eliminator]
def cases
  {motive: LazyMultiset α -> Prop}
  (nil: motive .nil)
  (cons: ∀a as, motive (.cons a as))
  (m: LazyMultiset α) : motive m := by
  induction m using Quotient.ind with | _ m =>
  cases m with
  | nil => apply nil
  | cons a as => apply cons a (Quotient.mk _ as)

@[simp] def not_mem_nil {a: α} : ¬mem a nil := LazyList.not_mem_nil (a := a)
@[simp] def mem_cons {a: α} {as: LazyMultiset α} : ∀{x}, (cons a as).mem x ↔ x = a ∨ as.mem x := by
  induction as using ind with | _ a =>
  apply LazyList.mem_cons

@[simp] def size_nil : size (nil (α := α)) = 0 := rfl
@[simp] def size_cons (a: α) (as: LazyMultiset α) : size (cons a as) = size as + 1 := by
  induction as using ind
  rfl

instance : Append (LazyMultiset α) where
  append : LazyMultiset α -> LazyMultiset α -> LazyMultiset α := by
    refine Quotient.lift₂ (fun a b => ofList (a ++ b)) ?_
    intro a b c d ac bd
    apply Quotient.sound
    apply LazyList.Perm.append
    assumption
    assumption

@[simp] def mem_append {as bs: LazyMultiset α} : ∀{x}, (as ++ bs).mem x ↔ as.mem x ∨ bs.mem x := by
  induction as using ind with | _ a =>
  induction bs using ind with | _ b =>
  apply LazyList.mem_append

@[simp] def size_append (as bs: LazyMultiset α) : size (as ++ bs) = size as + size bs := by
  induction as using ind
  induction bs using ind
  rfl

def append_comm (as bs: LazyMultiset α) : as ++ bs = bs ++ as := by
  induction as using ind with | _ a =>
  induction bs using ind with | _ b =>
  apply Quotient.sound
  apply LazyList.perm_append_comm

def append_assoc (as bs cs: LazyMultiset α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
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

@[simp] def size_map (f: α -> β) (as: LazyMultiset α) : size (map f as) = size as := by
  induction as using ind
  rfl

private def preFlatten (l: LazyList (LazyMultiset α)) : LazyMultiset α :=
  l.rec' (motive := fun _ => LazyMultiset α) nil (fun a _ ih => a ++ ih)

@[simp] private def preFlatten_nil : preFlatten (α := α) .nil = nil := rfl
@[simp] private def preFlatten_cons : preFlatten (α := α) (.cons a as) = a ++ (preFlatten as) := rfl

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
@[simp] def flatten_cons (a: LazyMultiset α) (as: LazyMultiset (LazyMultiset α)) : flatten (cons a as) = a ++ (flatten as) := by
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

@[simp]
def nodup_nil : (nil (α := α)).Nodup := LazyList.nodup_nil

def nodup_cons_iff (a: α) (as: LazyMultiset α) : ¬as.mem a ∧ as.Nodup ↔ (cons a as).Nodup := by
  induction as using ind
  apply LazyList.nodup_cons_iff

def nodup_cons_head {a: α} {as: LazyMultiset α} : (cons a as).Nodup -> ¬as.mem a := by
  intro h
  rw [←nodup_cons_iff] at h
  exact h.left

def nodup_cons_tail {a: α} {as: LazyMultiset α} : (cons a as).Nodup -> as.Nodup := by
  intro h
  rw [←nodup_cons_iff] at h
  exact h.right

def nodup_cons {a: α} {as: LazyMultiset α} : ¬as.mem a -> as.Nodup -> (cons a as).Nodup := by
  intro h g
  rw [←nodup_cons_iff]
  trivial

def nodup_map {f: α -> β} (hf: f.Injective) (as: LazyMultiset α) (h: as.Nodup) : (as.map f).Nodup := by
  induction as using ind
  apply LazyList.nodup_map
  assumption
  assumption

def nodup_append (as bs: LazyMultiset α) (ha: as.Nodup) (hb: bs.Nodup) (h: ∀x, as.mem x -> bs.mem x -> False) : (as ++ bs).Nodup := by
  induction as using ind; induction bs using ind
  apply LazyList.nodup_append
  assumption
  assumption
  assumption

def nodup_flatten (as: LazyMultiset (LazyMultiset α))  (h₀: as.Nodup)
  (h₁: ∀a, as.mem a -> a.Nodup)
  (h₂: ∀a b, as.mem a -> as.mem b -> ∀x, a.mem x -> b.mem x -> a = b) : as.flatten.Nodup := by
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

def nodup_flatMap {f: α -> LazyMultiset β} (hf: f.Injective) (as: LazyMultiset α) (h₀: as.Nodup)
  (h₁: ∀a, as.mem a -> (f a).Nodup)
  (h₂: ∀a b, as.mem a -> as.mem b -> ∀x, (f a).mem x -> (f b).mem x -> f a = f b) : (as.flatMap f).Nodup := by
  apply nodup_flatten
  apply nodup_map
  assumption
  assumption
  · intro a; simp; rintro _ h rfl; apply h₁
    assumption
  · simp
    rintro _ _ _ _ rfl _ _ rfl
    apply h₂
    assumption
    assumption

def cons_comm (a b: α) (as: LazyMultiset α) : cons a (cons b as) = cons b (cons a as) := by
  induction as using ind
  apply Quotient.sound
  apply LazyList.Perm.swap

@[simp]
def nil_ne_cons (a: α) (as: LazyMultiset α) : ¬nil = cons a as := by
  intro h
  have := size_cons a as
  rw [←h] at this
  simp at this

def mem_iff_eq_cons {x: α} {as: LazyMultiset α} : as.mem x ↔ ∃as', as = cons x as' := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp
    apply Iff.intro
    intro h
    rcases h with rfl | h
    exists as
    obtain ⟨as', rfl⟩ := ih.mp h
    exists (cons a as')
    rw [cons_comm]
    intro ⟨as', hx⟩
    apply Classical.or_iff_not_imp_right.mpr
    intro h
    have : (cons x as').mem x := by simp
    rw [←hx] at this
    simp at this
    apply this.resolve_right
    assumption

end LazyMultiset
