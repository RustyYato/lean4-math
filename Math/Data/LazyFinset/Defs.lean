import Math.Data.Multiset.Basic

inductive LazyFinset.Rel (α: Type*) : Multiset α -> Multiset α -> Prop where
| dedup (a: α) (as: Multiset α) : Rel α (a::ₘa::ₘas) (a::ₘas)

scoped instance LazyFinset.instSetoid (α: Type*) : Setoid (Multiset α) := Relation.setoid (Relation.EquivGen (LazyFinset.Rel α))

def LazyFinset (α: Type*) := Quotient (LazyFinset.instSetoid α)

namespace LazyFinset

def ofMultiset : Multiset α -> LazyFinset α := Quotient.mk _

def sound {as bs: Multiset α} : LazyFinset.Rel α as bs -> ofMultiset as = ofMultiset bs := by
  intro h
  apply Quotient.sound
  apply Relation.EquivGen.single
  assumption

def lift (f: Multiset α -> β) (resp: ∀a as, f (a::ₘa::ₘas) = f (a::ₘas)) : LazyFinset α -> β := by
  refine Quotient.lift f ?_
  intro a b h
  induction h with
  | single h => cases h; apply resp
  | refl => rfl
  | symm _ ih => rw [ih]
  | trans _ _ ih₀ ih₁ => rw [ih₀, ih₁]

def mem (x: α) : LazyFinset α -> Prop := by
  refine lift ?_ ?_
  exact (x ∈ ·)
  intro a as
  simp

instance : Membership α (LazyFinset α) where
  mem s a := s.mem a

instance : EmptyCollection (LazyFinset α) := ⟨ofMultiset ∅⟩

def cons (x: α) : LazyFinset α -> LazyFinset α := by
  refine lift ?_ ?_
  intro s; exact ofMultiset (x::ₘs)
  intro a as
  rw [Multiset.cons_comm x, Multiset.cons_comm x]
  apply sound
  apply LazyFinset.Rel.dedup a (x::ₘas)

@[simp] def not_mem_nil : ∀x, x ∉ (∅: LazyFinset α) := fun _ => List.not_mem_nil
@[simp] def mem_cons {a: α} {as: LazyFinset α} : ∀{x}, x ∈ cons a as ↔ x = a ∨ x ∈ as := by
  induction as using Quotient.ind with | _ as =>
  apply Multiset.mem_cons

@[simp] def cons_ofMultiset (a: α) (as: Multiset α) : ofMultiset (a::ₘas) = cons a (ofMultiset as) := rfl
@[simp] def dedup_cons (a: α) (as: LazyFinset α) : cons a (cons a as) = cons a as := by
  induction as using Quotient.ind with | _ =>
  apply sound
  apply Rel.dedup

def cons_comm (a₀ a₁: α) (as: LazyFinset α) : cons a₀ (cons a₁ as) = cons a₁ (cons a₀ as) := by
  induction as using Quotient.ind with | _ as =>
  show ofMultiset _ = ofMultiset _
  rw [Multiset.cons_comm]

private def eq_of_cons_mem (a: α) (as: Multiset α) (h: a ∈ as) : ofMultiset (a::ₘas) = ofMultiset as := by
  rw [Multiset.mem_spec] at h
  obtain ⟨as, rfl⟩ := h
  apply sound
  apply Rel.dedup

@[induction_eliminator]
def induction {motive: LazyFinset α -> Prop} (nil: motive ∅) (cons: ∀(a: α) (as: LazyFinset α), a ∉ as -> motive as -> motive (cons a as)) : ∀s, motive s := by
  intro s
  induction s using Quotient.ind with | _ s =>
  show motive (ofMultiset _)
  induction s with
  | nil => apply nil
  | cons a as ih =>
    by_cases h:a ∈ as
    · rwa [eq_of_cons_mem _ _ h]
    · show motive (LazyFinset.cons a (ofMultiset as))
      apply cons
      assumption
      assumption

def mem_spec {a: α} {as: LazyFinset α} : a ∈ as ↔ ∃as', as = cons a as' ∧ a ∉ as' := by
  apply flip Iff.intro
  rintro ⟨as', rfl, h⟩
  simp; intro h
  induction as with
  | nil => contradiction
  | cons a₀ as not_mem ih =>
    simp at h
    rcases h with rfl | h
    exists as
    obtain ⟨as', rfl, _⟩ := ih h
    exists cons a₀ as'
    rw [cons_comm]
    apply And.intro rfl
    intro h; apply not_mem
    simp at *
    rcases h with rfl | h
    left; rfl
    right; contradiction

@[ext]
def ext (as bs: LazyFinset α) : (∀x, x ∈ as ↔ x ∈ bs) -> as = bs := by
  intro h
  induction as generalizing bs with
  | nil =>
    induction bs with
    | nil => rfl
    | cons b bs =>
      have := h b
      simp at this
  | cons a as a_notin_as ih =>
    have := h a; simp at this
    rw [mem_spec] at this
    obtain ⟨bs, rfl, a_notin_bs⟩ := this
    rw [ih]
    intro x
    replace h := h x
    simp at h
    apply Iff.intro
    · intro g
      rcases h.mp (.inr g) with rfl | h'
      contradiction
      assumption
    · intro g
      rcases h.mpr (.inr g) with rfl | h'
      contradiction
      assumption

def append : LazyFinset α -> LazyFinset α -> LazyFinset α := by
  refine Quotient.lift₂ ?_ ?_
  intro a b ; exact ofMultiset (a ++ b)
  intro a b c d ac bd
  induction ac generalizing b d with
  | single ac =>
    cases ac; rename_i a as
    simp
    congr 1
    rw [Multiset.append_comm as, Multiset.append_comm as]
    induction bd with
    | single bd => cases bd; simp
    | refl => rfl
    | symm _ ih => rw [ih]
    | trans _ _ ih₀ ih₁ => rw [ih₀, ih₁]
  | @refl as =>
    simp; rw [Multiset.append_comm as, Multiset.append_comm as]
    induction bd with
    | single bd => cases bd; rename_i b bs; simp
    | refl => rfl
    | symm _ ih => rw [ih]
    | trans _ _ ih₀ ih₁ => rw [ih₀, ih₁]
  | symm a ih =>
    dsimp; symm; apply ih
    apply Relation.symm
    assumption
  | trans _ _ ih₀ ih₁ =>
    dsimp at *
    rw [ih₀ b d, ih₁]
    rfl; assumption

instance : Append (LazyFinset α) where
  append := append

@[simp] def append_ofMultiset (as bs: Multiset α) : ofMultiset (as ++ bs) = ofMultiset as ++ ofMultiset bs := rfl

def append_comm (as bs: LazyFinset α) : as ++ bs = bs ++ as := by
  induction as using Quotient.ind with | _ as =>
  induction bs using Quotient.ind with | _ bs =>
  show ofMultiset _ = ofMultiset _
  rw [Multiset.append_comm]
@[simp] def mem_append {as bs: LazyFinset α} : ∀{x}, x ∈ as ++ bs ↔ x ∈ as ∨ x ∈ bs := by
  induction as using Quotient.ind with | _ as =>
  induction bs using Quotient.ind with | _ bs =>
  apply Multiset.mem_append

end LazyFinset
