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

def ind {motive: LazyFinset α -> Prop} (ofMultiset : ∀as, motive (ofMultiset as)) (s: LazyFinset α) : motive s := by
  induction s using Quotient.ind with | _ as =>
  apply ofMultiset

@[simp] def lift_ofMultiset (f: Multiset α -> β) (resp) : lift f resp (ofMultiset as) = f as := rfl

def mem (x: α) : LazyFinset α -> Prop := by
  refine lift ?_ ?_
  exact (x ∈ ·)
  intro a as
  simp

instance : Membership α (LazyFinset α) where
  mem s a := s.mem a

instance : HasSubset (LazyFinset α) where
  Subset a b := ∀x, x ∈ a -> x ∈ b

instance : EmptyCollection (LazyFinset α) := ⟨ofMultiset ∅⟩
instance : Inhabited (LazyFinset α) := ⟨∅⟩
instance : Singleton α (LazyFinset α) where
  singleton a := ofMultiset {a}

@[simp] def mem_singleton {a: α} : ∀{x}, x ∈ ({a}: LazyFinset α) ↔ x = a := by
  apply Multiset.mem_singleton

def cons (x: α) : LazyFinset α -> LazyFinset α := by
  refine lift ?_ ?_
  intro s; exact ofMultiset (x::ₘs)
  intro a as
  rw [Multiset.cons_comm x, Multiset.cons_comm x]
  apply sound
  apply LazyFinset.Rel.dedup a (x::ₘas)

@[simp] def not_mem_nil : ∀x, x ∉ (∅: LazyFinset α) := fun _ => List.not_mem_nil
@[simp] def mem_cons {a: α} {as: LazyFinset α} : ∀{x}, x ∈ cons a as ↔ x = a ∨ x ∈ as := by
  induction as using ind with | _ as =>
  apply Multiset.mem_cons

@[simp] def cons_ofMultiset (a: α) (as: Multiset α) : ofMultiset (a::ₘas) = cons a (ofMultiset as) := rfl
@[simp] def dedup_cons (a: α) (as: LazyFinset α) : cons a (cons a as) = cons a as := by
  induction as using ind with | _ =>
  apply sound
  apply Rel.dedup

def cons_comm (a₀ a₁: α) (as: LazyFinset α) : cons a₀ (cons a₁ as) = cons a₁ (cons a₀ as) := by
  induction as using ind with | _ as =>
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
  induction s using ind with | _ s =>
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

def append_assoc (as bs cs: LazyFinset α) : as ++ bs ++ cs = as ++ (bs ++ cs) := by
  induction as using ind with | _ as =>
  induction bs using ind with | _ bs =>
  induction cs using ind with | _ cs =>
  show ofMultiset _ = ofMultiset _
  rw [Multiset.append_assoc]
def append_comm (as bs: LazyFinset α) : as ++ bs = bs ++ as := by
  induction as using ind with | _ as =>
  induction bs using ind with | _ bs =>
  show ofMultiset _ = ofMultiset _
  rw [Multiset.append_comm]
@[simp] def mem_append {as bs: LazyFinset α} : ∀{x}, x ∈ as ++ bs ↔ x ∈ as ∨ x ∈ bs := by
  induction as using ind with | _ as =>
  induction bs using ind with | _ bs =>
  apply Multiset.mem_append

@[simp] def nil_append (as: LazyFinset α) : ∅ ++ as = as := by
  induction as using ind with | _ as =>
  show ofMultiset _ = ofMultiset _
  rw [Multiset.nil_append]

@[simp] def cons_append (a: α) (as bs: LazyFinset α) : (cons a as) ++ bs = cons a (as ++ bs) := by
  induction as using ind with | _ as =>
  induction bs using ind with | _ bs =>
  show ofMultiset _ = ofMultiset _
  rw [Multiset.cons_append]

@[simp] def append_self (as: LazyFinset α) : as ++ as = as := by
  induction as with
  | nil => simp
  | cons a as _ ih =>
    rw [cons_append, append_comm, cons_append, ih]
    simp

def map (f: α -> β) : LazyFinset α -> LazyFinset β := by
  refine lift (ofMultiset ∘ Multiset.map f) ?_
  intro a as
  simp

@[simp] def nil_map (f: α -> β) : map f ∅ = ∅ := rfl
@[simp] def cons_map (f: α -> β) (a: α) (as: LazyFinset α) : map f (cons a as) = cons (f a) (map f as) := by
  induction as using ind with | _ as =>
  show ofMultiset _ = ofMultiset _
  simp

def mem_map {f: α -> β} {s: LazyFinset α} : ∀{x}, x ∈ s.map f ↔ ∃a ∈ s, f a = x := by
  induction s using ind with | _ s =>
  apply Multiset.mem_map

def flatten : LazyFinset (LazyFinset α) -> LazyFinset α := by
  refine lift ?_ ?_
  · intro h
    refine h.fold (· ++ ·) ∅ ?_
    intro a₀ a₁ as
    dsimp
    rw [←append_assoc, ←append_assoc, append_comm a₀]
  · intro a as
    simp;
    rw [←append_assoc]
    congr; simp

@[simp] def nil_flatten : flatten (α := α) ∅ = ∅ := rfl
@[simp] def cons_flatten (a: LazyFinset α) (as: LazyFinset (LazyFinset α)) : flatten (cons a as) = a ++ (flatten as) := by
  induction as using ind with | _ as =>
  induction a using ind with | _ a =>
  simp [flatten]; simp [cons, -cons_ofMultiset]

def mem_flatten {as: LazyFinset (LazyFinset α)} : ∀{x}, x ∈ as.flatten ↔ ∃a ∈ as, x ∈ a := by
  induction as with
  | nil => simp
  | cons a as h ih => simp [ih]

def flatMap (f: α -> LazyFinset β) (s: LazyFinset α) : LazyFinset β := (s.map f).flatten

@[simp] def nil_flatMap (f: α -> LazyFinset β) : flatMap f ∅ = ∅ := rfl
@[simp] def cons_flatMap (f: α -> LazyFinset β) (a: α) (as: LazyFinset α) : flatMap f (cons a as) = f a ++ (flatMap f as) := by simp [flatMap]

def mem_flatMap {f: α -> LazyFinset β} {as: LazyFinset α} : ∀{x}, x ∈ as.flatMap f ↔ ∃a ∈ as, x ∈ f a := by
  induction as with
  | nil => simp
  | cons a as h ih => simp [ih]

def toMultiset [DecidableEq α] : LazyFinset α -> Multiset α := by
  refine lift ?_ ?_
  · intro a
    exact a.dedup
  · intro a as
    ext x n
    apply Iff.intro
    · intro h
      have ha := (a::ₘa::ₘas).nodup_dedup
      rw [Multiset.mincount_le_one_iff_nodup] at ha
      have := ha _ _ h
      match n with
      | 0 => apply Multiset.MinCount.zero
      | 1 =>
        rw [Multiset.MinCount.iff_mem] at *
        simp [←Multiset.mem_dedup] at *
        assumption
    · intro h
      have ha := (a::ₘas).nodup_dedup
      rw [Multiset.mincount_le_one_iff_nodup] at ha
      have := ha _ _ h
      match n with
      | 0 => apply Multiset.MinCount.zero
      | 1 =>
        rw [Multiset.MinCount.iff_mem] at *
        simp [←Multiset.mem_dedup] at *
        assumption

def toMultiset_nodup [DecidableEq α] (s: LazyFinset α) : s.toMultiset.Nodup := by
  induction s using ind with | _ s =>
  apply Multiset.nodup_dedup

def toMultiset_ofMultiset [DecidableEq α] (as: Multiset α) : (ofMultiset as).toMultiset = as.dedup := rfl

@[simp] def ofMultiset_toMultiset [DecidableEq α] (as: LazyFinset α) : ofMultiset as.toMultiset = as := by
  induction as using ind with | _ s =>
  show ofMultiset s.dedup = ofMultiset s
  ext x;
  show x ∈ s.dedup ↔ x ∈ s
  rw [←Multiset.mem_dedup]

@[simp] def mem_toMultiset [DecidableEq α] {as: LazyFinset α} : ∀{x}, x ∈ as.toMultiset ↔ x ∈ as := by
  induction as using ind with | _ as =>
  intro
  apply (Multiset.mem_dedup _ _).symm

@[simp] def mem_ofMultiset {as: Multiset α} : ∀{x}, x ∈ (ofMultiset as) ↔ x ∈ as := by rfl

def filter (f: α -> Bool) : LazyFinset α -> LazyFinset α := by
  refine lift ?_ ?_
  intro s; exact ofMultiset (s.filter f)
  intro a₀ as
  ext; simp [Multiset.mem_filter]

@[simp] def mem_filter {f: α -> Bool} {as: LazyFinset α} : ∀{x}, x ∈ as.filter f ↔ x ∈ as ∧ f x := by
  induction as using ind with | _ as =>
  apply Multiset.mem_filter

def erase [DecidableEq α] (a: α) : LazyFinset α -> LazyFinset α :=
  filter (· ≠ a)

@[simp] def mem_erase [DecidableEq α] {a: α} {as: LazyFinset α} : ∀{x}, x ∈ as.erase a ↔ x ∈ as ∧ x ≠ a := by
  induction as using ind with | _ as =>
  simp [erase]

def Elem (s: LazyFinset α) := { x // x ∈ s }

instance {α: Type*} : CoeSort (LazyFinset α) (Type _) := ⟨Elem⟩

instance {P: α -> Prop} [DecidablePred P] (s: LazyFinset α) : Decidable (∃x ∈ s, P x) :=
  s.recOnSubsingleton fun s =>
  inferInstanceAs (Decidable (∃x ∈ s, P x))

instance {P: α -> Prop} [DecidablePred P] (s: LazyFinset α) : Decidable (∀x ∈ s, P x) :=
  s.recOnSubsingleton fun s =>
  inferInstanceAs (Decidable (∀x ∈ s, P x))

instance [DecidableEq α] (x: α) (as: LazyFinset α) : Decidable (x ∈ as) :=
  as.recOnSubsingleton fun as =>
  inferInstanceAs (Decidable (x ∈ as))

instance [DecidableEq α] : SDiff (LazyFinset α) where
  sdiff a b := a.filter (· ∉ b)

@[simp] def mem_sdiff [DecidableEq α] {a b: LazyFinset α} : ∀{x}, x ∈ a \ b ↔ x ∈ a ∧ x ∉ b := by
  simp [SDiff.sdiff]

instance [DecidableEq α] : Inter (LazyFinset α) where
  inter a b := a.filter (· ∈ b)

@[simp] def mem_inter [DecidableEq α] {a b: LazyFinset α} : ∀{x}, x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := by
  simp [Inter.inter]

instance : Union (LazyFinset α) where
  union a b := a ++ b

@[simp] def union_eq_append (a b: LazyFinset α) : a ∪ b = a ++ b := rfl

def append_disjoint_toMultiset {_: DecidableEq α} (a b: LazyFinset α) (h: ∀x ∈ a, x ∉ b) : (a ++ b).toMultiset = a.toMultiset ++ b.toMultiset := by
  ext x n
  match n with
  | 0 => simp [Multiset.MinCount.zero]
  | 1 => simp [Multiset.MinCount.iff_mem]
  | n + 2 =>
    apply Iff.intro
    intro h
    have := Multiset.mincount_le_one_iff_nodup.mp (toMultiset_nodup _) _ _ h
    contradiction
    intro h
    have := Multiset.mincount_le_one_iff_nodup.mp ?_ _ _ h
    contradiction
    apply Multiset.nodup_append
    apply toMultiset_nodup
    apply toMultiset_nodup
    clear h
    simpa

def exists_append_eq_of_sub {a b: LazyFinset α} (h: a ⊆ b) : ∃s, b = a ++ s ∧ ∀x ∈ a, x ∉ s := by
  classical
  exists b \ a
  apply And.intro
  ext; simp
  apply Iff.intro
  intro h;
  apply Classical.or_iff_not_imp_left.mpr
  intro
  apply And.intro <;> assumption
  intro g
  rcases g with g | g
  apply h; assumption
  exact g.left
  intro x ha
  simp; intro; assumption

def sub_append_left (a b: LazyFinset α) : a ⊆ a ++ b := by
  intro x; simp; exact Or.inl
def sub_append_right (a b: LazyFinset α) : b ⊆ a ++ b := by
  intro x; simp; exact Or.inr

@[simp] def singleton_toMultiset [DecidableEq α] (a: α) : toMultiset {a} = {a} := rfl

def nil_toMultiset [DecidableEq α] : toMultiset (α := α) ∅ = ∅ := rfl

def cons_toMultiset [DecidableEq α] (a: α) (as: LazyFinset α) (h: a ∉ as) : (cons a as).toMultiset = a::ₘas.toMultiset := by
  ext x n
  match n with
  | 0 => simp [Multiset.MinCount.zero]
  | 1 => simp [Multiset.MinCount.iff_mem]
  | n + 2 =>
    apply Iff.intro
    · intro h
      have := Multiset.mincount_le_one_iff_nodup.mp (toMultiset_nodup _) _ _ h
      contradiction
    · intro h
      have := Multiset.mincount_le_one_iff_nodup.mp ?_ _ _ h
      contradiction
      apply Multiset.nodup_cons
      simpa
      apply toMultiset_nodup

end LazyFinset
