import Math.Data.Quotient.Basic
import Math.Type.Notation
import Math.Data.Set.Basic
import Math.Relation.Defs
import Math.Tactics.PPWithUniv

namespace ZfSet

@[pp_with_univ]
inductive Pre where
| intro (α: Type*) (mem: α -> Pre)

def Equiv : Pre -> Pre -> Prop
| .intro _ αmem, .intro _ βmem =>
  (∀a, ∃b, Equiv (αmem a) (βmem b)) ∧
  (∀b, ∃a, Equiv (αmem a) (βmem b))

scoped infix:50 " zf≈ " => Equiv

def Pre.«Type» : Pre -> Type _
| .intro a _ => a

def Pre.Mem : ∀(s: Pre), s.Type -> Pre
| .intro _ mem => mem

def Equiv.mk : ∀a b: Pre,
  (∀a₀, ∃b₀, Equiv (a.Mem a₀) (b.Mem b₀)) ->
  (∀b₀, ∃a₀, Equiv (a.Mem a₀) (b.Mem b₀)) ->
  a zf≈ b
| .intro _ _, .intro _ _ => And.intro

@[refl]
def Equiv.refl' : ∀(a: Pre), a zf≈ a
| .intro _ _ => ⟨(fun x => ⟨x, Equiv.refl' _⟩), (fun x => ⟨x, Equiv.refl' _⟩)⟩

@[symm]
def Equiv.symm' : ∀{a b}, a zf≈ b -> b zf≈ a
| .intro a amem, .intro b bmem, ⟨ha, hb⟩ => by
  apply And.intro
  intro b₀
  have ⟨a₀, prf⟩ := hb b₀
  exists a₀
  exact Equiv.symm' prf
  intro a₀
  have ⟨b₀, prf⟩ := ha a₀
  exists b₀
  exact Equiv.symm' prf

def Equiv.trans : ∀{a b c}, a zf≈ b -> b zf≈ c -> a zf≈ c
| .intro a amem, .intro b bmem, .intro c cmem, ⟨hab, hba⟩, ⟨hbc, hcb⟩ => by
  apply And.intro
  intro a₀
  have ⟨b₀, hab⟩ := hab a₀
  have ⟨c₀, hbc⟩ := hbc b₀
  exists c₀
  exact Equiv.trans hab hbc
  intro c₀
  have ⟨b₀, hcb⟩ := hcb c₀
  have ⟨a₀, hba⟩ := hba b₀
  exists a₀
  exact Equiv.trans hba hcb

instance setoid : Setoid Pre where
  r := Equiv
  iseqv := ⟨Equiv.refl', Equiv.symm', Equiv.trans⟩

def Equiv.to_left : ∀{a b}, a zf≈ b -> ∀a₀: a.Type, ∃b₀: b.Type, (a.Mem a₀) zf≈ (b.Mem b₀)
| .intro _ _, .intro _ _, ⟨l, _⟩ => l
def Equiv.to_right : ∀{a b}, a zf≈ b -> ∀b₀: b.Type, ∃a₀: a.Type, (a.Mem a₀) zf≈ (b.Mem b₀)
| .intro _ _, .intro _ _, ⟨_, r⟩ => r

@[pp_with_univ]
def _root_.ZfSet := Quotient setoid
def mk : Pre -> ZfSet := Quot.mk Equiv

scoped notation "⟦" a "⟧" => mk a

@[cases_eliminator]
def ind : {motive: ZfSet -> Prop} -> (mk: ∀x, motive ⟦x⟧) -> ∀x, motive x := Quotient.ind
@[cases_eliminator]
def ind₂ : {motive: ZfSet -> ZfSet -> Prop} -> (mk: ∀x y, motive ⟦x⟧ ⟦y⟧) -> ∀x y, motive x y := Quotient.ind₂
@[cases_eliminator]
def ind₃ : {motive: ZfSet -> ZfSet -> ZfSet -> Prop} -> (mk: ∀x y z, motive ⟦x⟧ ⟦y⟧ ⟦z⟧) -> ∀x y z, motive x y z := by
  intro motive h x y z
  induction x, y using ind₂ with | mk x y =>
  induction z using ind with | mk z =>
  apply h
@[cases_eliminator]
def ind₄ : {motive: ZfSet -> ZfSet -> ZfSet -> ZfSet -> Prop} -> (mk: ∀w x y z, motive ⟦w⟧ ⟦x⟧ ⟦y⟧ ⟦z⟧) -> ∀w x y z, motive w x y z := by
  intro motive h w x y z
  induction w, x using ind₂ with | mk w x =>
  induction y, z using ind₂ with | mk y z =>
  apply h

@[refl]
def Equiv.refl : ∀(a: Pre), a ≈ a := Equiv.refl'
@[symm]
def Equiv.symm : ∀{a b}, a zf≈ b -> b ≈ a := Equiv.symm'

def Pre.mem (a b: Pre): Prop :=
  ∃a₀: a.Type, b zf≈ a.Mem a₀

def Pre.mem.spec :  ∀(a₀ b₀ a₁ b₁: Pre), a₀ zf≈ a₁ -> b₀ zf≈ b₁ -> a₀.mem b₀ -> a₁.mem b₁ := by
  intro a₀ b₀ a₁ b₁ aeq beq ⟨a₂, b₀_eqv_a⟩
  have := aeq.to_left
  have ⟨a₂', prf⟩ := aeq.to_left a₂
  exists a₂'
  apply Equiv.trans _ prf
  apply Equiv.trans beq.symm'
  assumption

-- constrain membership to be in a single universe for better universe inference
instance : Membership Pre.{u} Pre.{u} where
  mem := Pre.mem

def eqv : ZfSet.{u} -> ZfSet.{v} -> Prop := by
  apply Quotient.lift₂ (· zf≈ ·)
  intro a b c d ac bd
  apply propext; apply Iff.intro
  intro h
  exact ac.symm.trans <| h.trans bd
  intro h
  exact ac.trans <| h.trans bd.symm

scoped infix:50 " zf= " => eqv

def mem : ZfSet.{u} -> ZfSet.{v} -> Prop := by
  apply Quotient.lift₂ Pre.mem
  intro a b c d ac bd
  apply propext; apply Iff.intro
  apply Pre.mem.spec; assumption; assumption
  apply Pre.mem.spec; symm; assumption; symm; assumption

def sub.{u, v, w} (a: ZfSet.{u}) (b: ZfSet.{v}) : Prop :=
  ∀x: ZfSet.{w}, a.mem x -> b.mem x

def eqv.trans {a b c: ZfSet} : a zf= b -> b zf= c -> a zf= c := by
  cases a, b, c with | mk a b c =>
  apply Equiv.trans

@[symm]
def eqv.symm {a b: ZfSet} : a zf= b -> b zf= a := by
  cases a, b with | mk a b =>
  apply Equiv.symm'

@[refl]
def eqv.refl {a: ZfSet} : a zf= a := by
  cases a with | mk a =>
  apply Equiv.refl

def mem.congr {a b c d: ZfSet} : a zf= c -> b zf= d -> a.mem b -> c.mem d := by
  cases a, b, c, d with | mk  =>
  apply Pre.mem.spec

def sub.congr {a b c d: ZfSet} : a zf= c -> b zf= d -> sub.{_, _, u} a b -> sub.{_, _, u} c d := by
  intro ac bd h z hz
  exact (h _ (hz.congr ac.symm .refl)).congr bd .refl

instance : Membership ZfSet.{u} ZfSet.{u} where
  mem := mem

def mem.spec : mem a b ↔ ∃a' ∈ a, a' zf= b := by
  cases a, b with | mk a b =>
  apply Iff.intro
  intro ⟨a₀, eqv⟩
  exists ⟦a.Mem a₀⟧
  apply And.intro
  exact ⟨_, .refl' _⟩
  symm; assumption
  intro ⟨a', mem, eqv⟩
  cases a' with | mk a' =>
  obtain ⟨a₀, eqv'⟩ := mem
  exists a₀
  have: b zf≈ a' := eqv.symm
  apply this.trans
  assumption

instance : HasSubset Pre where
  Subset a b := ∀x ∈ a, x ∈ b

instance : HasSubset ZfSet where
  Subset a b := ∀x ∈ a, x ∈ b

def mem.ofMem {a b: ZfSet} : a ∈ b -> b.mem a := id

def sub.ofSubset {a b: ZfSet} : a ⊆ b -> sub.{_, _, u} a b := by
  intro h z ha
  rw [mem.spec] at *
  have ⟨z', z'_in_a, z'_eqv_z⟩ := ha
  have := h _ z'_in_a
  exists z'

def eq_of_eqv {a b: ZfSet} : a zf= b -> a = b := by
  intro eqv
  cases a, b with | mk a b =>
  apply Quotient.sound
  assumption

@[simp]
def mk_mem (a b: Pre) : (⟦a⟧ ∈ ⟦b⟧) = (a ∈ b) := rfl

@[simp]
def mk_sub (a b: Pre) : ⟦a⟧ ⊆ ⟦b⟧ ↔ a ⊆ b := by
  apply Iff.intro
  intro h x
  simp only [←mk_mem]
  apply h
  intro h x
  induction x using ind with | mk x =>
  simp
  apply h

def Pre.mem_def {a: Pre} : ∀{x: a.Type}, a.Mem x ∈ a := by
  intro x
  cases a with | intro a amem =>
  exists x

def Pre.ext (a b: Pre) : (∀x, x ∈ a ↔ x ∈ b) -> a ≈ b := by
  intro h
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  apply And.intro
  intro x
  have ⟨y, prf⟩  := (h (amem x)).mp Pre.mem_def
  exists y
  intro x
  have ⟨y, prf⟩  := (h (bmem x)).mpr Pre.mem_def
  exists y
  symm; assumption

@[ext]
def ext (a b: ZfSet) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := by
  intro h
  induction a using ind with | mk a =>
  induction b using ind with | mk b =>
  apply Quotient.sound
  apply Pre.ext
  exact fun x => h ⟦x⟧

@[refl]
def sub_refl (a: ZfSet) : a ⊆ a := fun _ => id
def sub_trans {a b c: ZfSet} : a ⊆ b -> b ⊆ c -> a ⊆ c := fun ab bc x h => bc x (ab x h)
def sub_antisym {a b: ZfSet} : a ⊆ b -> b ⊆ a -> a = b := by
  intro ab ba
  ext x
  apply Iff.intro
  apply ab
  apply ba

@[coe]
def toSet (s: ZfSet) : Set ZfSet := Set.mk (· ∈ s)

def toSet_mem (s: ZfSet) : ∀{x}, x ∈ s ↔ x ∈ s.toSet := Iff.rfl

def toSet_inj : Function.Injective toSet := by
  intro x y eq
  ext z
  simp [toSet_mem, eq]

def Pre.equivAcc {a b: Pre} (h: a zf≈ b) : Acc (· ∈ ·) ⟦a⟧ -> Acc (· ∈ ·) ⟦b⟧ := by
  induction a generalizing b with
  | intro α αmem ih =>
    cases b with | intro β βmem =>
    intro acc
    apply Acc.intro
    intro b mem
    cases b with | mk b =>
    obtain ⟨b₀, b₀eqv⟩: ∃b₀, b zf≈ βmem b₀ := mem
    have ⟨a₀, a₀eqv⟩ := h.right b₀
    apply ih
    apply flip Equiv.trans
    symm; exact b₀eqv
    assumption
    apply acc.inv
    exists a₀

instance : @Relation.IsWellFounded ZfSet (· ∈ ·) where
  wf := by
    apply WellFounded.intro
    intro a
    cases a with | mk a =>
    induction a with
    | intro α αmem ih =>
    apply Acc.intro
    intro b
    cases b with | mk b =>
    intro mem
    obtain ⟨a, eqv⟩: ∃a, b zf≈ αmem a := mem
    apply Pre.equivAcc eqv.symm
    apply ih

def Pre.lift.{u, v} : Pre.{u} -> Pre.{max u v}
| .intro a amem => .intro (ULift a) (fun x => (amem x.down).lift)

def Pre.lift.spec.{u, v} (a: Pre.{u}) : a zf≈ Pre.lift.{u, v} a := by
  induction a with | intro a amem ih =>
  apply And.intro
  intro a₀
  exists ⟨a₀⟩
  apply ih
  intro a₀
  exists a₀.down
  apply ih

def lift.{u, v} : ZfSet.{u} -> ZfSet.{max u v} := by
  apply Quotient.lift (⟦.lift ·⟧)
  intro a b eqv
  apply Quotient.sound
  apply (Pre.lift.spec a).symm'.trans
  apply Equiv.trans _ (Pre.lift.spec b)
  assumption

def mem_lift (s: ZfSet.{u}) : ∀{x: ZfSet.{max u v}}, x ∈ s.lift ↔ s.mem x := by
  intro x
  cases x, s with | mk x s =>
  cases s with | intro S Smem =>
  have s₀_eqv_lift := Pre.lift.spec.{u, v} (Pre.intro S Smem)
  apply Iff.intro
  intro ⟨s₀, eqv⟩
  have ⟨s, _⟩ := s₀_eqv_lift.to_right s₀
  exists s
  apply eqv.trans
  symm; assumption
  intro ⟨s₀, eqv⟩
  have ⟨s, _⟩ := s₀_eqv_lift.to_left s₀
  exists s
  apply eqv.trans
  assumption

def sub_lift.{u, v} (s: ZfSet.{u}) : ∀{x: ZfSet.{max u v}}, x ⊆ s.lift ↔ sub.{_, _, max u v} x s := by
  intro x
  apply Iff.intro
  intro h y
  rw [mem.spec]
  intro ⟨x', x'_in_x, x'_eqv_y⟩
  have := h x' x'_in_x
  rw [mem_lift] at this
  apply this.congr
  rfl; assumption
  intro h y hy
  rw [mem_lift]
  replace z := h  y hy
  assumption

instance : EmptyCollection Pre where
  emptyCollection := .intro PEmpty PEmpty.elim

instance : EmptyCollection ZfSet where
  emptyCollection := ⟦∅⟧

instance : Nonempty ZfSet := ⟨∅⟩

protected def Nonempty (a: ZfSet) : Prop := ∃x, x ∈ a

@[simp]
def not_mem_empty : ∀x, x ∉ (∅: ZfSet) := by
  intro x
  induction x using ind with | mk x =>
  intro ⟨_, _⟩
  contradiction

def empty_sub (a: ZfSet) : ∅ ⊆ a := by
  intro _ h
  have := not_mem_empty _ h
  contradiction

def of_sub_empty (a: ZfSet) : a ⊆ ∅ -> a = ∅ := by
  intro h
  ext x
  apply Iff.intro
  apply h
  intro h
  have := not_mem_empty _ h
  contradiction

def sub_empty_iff (a: ZfSet) : a ⊆ ∅ ↔ a = ∅ := by
  apply Iff.intro
  apply of_sub_empty
  intro h
  subst h
  rfl

def Pre.union : Pre.{u} -> Pre.{u} -> Pre.{u}
| .intro a amem, .intro b bmem => .intro (a ⊕ b) (fun
  | .inl x => amem x
  | .inr x => bmem x)

instance : Union Pre := ⟨Pre.union⟩

def Pre.union.spec (a b c d: Pre) : a zf≈ c -> b zf≈ d -> a ∪ b zf≈ c ∪ d := by
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  cases c with | intro c cmem =>
  cases d with | intro d dmem =>
  intro ac bd
  apply And.intro
  intro x
  cases x <;> rename_i x
  have ⟨y, prf⟩ := ac.left x
  exists .inl y
  have ⟨y, prf⟩ := bd.left x
  exists .inr y
  intro x
  cases x <;> rename_i x
  have ⟨y, prf⟩ := ac.right x
  exists .inl y
  have ⟨y, prf⟩ := bd.right x
  exists .inr y

def union : ZfSet -> ZfSet -> ZfSet := by
  apply Quotient.lift₂ (⟦· ∪ ·⟧)
  intros
  apply Quotient.sound
  apply Pre.union.spec <;> assumption

instance : Union ZfSet := ⟨.union⟩

@[simp]
def mk_union {a b: Pre} : ⟦a⟧ ∪ ⟦b⟧ = ⟦a ∪ b⟧ := rfl

def mem_union {a b: ZfSet} : ∀{x}, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := by
  intro x
  induction a, b, x using ind₃ with | mk a b x =>
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  simp
  apply Iff.intro
  intro ⟨x₀, prf⟩
  cases x₀ <;> rename_i x₀
  left; exists x₀
  right; exists x₀
  intro h
  cases h <;> rename_i h
  obtain ⟨x, prf⟩ := h
  exists .inl x
  obtain ⟨x, prf⟩ := h
  exists .inr x

def toSet_union (a b: ZfSet) : (a ∪ b).toSet = a.toSet ∪ b.toSet := by
  ext x
  simp [mem_union, Set.mem_union, toSet]

def union_comm (a b: ZfSet) : a ∪ b = b ∪ a := by
  ext x; simp [mem_union, or_comm]

def union_assoc (a b c: ZfSet) : a ∪ b ∪ c = a ∪ (b ∪ c) := by
  ext x; simp [mem_union, or_assoc]

def sub_union_left (a b: ZfSet) : a ⊆ a ∪ b := by
  intro x
  simp [mem_union]
  exact .inl

def sub_union_right (a b: ZfSet) : b ⊆ a ∪ b := by
  intro x
  simp [mem_union]
  exact .inr

instance : @Std.Commutative ZfSet (· ∪ ·) := ⟨union_comm⟩
instance : @Std.Associative ZfSet (· ∪ ·) := ⟨union_assoc⟩

def union_empty (a: ZfSet) : a ∪ ∅ = a := by
  ext x
  apply Iff.intro
  intro h
  cases mem_union.mp h
  assumption
  have := not_mem_empty x
  contradiction
  intro h
  apply mem_union.mpr
  left; assumption

def empty_union (a: ZfSet) : ∅ ∪ a = a := by
  rw [union_comm]
  apply union_empty

def Pre.sep (P: Pre → Prop) : Pre -> Pre
| .intro a amem => .intro { x: a // P (amem x) } (fun x => amem x.val)

def Pre.sep.spec (P: Pre → Prop) (a b: Pre) :
  a zf≈ b -> (∀x y, x zf≈ y -> P x -> P y) ->
  a.sep P zf≈ b.sep P := by
  intro ab resp
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  apply And.intro
  · intro ⟨a₀, pa₀⟩
    have ⟨b₀, prf⟩ := ab.left a₀
    refine ⟨⟨b₀, ?_⟩, ?_⟩
    apply resp
    all_goals assumption
  · intro ⟨b₀, pb₀⟩
    have ⟨a₀, prf⟩ := ab.right b₀
    refine ⟨⟨a₀, ?_⟩, ?_⟩
    apply resp
    symm
    all_goals assumption

def sep (P: ZfSet -> Prop) : ZfSet -> ZfSet := by
  apply Quotient.lift (⟦Pre.sep (fun x => P ⟦x⟧) ·⟧)
  intro a b eq
  apply Quotient.sound
  apply Pre.sep.spec
  assumption
  intro _ _ eq
  unfold ZfSet.mk
  rw [Quot.sound eq]
  exact id

@[simp]
def mk_sep {P: ZfSet -> Prop} {a: Pre} : ⟦a⟧.sep P = ⟦a.sep (fun x => P ⟦x⟧)⟧ := rfl

def mem_sep {P: ZfSet -> Prop} {a: ZfSet} : ∀{x}, x ∈ a.sep P ↔ x ∈ a ∧ P x := by
  intro x
  induction a, x using ind₂ with | mk a x =>
  cases a with | intro a amem =>
  simp
  apply Iff.intro
  intro ⟨y, prf⟩
  have : Quot.mk Equiv x = Quot.mk Equiv (amem y.val) := Quot.sound prf
  apply And.intro
  exists y.val
  unfold ZfSet.mk
  unfold Pre.sep Pre.Mem at prf
  simp at prf
  rw [this]
  exact y.property
  intro ⟨⟨y, prf⟩, prop⟩
  have : Quot.mk Equiv x = Quot.mk Equiv (amem y) := Quot.sound prf
  unfold ZfSet.mk at prop
  rw [this] at prop
  exists ⟨y, prop⟩

def inter (a b: ZfSet) := a.sep (· ∈ b)

instance : Inter ZfSet := ⟨inter⟩

def mem_inter {a b: ZfSet} : ∀{x}, x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := mem_sep

def toSet_inter (a b: ZfSet) : (a ∩ b).toSet = a.toSet ∩ b.toSet := by
  ext x
  simp [mem_inter, Set.mem_inter, toSet]

def inter_comm (a b: ZfSet) : a ∩ b = b ∩ a := by
  ext x
  simp [mem_inter, and_comm]

def inter_assoc (a b c: ZfSet) : a ∩ b ∩ c = a ∩ (b ∩ c) := by
  ext x
  simp [mem_inter, and_assoc]

def empty_inter (a: ZfSet) : ∅ ∩ a = ∅ := by
  ext; simp [mem_inter]

def inter_empty (a: ZfSet) : a ∩ ∅ = ∅ := by
  ext; simp [mem_inter]

def inter_sub_left (a b: ZfSet) : a ∩ b ⊆ a := by
  intro x
  simp [mem_inter]
  intros; assumption

def inter_sub_right (a b: ZfSet) : a ∩ b ⊆ b := by
  intro x
  simp [mem_inter]

def left_sub_union (a b: ZfSet) : a ⊆ a ∪ b := by
  intro x
  rw [mem_union]; exact .inl

def right_sub_union (a b: ZfSet) : b ⊆ a ∪ b := by
  intro x
  rw [mem_union]; exact .inr

def sdiff (a b: ZfSet) := a.sep (· ∉ b)

instance : SDiff ZfSet := ⟨sdiff⟩

def mem_sdiff {a b: ZfSet} : ∀{x}, x ∈ a \ b ↔ x ∈ a ∧ x ∉ b := by
  intro x
  show x ∈ sdiff a b ↔ _
  unfold sdiff
  exact mem_sep

def toSet_sdiff (a b: ZfSet) : (a \ b).toSet = a.toSet \ b.toSet := by
  ext x
  simp [mem_sdiff, Set.mem_sdiff, toSet]

def empty_sdiff (a: ZfSet) : ∅ \ a = ∅ := by
  ext; simp [mem_sdiff]

def sdiff_empty (a: ZfSet) : a \ ∅ = a := by
  ext; simp [mem_sdiff]

def sdiff_sub_left (a b: ZfSet) : a \ b ⊆ a := by
  intro x
  simp [mem_sdiff]
  intros; assumption

def Pre.singleton (a: Pre.{u}) : Pre.{u} := .intro PUnit (fun _ => a)
instance : Singleton Pre Pre := ⟨.singleton⟩
def singleton : ZfSet.{u} -> ZfSet.{u} := by
  apply Quotient.lift (⟦{·}⟧)
  intros a b  eq
  apply Quotient.sound
  apply And.intro
  intro; refine ⟨.unit, eq⟩
  intro; refine ⟨.unit, eq⟩
instance : Singleton ZfSet ZfSet := ⟨.singleton⟩

def mem_singleton {a: ZfSet} : ∀{x: ZfSet}, x ∈ ({a}: ZfSet) ↔ x = a := by
  intro x
  induction a, x using ind₂ with | mk a x =>
  apply Iff.intro
  intro ⟨h, prf⟩
  exact Quotient.sound prf
  intro h
  exact ⟨.unit, Quotient.exact h⟩

instance : Insert Pre.{u} Pre.{u} where
  insert a b := { a } ∪ b

instance : Insert ZfSet.{u} ZfSet.{u} where
  insert a b := { a } ∪ b

def mem_insert {a b: ZfSet} : ∀{x}, x ∈ insert a b ↔ x = a ∨ x ∈ b := by
  simp [insert, mem_union, mem_singleton]

def toSet_insert (a b: ZfSet) : (insert a b).toSet = insert a b.toSet := by
  ext x
  simp [mem_insert, toSet]

def mem_pair {a b: ZfSet} : ∀{x}, x ∈ ({a, b}: ZfSet) ↔ x = a ∨ x = b := by
  simp [mem_insert, mem_singleton]

def Pre.powerset : Pre -> Pre
| .intro a amem => .intro (Set a) fun s => .intro { x // x ∈ s } fun x => amem x

def Pre.mem_powerset {a: Pre} : ∀{x}, x ∈ a.powerset ↔ x ⊆ a := by
  intro x
  cases a with | intro a amem =>
  cases x with | intro x xmem =>
  apply Iff.intro
  intro mem
  obtain ⟨s, h⟩ := mem
  obtain s : Set a := s
  intro x₀ x₀mem
  obtain ⟨x₁, x₀_eq_x₁⟩ := x₀mem
  obtain x₁: x := x₁
  obtain ⟨a₀, prf⟩ := h.to_left x₁
  replace ⟨a₀, a₀_mem⟩ : { a // a ∈ _ } := a₀
  refine ⟨a₀, ?_⟩
  apply x₀_eq_x₁.trans
  apply prf.trans
  rfl
  intro sub
  replace sub := fun y => sub y
  refine ⟨?_, ?_⟩
  apply Set.mk
  intro a₀
  exact ∃x₀, xmem x₀ zf≈ amem a₀
  apply And.intro
  intro x₀
  simp only
  have ⟨a₀, pf⟩ := sub (xmem x₀) Pre.mem_def
  refine ⟨⟨a₀, ?_⟩, ?_⟩
  exists x₀
  assumption
  intro ⟨a₀, prf⟩
  obtain ⟨x₀, prf⟩  := prf
  exists x₀

def powerset : ZfSet -> ZfSet := by
  apply Quotient.lift (⟦·.powerset⟧)
  intro a b eq
  ext x; induction x using ind with | mk x =>
  simp [Pre.mem_powerset]
  have : ⟦a⟧ = ⟦b⟧ := Quotient.sound eq
  rw [←mk_sub, ←mk_sub, this]

@[simp]
def mk_powerset (a: Pre) : ⟦a⟧.powerset = ⟦a.powerset⟧ := rfl

def mem_powerset {a: ZfSet} : ∀{x}, x ∈ a.powerset ↔ x ⊆ a := by
  intro x
  induction a, x using ind₂ with | mk a x =>
  simp [Pre.mem_powerset]

def powerset_empty : powerset ∅ = {∅} := by
  ext x
  rw [mem_powerset, mem_singleton]
  exact sub_empty_iff x

def Pre.image (f: Pre.{u} -> Pre.{u}): Pre.{u} -> Pre.{u}
| .intro a amem => .intro a (fun x => f (amem x))

def cast_eqv: a ≈ b -> a zf≈ b := id

noncomputable
def image (f: ZfSet.{u} -> ZfSet.{u}): ZfSet.{u} -> ZfSet.{u} := by
  apply Quotient.lift (fun _ => ⟦_⟧) _
  intro p
  apply p.image
  intro h
  exact Quotient.out (f ⟦h⟧)
  simp
  intro a b eq
  cases a with | intro a amem =>
  cases b with | intro b bmem =>
  apply Quotient.sound
  apply And.intro
  · intro a₀
    have ⟨b₀, prf⟩ := eq.left a₀
    simp
    exists b₀
    apply Quotient.exact (s := setoid)
    unfold Quotient.mk
    show Quotient.mk _ (Quotient.out (f ⟦_⟧)) = Quotient.mk _ (Quotient.out (f ⟦_⟧))
    rw [Quotient.out_spec, Quotient.out_spec]
    congr 1
    exact Quotient.sound prf
  · intro b₀
    have ⟨a₀, prf⟩ := eq.right b₀
    simp
    exists a₀
    apply Quotient.exact (s := setoid)
    unfold Quotient.mk
    show Quotient.mk _ (Quotient.out (f ⟦_⟧)) = Quotient.mk _ (Quotient.out (f ⟦_⟧))
    rw [Quotient.out_spec, Quotient.out_spec]
    congr 1
    exact Quotient.sound prf

def mem_image {a: ZfSet} {f: ZfSet -> ZfSet} : ∀{x}, x ∈ a.image f ↔ ∃a₀ ∈ a, x = f a₀ := by
  intro x
  induction a, x using ind₂ with | mk a x =>
  cases a with | intro a amem =>
  apply Iff.intro
  intro ⟨a₀, prf⟩
  simp at a₀
  exists ⟦amem a₀⟧
  apply And.intro
  apply Pre.mem_def
  simp only [Pre.image, Pre.Mem] at prf
  replace prf : x ≈ Quotient.out _ := prf
  have := Quotient.sound prf
  rw [Quotient.out_spec] at this
  assumption
  intro ⟨a₀, a₀_in_a, x_eq⟩
  induction a₀ using ind with | mk a₀ =>
  obtain ⟨a₁, a₁prf⟩ := a₀_in_a
  refine ⟨a₁, ?_⟩
  simp [Pre.image, Pre.Mem]
  show x ≈ _
  apply Quotient.exact
  erw [Quotient.out_spec]
  apply x_eq.trans
  congr 1
  apply Quotient.sound
  assumption

def Pre.attach_image (p: Pre.{u}) (f: ∀x ∈ p, Pre.{u}): Pre.{u} :=
  .intro p.Type (fun x => f (p.Mem x) ⟨_, .refl' _⟩)

private def hcongrFun
  {β₀ β₁: α -> Prop}
  (f: ∀x, β₀ x -> γ) (g: ∀x, β₁ x -> γ):
  β₀ = β₁ -> HEq f g -> ∀x y h₀ h₁, x = y -> f x h₀ = g y h₁ := by
  intro eq heq
  cases eq; cases heq
  intro x y _ _ _; subst y
  rfl

noncomputable
def attach_image (s: ZfSet) (f: ∀x ∈ s, ZfSet.{u}): ZfSet.{u} := by
  revert f
  apply Quotient.hrecOn s (motive := fun s => _) _ _
  intro s f
  refine ⟦Pre.attach_image s ?_⟧
  intro x mem
  exact (f ⟦x⟧ mem).out
  intro A B eq
  apply Function.hfunext
  rw [Quotient.sound eq]
  intro ha hb heq
  apply heq_of_eq
  apply Quotient.sound
  unfold Pre.attach_image
  apply And.intro
  intro a
  have ⟨b, eqv⟩ := eq.to_left a
  exists b
  dsimp
  apply Quotient.exact (s := setoid)
  rw [Quotient.out_spec, Quotient.out_spec]
  apply hcongrFun (f := ha) (g := hb)
  rw [Quotient.sound eq]
  assumption
  exact Quotient.sound eqv
  intro b
  have ⟨a, eqv⟩ := eq.to_right b
  exists a
  dsimp
  apply Quotient.exact (s := setoid)
  rw [Quotient.out_spec, Quotient.out_spec]
  apply hcongrFun (f := ha) (g := hb)
  rw [Quotient.sound eq]
  assumption
  exact Quotient.sound eqv

def mem_attach_image {s: ZfSet} {f: ∀x ∈ s, ZfSet} : ∀{x}, x ∈ s.attach_image f ↔ ∃s', ∃h: s' ∈ s, x = f s' h := by
  intro x
  cases s, x with | mk S X =>
  apply Iff.intro
  intro ⟨s, X_eq⟩
  refine  ⟨⟦S.Mem s⟧, ?_, ?_⟩
  exact ⟨_, .refl' _⟩
  apply (Quotient.sound X_eq).trans
  unfold Pre.attach_image Pre.Mem; dsimp
  rw [Quotient.out_spec]
  intro ⟨s, s_in_S, eq⟩
  cases s with | mk S' =>
  obtain ⟨s, eqv⟩ := s_in_S
  refine ⟨?_, ?_⟩
  assumption
  apply Quotient.exact (s := setoid)
  apply eq.trans
  erw [Quotient.out_spec]
  congr 1
  exact Quotient.sound eqv

def attach_image_empty : attach_image ∅ f = ∅ := by
  ext x
  rw [mem_attach_image]
  apply Iff.intro
  intro ⟨_, h, _⟩
  exact (not_mem_empty _ h).elim
  intro h
  exact (not_mem_empty _ h).elim

def Pre.sUnion (a: Pre) : Pre :=
 .intro (Σx: a.Type, (a.Mem x).Type) fun ⟨x, x'⟩ => (a.Mem x).Mem x'

def Pre.sUnion.spec (a b: Pre) (h: a zf≈ b) : a.sUnion zf≈ b.sUnion := by
  cases a with | intro A Amem =>
  cases b with | intro B Bmem =>
  apply And.intro <;> dsimp
  intro ⟨a, a'⟩
  have ⟨b, eqv₀⟩ := h.to_left a
  have ⟨b', eqv₁⟩ := eqv₀.to_left a'
  exists ⟨b, b'⟩
  intro ⟨b, b'⟩
  have ⟨a, eqv₀⟩ := h.to_right b
  have ⟨a', eqv₁⟩ := eqv₀.to_right b'
  exists ⟨a, a'⟩

instance : SUnion Pre Pre where
  sUnion := Pre.sUnion

instance : SUnion ZfSet ZfSet where
  sUnion := by
    apply Quotient.lift (⟦·.sUnion⟧)
    intro a b eq
    apply Quotient.sound
    apply Pre.sUnion.spec
    assumption

instance : SInter ZfSet ZfSet where
  sInter a := (⋃a).sep fun x => ∀a' ∈ a, x ∈ a'

def mem_sUnion {a: ZfSet} : ∀{x}, x ∈ ⋃a ↔ ∃a' ∈ a, x ∈ a' := by
  intro x
  cases a, x with | mk A X =>
  apply Iff.intro
  intro ⟨⟨a, a'⟩, eqv⟩
  exists ⟦A.Mem a⟧
  apply And.intro
  exact ⟨_, .refl' _⟩
  exists a'
  intro ⟨a', ha', hx⟩
  cases a' with | mk A' =>
  obtain ⟨a, eqv⟩ := ha'
  obtain ⟨a', eqv'⟩ := hx
  have ⟨a₀, eqv₀⟩ := eqv.to_left a'
  exists ⟨a, a₀⟩
  exact eqv'.trans eqv₀

def mem_sInter {a: ZfSet} (h: a.Nonempty) : ∀{x}, x ∈ ⋂a ↔ ∀a' ∈ a, x ∈ a' := by
  intro x
  simp [SInter.sInter]
  rw [mem_sep, mem_sUnion]
  apply Iff.intro
  intro ⟨g₀, g₁⟩
  assumption
  intro g
  obtain ⟨x, mem⟩ := h
  apply And.intro
  refine ⟨_, mem, ?_⟩
  apply g; assumption
  assumption

def sUnion_empty : ⋃ (∅: ZfSet) = ∅ := by
  ext
  rw [mem_sUnion]
  apply Iff.intro
  intro ⟨_, h, _⟩
  exact (not_mem_empty _ h).elim
  intro h
  exact (not_mem_empty _ h).elim

def insert_nonempty {a b: ZfSet} : (insert a b).Nonempty :=
  ⟨_, mem_insert.mpr (.inl rfl)⟩

def Pre.range (f: ι -> Pre) : Pre :=
  .intro ι <| fun x => f x

noncomputable def range (f: ι -> ZfSet) : ZfSet :=
  ⟦Pre.range (fun x => (f x).out)⟧

def mem_range {f: ι -> ZfSet} : ∀{x}, x ∈ range f ↔ ∃i, x = f i := by
  intro x
  cases x with | mk x =>
  apply Iff.intro
  intro ⟨i, eqv⟩
  exists i
  apply (Quotient.sound eqv).trans
  simp [Pre.range, Pre.Mem]
  rw [Quotient.out_spec]
  intro ⟨i, eqv⟩
  exists i
  apply Quotient.exact (s := setoid)
  simp [Pre.range, Pre.Mem]
  rw [Quotient.out_spec]
  assumption

def Pre.succ (s: Pre) := insert s s
def succ (s: ZfSet) := insert s s

def mk_succ (s: Pre) : ⟦.succ s⟧ = ⟦s⟧.succ := rfl

def Pre.ofNat : Nat -> Pre
| 0 => ∅
| .succ n => (ofNat n).succ

def ofNat : Nat -> ZfSet
| 0 => ∅
| .succ n => (ofNat n).succ

def mk_ofNat (n: Nat) : ofNat n = ⟦.ofNat n⟧ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ofNat, Pre.ofNat, mk_succ, ih]

def Pre.omega : Pre := .intro (ULift Nat) (.ofNat ∘ ULift.down)
def omega : ZfSet := ⟦.omega⟧

def mem_ofNat : ∀{x}, x ∈ ofNat n ↔ ∃m < n, x = ofNat m := by
  intro x
  induction n with
  | zero =>
    apply Iff.intro
    intro mem
    have := not_mem_empty _ mem
    contradiction
    intro ⟨_, _, _⟩
    contradiction
  | succ n ih =>
    rw [ofNat, succ, mem_insert]
    apply Iff.intro
    intro h
    rcases h with h | h
    exists n
    apply And.intro
    apply Nat.lt_succ_self
    assumption
    have ⟨m, mLt, eq⟩ := ih.mp h
    refine ⟨m, ?_, eq⟩
    apply Nat.lt_trans mLt
    apply Nat.lt_succ_self
    intro ⟨m, mLt, eq⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ mLt) with h | h
    right; apply ih.mpr; exists m
    left; subst n; assumption

def ofNat_inj : ∀{n m: Nat}, ofNat n = ofNat m ↔ n = m := by
  intro n m
  apply flip Iff.intro
  intro h; rw [h]
  intro eq
  rcases Nat.lt_trichotomy n m with lt | eq | gt
  have := mem_ofNat.mpr ⟨n, lt, rfl⟩; rw [eq] at this
  have := Relation.irrefl (rel := (· ∈ ·)) this
  contradiction
  assumption
  have := mem_ofNat.mpr ⟨m, gt, rfl⟩; rw [eq] at this
  have := Relation.irrefl (rel := (· ∈ ·)) this
  contradiction

def ofNat_mem_ofNat : ∀{n m}, ofNat n ∈ ofNat m ↔ n < m := by
  intro n m
  rw [mem_ofNat]
  apply Iff.intro
  intro ⟨k, kLt, eq⟩
  cases ofNat_inj.mp eq
  assumption
  intro
  exists n

def mem_omega : ∀{x}, x ∈ omega ↔ ∃n, x = ofNat n := by
  intro x
  cases x with | mk x =>
  apply flip Iff.intro
  intro ⟨n, eqv⟩
  rw [eqv]; clear eqv
  rw [mk_ofNat]
  exists ⟨n⟩
  intro ⟨⟨n⟩, eqv⟩
  exists n
  rw [mk_ofNat]
  apply Quotient.sound
  exact eqv

def ofNat_mem_omega : ofNat n ∈ omega := by
  rw [mem_omega]
  exists n

end ZfSet
