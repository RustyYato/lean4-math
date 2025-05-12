import Math.Data.Quotient.Basic
import Math.Data.Trunc
import Math.Type.Notation
import Math.Data.Set.Basic
import Math.Relation.Defs
import Math.Tactics.PPWithUniv
import Math.Order.Defs

namespace ZfSet

@[pp_with_univ]
inductive Pre where
| intro (α: Type*) (mem: α -> Pre)

def Pre.«Type» : Pre -> Type _
| .intro a _ => a

def Pre.Mem : ∀(s: Pre), s.Type -> Pre
| .intro _ mem => mem

@[simp] def Pre.intro_type (α: Type*) (memα: α -> Pre) : (Pre.intro α memα).Type = α := rfl
@[simp] def Pre.intro_mem (α: Type*) (memα: α -> Pre) : (Pre.intro α memα).Mem = memα := rfl

inductive EquivState where
| intro (a b: Pre)
| exists_left (a b: Pre) (a₀: a.Type)
| exists_right (a b: Pre) (b₀: b.Type)

inductive Equiv' : EquivState -> Prop where
| intro (a b: Pre) :
  (∀a₀, Equiv' (.exists_left a b a₀)) ->
  (∀b₀, Equiv' (.exists_right a b b₀)) ->
  Equiv' (.intro a b)
| equiv_left (a b: Pre) (a₀: a.Type) (b₀: b.Type) :
  Equiv' (.intro (a.Mem a₀) (b.Mem b₀)) ->
  Equiv' (.exists_left a b a₀)
| equiv_right (a b: Pre) (a₀: a.Type) (b₀: b.Type) :
  Equiv' (.intro (a.Mem a₀) (b.Mem b₀)) ->
  Equiv' (.exists_right a b b₀)

def Equiv (a b: Pre) : Prop := Equiv' (.intro a b)

scoped infix:50 " zf≈ " => Equiv

def Equiv.left (h: a zf≈ b) : ∀a₀, ∃b₀, a.Mem a₀ zf≈ b.Mem b₀ := by
  intro a₀
  cases h with | intro _ _ l r =>
  cases l a₀ with | equiv_left _ _ _ b₀ =>
  exists b₀

def Equiv.right (h: a zf≈ b) : ∀b₀, ∃a₀, a.Mem a₀ zf≈ b.Mem b₀ := by
  intro a₀
  cases h with | intro _ _ l r =>
  cases r a₀ with | equiv_right _ _ a₀ =>
  exists a₀

def Equiv.intro (a b: Pre) :
  (∀a₀, ∃b₀, a.Mem a₀ zf≈ b.Mem b₀) ->
  (∀b₀, ∃a₀, a.Mem a₀ zf≈ b.Mem b₀) ->
  Equiv a b := by
  intro ha hb
  apply Equiv'.intro
  intro a₀
  have ⟨b₀, ha⟩ := ha a₀
  apply Equiv'.equiv_left
  assumption
  intro b₀
  have ⟨a₀, ha⟩ := hb b₀
  apply Equiv'.equiv_right
  assumption

@[induction_eliminator]
def Equiv.rec {motive : ∀a b: Pre, a zf≈ b -> Prop}
  (intro:  ∀a b: Pre,
    (∀a₀, ∃b₀, ∃h: a.Mem a₀ zf≈ b.Mem b₀, motive _ _ h) ->
    (∀b₀, ∃a₀, ∃h: a.Mem a₀ zf≈ b.Mem b₀, motive _ _ h) ->
    (h: a zf≈ b) ->
    motive a b h) {a b: Pre} (h: a zf≈ b) : motive a b h := by
    induction a generalizing b with
    | intro α memα ih =>
    cases b with
    | intro β memβ =>
    apply intro
    · intro a₀
      have ⟨b₀, h⟩ := h.left a₀
      exists b₀
      exists h
      apply ih
    · intro b₀
      have ⟨a₀, h⟩ := h.right b₀
      exists a₀
      exists h
      apply ih

@[cases_eliminator]
def Equiv.cases {motive : ∀a b: Pre, a zf≈ b -> Prop}
  (intro:  ∀a b: Pre,
    (∀a₀, ∃b₀, a.Mem a₀ zf≈ b.Mem b₀) ->
    (∀b₀, ∃a₀, a.Mem a₀ zf≈ b.Mem b₀) ->
    (h: a zf≈ b) ->
    motive a b h) {a b: Pre} (h: a zf≈ b) : motive a b h := by
    induction a generalizing b with
    | intro α memα ih =>
    cases b with
    | intro β memβ =>
    apply intro
    · intro a₀
      have ⟨b₀, h⟩ := h.left a₀
      exists b₀
    · intro b₀
      have ⟨a₀, h⟩ := h.right b₀
      exists a₀

@[refl]
def Equiv.refl (a: Pre) : a zf≈ a := by
  induction a with
  | intro α memα ih =>
  apply Equiv.intro
  simp
  iterate 2
    intro a₀
    exists a₀
    apply ih

@[symm]
def Equiv.symm {a b: Pre} (h: a zf≈ b) : b zf≈ a := by
  induction h with
  | intro a b ha hb h =>
  apply Equiv.intro
  intro b₀
  have ⟨a₀, hb, ih⟩ := hb b₀
  exists a₀
  intro a₀
  have ⟨b₀, ha, ih⟩ := ha a₀
  exists b₀

def Equiv.trans {a b c: Pre} (h: a zf≈ b) (g: b zf≈ c) : a zf≈ c := by
  induction h generalizing c with
  | intro a b hab hba h =>
  cases g with | intro _ _ hbc hcb =>
  apply Equiv.intro
  · intro a₀
    have ⟨b₀, _, h⟩ := hab a₀
    have ⟨c₀, g⟩ := hbc b₀
    exists c₀
    apply h
    assumption
  · intro c₀
    have ⟨b₀, g⟩ := hcb c₀
    have ⟨a₀, _, h⟩ := hba b₀
    exists a₀
    apply h
    assumption

instance Pre.setoid : Setoid Pre where
  r := Equiv
  iseqv := {
    refl := Equiv.refl
    symm := Equiv.symm
    trans := Equiv.trans
  }

@[pp_with_univ]
def _root_.ZfSet := Quotient Pre.setoid

def mk : Pre -> ZfSet := Quotient.mk _

scoped notation "⟦" x "⟧" => mk x

@[cases_eliminator]
def ind {motive: ZfSet -> Prop} (mk: ∀x, motive (mk x)) (s: ZfSet) : motive s := Quotient.ind mk s
def sound {a b: Pre} : a zf≈ b -> mk a = mk b := Quotient.sound (s := Pre.setoid)
def exact {a b: Pre} : mk a = mk b -> a zf≈ b := Quotient.exact

def lift (f: Pre -> α) (hf: ∀a b, a zf≈ b -> f a = f b) (s: ZfSet) : α := Quotient.lift f hf s
def lift₂ (f: Pre -> Pre -> α) (hf: ∀a b c d, a zf≈ c -> b zf≈ d -> f a b = f c d) (s₀ s₁: ZfSet) : α := Quotient.lift₂ f hf s₀ s₁
def attach (s: ZfSet) : Trunc { a // s = mk a } := Quotient.attach s

noncomputable def out : ZfSet ↪ Pre := Quotient.out
def out_spec (s: ZfSet) : mk s.out = s := Quotient.out_spec _

attribute [irreducible] ZfSet

-- equality of two sets modulo universes
def eqv : ZfSet.{u} -> ZfSet.{v} -> Prop := by
  refine lift₂ (· zf≈ ·) ?_
  intro a b c d ac bd
  simp
  apply Iff.intro
  intro h
  apply ac.symm.trans
  apply h.trans
  assumption
  intro h
  apply ac.trans
  apply h.trans
  symm; assumption

scoped infix:50 " zf= " => eqv

@[refl]
def eqv.refl (s: ZfSet) : s zf= s := by
  cases s with | mk s =>
  apply Equiv.refl

@[symm]
def eqv.symm {a b: ZfSet} (h: a zf= b) : b zf= a := by
  cases a with | mk a =>
  cases b with | mk b =>
  apply Equiv.symm h

def eqv.trans {a b c: ZfSet} (h: a zf= b) (g: b zf= c) : a zf= c := by
  cases a with | mk a =>
  cases b with | mk b =>
  cases c with | mk c =>
  apply Equiv.trans h g

-- if two sets have the same universe then eqv is the same as equality
def eqv_iff_eq {a b: ZfSet} : a zf= b ↔ a = b := by
  apply flip Iff.intro
  intro h; rw [h]
  intro h
  cases a with | mk a =>
  cases b with | mk b =>
  apply sound
  assumption

def Pre.mem (S x: Pre) : Prop := ∃s: S.Type, x zf≈ S.Mem s

instance : Membership Pre.{u} Pre.{u} where
  mem := Pre.mem

def Pre.mem.spec (x y S R: Pre) (hx: x zf≈ y) (hS: S zf≈ R) : S.mem x -> R.mem y := by
  intro ⟨s, h⟩
  have ⟨r, hS⟩ := hS.left s
  exists r
  apply hx.symm.trans
  apply h.trans
  assumption

def mem : ZfSet -> ZfSet -> Prop := by
  refine lift₂ Pre.mem ?_
  intro x S y R hx hS
  ext; apply Iff.intro
  apply Pre.mem.spec
  assumption
  assumption
  apply Pre.mem.spec
  symm; assumption
  symm; assumption

instance : Membership ZfSet.{u} ZfSet.{u} where
  mem := mem

instance : HasSubset ZfSet where
  Subset a b := ∀x ∈ a, x ∈ b

@[pp_with_univ]
def Pre.ulift.{u, v} : Pre.{v} -> Pre.{max u v}
| .intro α memα => .intro (ULift α) (fun x => ulift (memα x.down))

def Pre.ulift.spec (a b: Pre) (h: a zf≈ b) : ulift a zf≈ ulift b := by
  induction h with
  | intro a b ha hb h =>
  cases a with | intro α memα =>
  cases b with | intro β memβ =>
  apply Equiv.intro
  · intro a₀
    have ⟨b₀, hb, h⟩ := ha (ULift.down a₀)
    exists ULift.up b₀
  · intro b₀
    have ⟨a₀, ha, h⟩ := hb (ULift.down b₀)
    exists ULift.up a₀

@[pp_with_univ]
def ulift.{u, v} : ZfSet.{v} -> ZfSet.{max u v} := by
  refine lift (fun s => ⟦s.ulift⟧) ?_
  intro a b h
  simp
  apply sound
  apply Pre.ulift.spec
  assumption

def Pre.ulift_eqv_self.{u, v} (a: Pre) : a zf≈ ulift.{u, v} a := by
  induction a with
  | intro α memα ih =>
  apply Equiv.intro
  · intro a₀
    exists ULift.up a₀
    apply ih
  · intro a₀
    exists ULift.down a₀
    apply ih

def ulift_eqv_self.{u, v} (a: ZfSet) : a zf= ulift.{u, v} a := by
  cases a with | mk a =>
  apply Pre.ulift_eqv_self

def eqv_iff_ulift_eq_ulift (a: ZfSet.{u}) (b: ZfSet.{v}) : a zf= b ↔ ulift.{max u v} a = ulift.{max u v} b := by
  cases a with | mk a =>
  cases b with | mk b =>
  apply Iff.intro
  intro h
  rw [←eqv_iff_eq]
  apply (ulift_eqv_self _).symm.trans
  apply eqv.trans _ (ulift_eqv_self _)
  assumption
  intro h
  apply (ulift_eqv_self _).trans
  apply eqv.trans _ (ulift_eqv_self _).symm
  rw [h]

instance mem_wf : @Relation.IsWellFounded ZfSet (· ∈ ·) where
  wf := by
    apply WellFounded.intro
    intro a
    cases a with | mk a =>
    induction a with | intro α memα ih =>
    apply Acc.intro
    intro b h
    cases b with | mk b =>
    obtain ⟨x, hx⟩ := h
    simp at hx
    rw [sound hx]
    apply ih

def mem_irrefl (a: ZfSet) : ¬a ∈ a := irrefl (· ∈ ·) a
def mem_asymm {a b: ZfSet} : a ∈ b -> ¬b ∈ a := asymm (· ∈ ·)

def Pre.ext.{u, v} (a: Pre.{u}) (b: Pre.{v}) : (∀x: Pre.{max u v}, mem a x ↔ mem b x) -> a zf≈ b := by
  intro h
  induction a with | intro α memα ih =>
  cases b with | intro β memβ =>
  apply Equiv.intro
  · intro a₀
    have ⟨b₀, h⟩ := (h (memα a₀).ulift).mp (by
      apply mem.spec
      apply ulift_eqv_self
      rfl
      exists a₀)
    have := (ulift_eqv_self _).trans h
    exists b₀
  · intro b₀
    have ⟨a₀, h⟩ := (h (memβ b₀).ulift).mpr (by
      apply mem.spec
      apply ulift_eqv_self
      rfl
      exists b₀)
    have := (ulift_eqv_self _).trans h
    exists a₀
    symm; assumption

def ext_eqv.{u, v} (a: ZfSet.{u}) (b: ZfSet.{v}) : (∀x: ZfSet.{max u v}, mem a x ↔ mem b x) -> a zf= b := by
  intro h
  cases a with | mk a =>
  cases b with | mk b =>
  apply Pre.ext
  intro x
  apply h ⟦x⟧

@[ext]
def ext (a b: ZfSet) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := by
  intro h
  rw [←eqv_iff_eq]
  apply ext_eqv
  apply h

instance : @Relation.IsPartialOrder ZfSet (· ⊆ ·) (· = ·) where
  refl _ _ := id
  trans h g x hx := g _ (h _ hx)
  antisymm_by := by
    intro a b ha hb
    ext x
    apply Iff.intro
    apply ha
    apply hb

instance : LE ZfSet := ⟨(· ⊆ ·)⟩
instance : LT ZfSet := ⟨Relation.strict (· ≤ ·)⟩
instance : IsLawfulLT ZfSet where
instance : IsPartialOrder ZfSet where
  le_refl := Relation.refl (rel := (· ⊆ ·))
  le_trans := Relation.trans' (r := (· ⊆ ·))
  le_antisymm := antisymm (· ⊆ ·)

def Pre.nil : Pre := .intro PEmpty PEmpty.elim

def nil : ZfSet := ⟦Pre.nil⟧

instance : EmptyCollection ZfSet where
  emptyCollection := nil

@[simp]
def not_mem_nil (a: ZfSet) : ¬a ∈ (∅: ZfSet) := by cases a; nofun

def Pre.singleton (s: Pre) : Pre := .intro PUnit (fun _ => s)

def Pre.singleton.spec (a b: Pre) (h: a zf≈ b) : a.singleton zf≈ b.singleton := by
  apply Equiv.intro
  intro
  exists ⟨⟩
  intro
  exists ⟨⟩

def singleton : ZfSet -> ZfSet := by
  refine lift (mk ∘ Pre.singleton) ?_
  intro a b h
  apply sound
  apply Pre.singleton.spec
  assumption

instance : Singleton ZfSet ZfSet where
  singleton := singleton

@[simp]
def mem_singleton {s: ZfSet} : ∀{x}, x ∈ ({s}: ZfSet) ↔ x = s := by
  cases s with | mk s =>
  intro x
  cases x with | mk x =>
  apply Iff.intro
  intro ⟨_, h⟩
  apply sound
  assumption
  intro h; rw [h]
  exists ⟨⟩

def Pre.union (a b: Pre.{u}) : Pre :=
  .intro (a.Type ⊕ b.Type) <| fun
    | .inl x => a.Mem x
    | .inr x => b.Mem x

def Pre.union.spec (a b c d: Pre) (ac: a zf≈ c) (bd: b zf≈ d) : a.union b zf≈ c.union d := by
  apply Equiv.intro
  · intro x
    cases x with
    | inl x =>
      have ⟨y, hy⟩ := ac.left x
      exists .inl y
    | inr x =>
      have ⟨y, hy⟩ := bd.left x
      exists .inr y
  · intro x
    cases x with
    | inl x =>
      have ⟨y, hy⟩ := ac.right x
      exists .inl y
    | inr x =>
      have ⟨y, hy⟩ := bd.right x
      exists .inr y

def union : ZfSet -> ZfSet -> ZfSet := by
  refine lift₂ (fun a b => ⟦a.union b⟧) ?_
  intro a b c d h g
  apply sound
  apply Pre.union.spec
  assumption
  assumption

instance : Union ZfSet where
  union := union

instance : Max ZfSet where
  max := union

@[simp]
def mem_union {a b: ZfSet} : ∀{x}, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := by
  intro x
  cases a with | mk a =>
  cases b with | mk b =>
  cases x with | mk x =>
  apply Iff.intro
  · intro ⟨z, h⟩
    cases z with
    | inl a₀ => left; exists a₀
    | inr b₀ => right; exists b₀
  · intro h
    rcases h with ⟨z, h⟩ | ⟨z, h⟩
    exists .inl z
    exists .inr z

def Pre.sep (P: Pre -> Prop) (a: Pre) : Pre :=
  .intro { x: a.Type // P (a.Mem x) } (fun x => a.Mem x.val)

def Pre.sep.spec (a b: Pre) (P Q: Pre -> Prop) (h: a zf≈ b) (g: ∀x y, x zf≈ y -> (P x ↔ Q y)) : a.sep P zf≈ b.sep Q := by
  apply Equiv.intro
  · intro ⟨a₀, ha₀⟩
    have ⟨b₀, h⟩ := h.left a₀
    refine ⟨⟨b₀, ?_⟩, h⟩
    rw [←g]
    assumption
    assumption
  · intro ⟨b₀, hb₀⟩
    have ⟨a₀, h⟩ := h.right b₀
    refine ⟨⟨a₀, ?_⟩, h⟩
    rw [g]
    assumption
    assumption

def sep (P: ZfSet -> Prop) : ZfSet -> ZfSet := by
  refine lift (mk ∘ Pre.sep (P ∘ mk)) ?_
  intro a b h
  apply sound
  apply Pre.sep.spec
  assumption
  intro x y h
  simp
  rw [sound h]

@[simp]
def mem_sep {P: ZfSet -> Prop} {s: ZfSet} : ∀{x}, x ∈ s.sep P ↔ x ∈ s ∧ P x := by
  intro x
  cases s with | mk s =>
  cases x with | mk x =>
  apply Iff.intro
  intro ⟨z, hz⟩
  apply And.intro
  exists z.val
  rw [sound hz]
  exact z.property
  intro ⟨⟨z, hz⟩, g⟩
  exists ⟨z, ?_⟩
  simp
  rwa [←sound hz]
  assumption

def inter (a b: ZfSet) : ZfSet := a.sep (· ∈ b)

instance : Inter ZfSet where
  inter := inter

instance : Min ZfSet where
  min := inter

@[simp]
def mem_inter {a b: ZfSet} : ∀{x}, x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := by
  apply mem_sep

protected def insert (a b: ZfSet) := {a} ∪ b

instance : Insert ZfSet ZfSet where
  insert := ZfSet.insert

def insert_def (a b: ZfSet) : insert a b = {a} ∪ b := rfl

@[simp]
def mem_insert {a b: ZfSet} : ∀{x}, x ∈ insert a b ↔ x = a ∨ x ∈ b := by simp [insert_def]

attribute [irreducible] union inter sep ulift ZfSet.insert

def min_eq_inter (a b: ZfSet) : a ⊓ b = a ∩ b := rfl
def max_eq_union (a b: ZfSet) : a ⊔ b = a ∪ b := rfl

instance : IsLattice ZfSet where
  le_max_left := by
    intro a b x
    simp [max_eq_union]
    apply Or.inl
  le_max_right := by
    intro a b x
    simp [max_eq_union]
    apply Or.inr
  max_le := by
    intro S a b h g x
    simp [max_eq_union]
    intro h; cases h
    apply h
    assumption
    apply g
    assumption
  min_le_left := by
    intro a b x
    simp [min_eq_inter]
    intros; assumption
  min_le_right := by
    intro a b x
    simp [min_eq_inter]
  le_min := by
    intro a b S h g x
    simp [min_eq_inter]
    intro
    apply And.intro
    apply h
    assumption
    apply g
    assumption

instance : @Std.Associative ZfSet (· ∪ ·) := ⟨max_assoc⟩
instance : @Std.Associative ZfSet (· ∩ ·) := ⟨min_assoc⟩
instance : @Std.Commutative ZfSet (· ∪ ·) := ⟨max_comm⟩
instance : @Std.Commutative ZfSet (· ∩ ·) := ⟨min_comm⟩

def union_comm (a b: ZfSet) : a ∪ b = b ∪ a := max_comm _ _
def inter_comm (a b: ZfSet) : a ∩ b = b ∩ a := min_comm _ _
def union_assoc (a b c: ZfSet) : a ∪ b ∪ c = a ∪ (b ∪ c) := max_assoc _ _ _
def inter_assoc (a b c: ZfSet) : a ∩ b ∩ c = a ∩ (b ∩ c) := min_assoc _ _ _

@[simp] def union_nil (a: ZfSet) : a ∪ ∅ = a := by ext; simp
@[simp] def nil_union (a: ZfSet) : ∅ ∪ a = a := by ext; simp
@[simp] def sep_nil {P: ZfSet -> Prop} : sep P ∅ = ∅ := by ext; simp
@[simp] def inter_nil (a: ZfSet) : a ∩ ∅ = ∅ := by ext; simp
@[simp] def nil_inter (a: ZfSet) : ∅ ∩ a = ∅ := by ext; simp
@[simp] def insert_nil (a: ZfSet) : insert a ∅ = ({a} :ZfSet) := by ext; simp

@[simp] def union_insert (x a b: ZfSet) : a ∪ (insert x b) = insert x (a ∪ b) := by ext; simp; ac_nf
@[simp] def insert_union (x a b: ZfSet) : (insert x a) ∪ b = insert x (a ∪ b) := by ext; simp; ac_nf
@[simp] def insert_inter_insert (x a b: ZfSet) : (insert x a) ∩ (insert x b) = insert x (a ∩ b) := by ext; simp [or_and_left]
@[simp] def insert_idempot (x a: ZfSet) : insert x (insert x a) = insert x a := by ext; simp

@[simp] def inter_union_inter_left (k a b: ZfSet) : (k ∪ a) ∩ (k ∪ b) = k ∪ (a ∩ b) := by ext; simp [or_and_left]
@[simp] def inter_union_inter_right (k a b: ZfSet) : (a ∪ k) ∩ (b ∪ k) = (a ∩ b) ∪ k := by simp [union_comm _ k]

@[simp] def union_inter_union_left (k a b: ZfSet) :  (k ∩ a) ∪ (k ∩ b) = k ∩ (a ∪ b) := by ext; simp [and_or_left]
@[simp] def union_inter_union_right (k a b: ZfSet) : (a ∩ k) ∪ (b ∩ k) = (a ∪ b) ∩ k := by simp [inter_comm _ k]

protected def Nonempty (s: ZfSet) := ∃x, x ∈ s

@[simp] def nonempty_insert (x a: ZfSet) : (insert x a).Nonempty := ⟨x, by simp⟩
@[simp] def nonempty_singleton (x: ZfSet) : ZfSet.Nonempty {x} := ⟨x, by simp⟩
@[simp] def nonempty_of_inter_left (a b: ZfSet) (h: (a ∩ b).Nonempty) : a.Nonempty := by
  obtain ⟨x, h⟩ := h; simp at h; exists x; exact h.left
@[simp] def nonempty_of_inter_right (a b: ZfSet) (h: (a ∩ b).Nonempty) : b.Nonempty := by
  obtain ⟨x, h⟩ := h; simp at h; exists x; exact h.right
@[simp] def nonempty_union_of_left (a b: ZfSet) (h: a.Nonempty) : (a ∪ b).Nonempty := by
  obtain ⟨x, h⟩ := h; exists x; simp [h]
@[simp] def nonempty_union_of_right (a b: ZfSet) (h: b.Nonempty) : (a ∪ b).Nonempty := by
  obtain ⟨x, h⟩ := h; exists x; simp [h]
@[simp]
def not_nonempty_iff {s: ZfSet} : ¬s.Nonempty ↔ s = ∅ := by
  apply Iff.intro
  intro h
  ext x; simp; intro g
  apply h
  exists x
  rintro rfl
  intro ⟨x, h⟩
  simp at h

@[simp]
def ne_empty_iff {s: ZfSet} : s ≠ ∅ ↔ s.Nonempty := by
  rw [←Classical.not_not (a := s.Nonempty), Iff.comm]
  simp

protected def Pre.sUnion (U: Pre) : Pre :=
  .intro (Σu: U.Type, (U.Mem u).Type) fun ⟨u₀, u₁⟩ => (U.Mem u₀).Mem u₁

def Pre.sUnion.spec (a b: Pre) (h: a zf≈ b) : a.sUnion zf≈ b.sUnion := by
  apply Equiv.intro
  · intro ⟨a₀, a₁⟩
    have ⟨b₀, h⟩ := h.left a₀
    have ⟨b₁, h⟩ := h.left a₁
    exists ⟨b₀, b₁⟩
  · intro ⟨b₀, b₁⟩
    have ⟨a₀, h⟩ := h.right b₀
    have ⟨a₁, h⟩ := h.right b₁
    exists ⟨a₀, a₁⟩

protected def sUnion : ZfSet -> ZfSet := by
  refine lift (mk ∘ Pre.sUnion) ?_
  intro a b h
  apply sound
  apply Pre.sUnion.spec
  assumption

@[simp]
def mem_sUnion {s: ZfSet} : ∀{x}, x ∈ s.sUnion ↔ ∃s' ∈ s, x ∈ s' := by
  intro x
  cases s with | mk s =>
  cases x with | mk x =>
  apply Iff.intro
  · intro ⟨⟨a₀, a₁⟩, h⟩
    exists ⟦s.Mem a₀⟧
    apply And.intro
    exists a₀
    exists a₁
  · intro ⟨s', h, g⟩
    cases s' with | mk s' =>
    obtain ⟨a₀, h⟩ := h
    obtain ⟨a₁, g⟩ := g
    have ⟨a₂, h⟩ := h.left a₁
    apply Pre.mem.spec
    symm; apply g
    rfl
    exists ⟨a₀, a₂⟩

protected def sInter (U: ZfSet) : ZfSet := U.sUnion.sep (fun s => ∀u ∈ U, s ∈ u)

@[simp]
def mem_sInter {U: ZfSet} (h: U.Nonempty) : ∀{x}, x ∈ U.sInter ↔ ∀u ∈ U, x ∈ u := by
  intro x
  cases U with | mk U =>
  cases x with | mk x =>
  simp [ZfSet.sInter]
  intro g
  obtain ⟨u', hu'⟩ := h
  exists u'
  apply And.intro
  assumption
  apply g
  assumption

attribute [irreducible] ZfSet.sUnion ZfSet.sInter

@[simp] def sUnion_nil : ZfSet.sUnion ∅ = ∅ := by ext x; simp
@[simp] def sInter_nil : ZfSet.sInter ∅ = ∅ := by simp [ZfSet.sInter]

@[simp] def sUnion_insert (x a: ZfSet) : ZfSet.sUnion (insert x a) = x ∪ ZfSet.sUnion a := by ext x; simp
@[simp] def sInter_insert (x a: ZfSet) (ha: a.Nonempty) : ZfSet.sInter (insert x a) = x ∩ ZfSet.sInter a := by
  ext x; simp [mem_sInter ha]
@[simp] def sUnion_singleton (a: ZfSet) : ZfSet.sUnion {a} = a := by ext; simp
@[simp] def sInter_singleton (a: ZfSet) : ZfSet.sInter {a} = a := by ext; simp
@[simp] def sUnion_union (a b: ZfSet) : ZfSet.sUnion (a ∪ b) = ZfSet.sUnion a ∪ ZfSet.sUnion b := by
  ext; simp [or_and_right]
  apply Iff.intro
  intro ⟨s', h⟩
  rcases h with ⟨h, g⟩ | ⟨h, g⟩
  left; exists s'
  right; exists s'
  intro h
  rcases h with ⟨s', h, g⟩ | ⟨s', h, g⟩
  exists s'; left; trivial
  exists s'; right; trivial
@[simp] def sInter_union (a b: ZfSet) (ha: a.Nonempty) (hb: b.Nonempty) : ZfSet.sInter (a ∪ b) = ZfSet.sInter a ∩ ZfSet.sInter b := by
  ext; simp [ha, hb]
  apply Iff.intro
  · intro h
    apply And.intro
    intro u hu
    apply h
    left; assumption
    intro u hu
    apply h
    right; assumption
  · intro ⟨h, g⟩
    intro u hu
    cases hu
    apply h; assumption
    apply g; assumption

end ZfSet
