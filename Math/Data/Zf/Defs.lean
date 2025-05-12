import Math.Data.Quotient.Basic
import Math.Data.Trunc
import Math.Type.Notation
import Math.Data.Set.Basic
import Math.Relation.Defs
import Math.Tactics.PPWithUniv

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

end ZfSet
