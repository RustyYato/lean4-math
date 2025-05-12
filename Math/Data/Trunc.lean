import Math.Type.Notation
import Math.Data.Setoid.Basic

def Trunc (α: Sort*) := Quotient (Setoid.trueSetoid α)

namespace Trunc

def mk : α -> Trunc α := Quotient.mk _

scoped notation "⟦" x "⟧" => mk x

instance : Subsingleton (Trunc α) where
  allEq := by
    intro a b
    induction a, b using Quotient.ind₂
    apply Quotient.sound
    trivial

def lift : (f: α -> β) -> (resp: ∀a b, f a = f b) -> Trunc α -> β :=
  fun f resp => Quotient.lift f (fun a b _ => resp a b)
def lift₂ : (f: α₀ -> α₁ -> β) -> (resp: ∀a b c d, f a b = f c d) -> Trunc α₀ -> Trunc α₁ -> β :=
  fun f resp => Quotient.lift₂ f (fun a b c d _ _ => resp a b c d)

@[induction_eliminator]
def ind {motive: Trunc α -> Prop} : (mk: ∀x, motive ⟦x⟧) -> ∀x, motive x := Quotient.ind

instance [Inhabited α] : Inhabited (Trunc α) where
  default := ⟦default⟧
instance [h: Nonempty α] : Nonempty (Trunc α) :=
  have ⟨x⟩ := h
  ⟨⟦x⟧⟩

def bind (a: Trunc α) (f: α -> Trunc β) : Trunc β :=
  a.lift f (fun _ _ => Subsingleton.allEq _ _)

def map (f: α -> β) (a: Trunc α) : Trunc β := a.bind ((⟦·⟧) ∘ f)

instance : Monad Trunc where
  pure := (⟦·⟧)
  bind := bind
  map := map

open Subsingleton in instance : LawfulMonad Trunc where
  map_const := rfl
  id_map _ := allEq _ _
  seqLeft_eq _ _ := allEq _ _
  seqRight_eq _ _ := allEq _ _
  pure_seq _ _ := allEq _ _
  bind_pure_comp _ _ := allEq _ _
  bind_map _ _ := allEq _ _
  pure_bind _ _ := allEq _ _
  bind_assoc _ _ _ := allEq _ _

def nonempty (x: Trunc α) : Nonempty α := nonempty_of_exists x.exists_rep
def nonempty_iff : Nonempty α ↔ Nonempty (Trunc α) := by
  apply Iff.intro
  intro; infer_instance
  intro ⟨x⟩; exact x.nonempty

noncomputable def out (x: Trunc α) : α := Classical.choice x.nonempty
def out_spec (x: Trunc x) : ⟦x.out⟧ = x := Subsingleton.allEq _ _

@[simp]
def mk_lift : lift f resp (mk x) = f x := rfl

instance : DecidableEq (Trunc α) := fun  _ _  =>  .isTrue (Subsingleton.allEq _ _)

end Trunc

def Quot.attach {r: α -> α -> Prop} : ∀q: Quot r, Trunc { a // q = Quot.mk _ a } := by
  refine Quot.rec ?_ ?_
  intro x
  exact Trunc.mk ⟨x, rfl⟩
  intro a b h
  apply Subsingleton.allEq

def Quotient.attach {s: Setoid α} : ∀q: Quotient s, Trunc { a // q = Quotient.mk _ a } := by
  apply Quot.attach
