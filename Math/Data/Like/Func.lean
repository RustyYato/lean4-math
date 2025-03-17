import Math.Function.Basic
import Math.Logic.Basic
import Math.Type.Notation
import Lean.Elab.Command

class DFunLike (F: Sort*) (α: outParam Sort*) (β: outParam (α -> Sort*)) where
  coe: F -> ∀x, β x
  coe_inj: Function.Injective coe

abbrev FunLike (F: Sort*) (α β: outParam <| Sort*) := DFunLike F α (fun _ => β)

instance [DFunLike F α β] : CoeFun F (fun _ => ∀x, β x) where
  coe := DFunLike.coe

instance {β: α -> Sort*} : DFunLike (∀x, β x) α β where
  coe := id
  coe_inj _ _ := id

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.Meta.registerCoercion ``DFunLike.coe
    (some { numArgs := 5, coercee := 4, type := .coeFun })

namespace DFunLike

def coe.inj [d: DFunLike F α β]: Function.Injective d.coe := DFunLike.coe_inj

def ext [DFunLike F α β] (a b: F) : (∀x, a x = b x) -> a = b := by
  intro h
  apply DFunLike.coe_inj
  funext x
  exact h _

def ext_iff [DFunLike F α β] {a b: F} : a = b ↔ (∀x, a x = b x) := by
  apply Iff.intro _ (ext _ _)
  intro
  subst b
  intro
  rfl

def exists_ne [DFunLike F α β] {a b: F} (h: a ≠ b) : ∃x, a x ≠ b x := by
  apply Classical.not_forall.mp
  apply ext_iff.not_iff_not.mp
  exact h

end DFunLike

namespace FunLike

variable {F α β : Sort*} [i : FunLike F α β]

def congr {f g : F} {x y : α} (h₁ : f = g) (h₂ : x = y) : f x = g y :=
  _root_.congr (congrArg _ h₁) h₂

def congrArg (f : F) {x y : α} (h₂ : x = y) : f x = f y :=
  _root_.congrArg _ h₂

def coe_apply (f: F) {x: α} : DFunLike.coe f x = f x := rfl

def comp (f: A -> B) (h: Function.Injective f) [fl: FunLike B α β] : FunLike A α β where
  coe := fl.coe ∘ f
  coe_inj := by
    apply Function.Injective.comp
    apply fl.coe_inj
    assumption

end FunLike
