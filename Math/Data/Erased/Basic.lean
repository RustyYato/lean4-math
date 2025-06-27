import Math.Type.Notation
import Math.Logic.Equiv.Defs
import Math.Function.Basic

structure Erased (α: Sort*) where
  ofFn ::
  fn: α -> Prop
  spec: ∃a, fn = fun b => a = b

namespace Erased

noncomputable def out (a: Erased α): α := Classical.choose a.spec
def mk : α ↪ Erased α where
  toFun a := {
    fn := fun b => a = b
    spec := ⟨a, rfl⟩
  }
  inj' := by
    intro a b eq
    rw [congrFun (ofFn.inj eq) b]

def mk_out (a: Erased α) : mk a.out = a := by
  cases a with | ofFn a spec =>
  unfold mk out
  rw [Embedding.mk_apply]
  congr; apply (Classical.choose_spec spec).symm
def out_mk (a: α) : (mk a).out = a := by
  apply mk.inj
  rw [mk_out]

def ofNonempty (h: Nonempty α) : Erased α := mk (Classical.choice h)
def toNonempty (h: Erased α) : Nonempty α := nonempty_of_exists h.spec

def liftRel (r: α -> α -> Prop) : Erased α -> Erased α -> Prop :=
  fun a b => ∃x y, r x y ∧ a.fn x ∧ b.fn y

@[induction_eliminator]
def induction {motive: Erased α -> Prop} (mk: ∀x, motive (mk x)) (e: Erased α) : motive e := by
  obtain ⟨_, a, rfl⟩ := e
  apply mk

end Erased

namespace Equiv

noncomputable def erased (α: Sort*) : α ≃ Erased α where
  toFun := Erased.mk
  invFun := Erased.out
  leftInv _ := by
    apply Erased.mk.inj
    rw [Erased.mk_out]
  rightInv := by apply Erased.mk_out

end Equiv

namespace Bijection

def erased (α: Sort*) : α ⇔ Erased α := {
  Erased.mk with
  surj' := by
    intro a
    induction a with | mk a =>
    exists a
}

end Bijection
