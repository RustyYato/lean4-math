import Math.Type.Notation
import Math.Function.Basic

structure Erased (α: Sort*) where
  ofFn ::
  fn: α -> Prop
  spec: ∃a, fn = fun b => a = b

namespace Erased

noncomputable def out (a: Erased α): α := Classical.choose a.spec
def mk (a: α): Erased α where
  fn := fun b => a = b
  spec := ⟨a, rfl⟩

def mk_inj : Function.Injective (@mk α) := by
  intro a b eq
  rw [congrFun (ofFn.inj eq) b]

def mk_out (a: Erased α) : mk a.out = a := by
  cases a with | ofFn a spec =>
  unfold mk out
  congr
  rw [←Classical.choose_spec spec]

def ofNonempty (h: Nonempty α) : Erased α := mk (Classical.choice h)
def toNonempty (h: Erased α) : Nonempty α := nonempty_of_exists h.spec

def liftRel (r: α -> α -> Prop) : Erased α -> Erased α -> Prop :=
  fun a b => ∃x y, r x y ∧ a.fn x ∧ b.fn y

@[induction_eliminator]
def induction {motive: Erased α -> Prop} (mk: ∀x, motive (mk x)) (e: Erased α) : motive e := by
  obtain ⟨_, a, rfl⟩ := e
  apply mk

end Erased
