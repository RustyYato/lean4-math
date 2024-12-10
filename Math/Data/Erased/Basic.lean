import Math.Type.Notation
import Math.Function.Basic

structure Erased (α: Sort*) where
  ofFn ::
  fn: α -> Prop
  spec: ∃a, fn = fun b => a = b

noncomputable def Erased.out (a: Erased α): α := Classical.choose a.spec
def Erased.mk (a: α): Erased α where
  fn := fun b => a = b
  spec := ⟨a, rfl⟩

def Erased.mk_inj : Function.Injective (@mk α) := by
  intro a b eq
  rw [congrFun (ofFn.inj eq) b]

def Erased.mk_out (a: Erased α) : mk a.out = a := by
  cases a with | ofFn a spec =>
  unfold mk out
  congr
  rw [←Classical.choose_spec spec]

def Erased.ofNonempty (h: Nonempty α) : Erased α := mk (Classical.choice h)
def Erased.toNonempty (h: Erased α) : Nonempty α := nonempty_of_exists h.spec
