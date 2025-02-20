import Math.Algebra.Ring.Defs

structure Ring (α: Type*) where
  [ops: RingOps α]
  [spec: IsRing α]

namespace Ring

def Elem (_: Ring α) := α

instance : CoeSort (Ring α) (Type _) := ⟨Elem⟩

instance (r: Ring α) : RingOps r := r.ops
instance (r: Ring α) : IsRing r := r.spec

def opp (r: Ring α) : Ring αᵐᵒᵖ :=
  let _ := r.ops
  have := r.spec
  Ring.mk

end Ring
