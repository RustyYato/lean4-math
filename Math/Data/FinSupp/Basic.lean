import Math.Data.Set.Finite
import Math.Data.Set.Like.Nat
import Math.Data.StdNat.Find

variable (α β: Type*) (S: Type*) [SetLike S α]

section

variable (f: α -> β) (default: β) (set: S)

structure FinSupp.IsFiniteSupport where
  finite: IsFinite set
  spec: ∀x, x ∈ set ∨ f x = default

end

structure FinSupp (default: β) where
  coeffs: α -> β
  support: Squash { set: S // FinSupp.IsFiniteSupport α β S coeffs default set }

variable {α: Type*} {β: α -> Type*} {default: ∀x, β x} {S: Type*} [SetLike S α]
