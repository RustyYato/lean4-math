import Math.Algebra.Semiring.SetLike.Defs
import Math.Algebra.Hom.Defs
import Math.Algebra.Monoid.Action.SetLike.Defs

section

variable (S R: Type*) {α: Type*} [SetLike S α]
  [Zero α] [One α] [Add α] [Mul α]
  [Zero R] [One R] [Add R] [Mul R]
  [AlgebraMap R α] [SMul R α]

class IsAlgebraMapMem where
  mem_algebraMap (s: S) (r: R) : algebraMap r ∈ s := by intro s; exact s.mem_algebraMap

class IsSubalgebra extends IsAlgebraMapMem S R, IsSubsemiring S where

end

section

variable (R α: Type*)
  [Zero α] [One α] [Add α] [Mul α]
  [Zero R] [One R] [Add R] [Mul R]
  [AlgebraMap R α] [SMul R α]

class Subalgebra extends AddSubsemigroup α, Subsemigroup α where
  mem_algebraMap (r: R) : algebraMap r ∈ carrier

instance : SetLike (Subalgebra R α) α where
instance : IsSubalgebra (Subalgebra R α) R where
  mem_zero s := by
    rw [←map_zero (algebraMap (R := R))]
    apply Subalgebra.mem_algebraMap
  mem_one s := by
    rw [←map_one (algebraMap (R := R))]
    apply Subalgebra.mem_algebraMap

end

section

variable (R: Type*) {α: Type*} [SetLike S α]
  [Zero α] [One α] [Add α] [Mul α]
  [Zero R] [One R] [Add R] [Mul R]
  [AlgebraMap R α] [SMul R α]

def mem_algebraMap [IsAlgebraMapMem S R] (s: S) (r: R) : algebraMap r ∈ s := IsAlgebraMapMem.mem_algebraMap _ _

@[ext]
def ext (a b: Subsemiring α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

inductive Generate (U: Set α) : α -> Prop where
| of (a: α) : a ∈ U -> Generate U a
| add {a b: α} : Generate U a -> Generate U b -> Generate U (a + b)
| mul {a b: α} : Generate U a -> Generate U b -> Generate U (a * b)
| algebraMap (r: R) : Generate U (algebraMap r)

def generate (U: Set α) : Subalgebra R α where
  carrier := Set.mk (Generate R U)
  mem_add := Generate.add
  mem_mul := Generate.mul
  mem_algebraMap := Generate.algebraMap

end
