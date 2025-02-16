import Math.Algebra.LinearMap
import Math.Algebra.Field.Defs
import Math.Algebra.Group.Action.Basic
import Math.Data.Set.Basic

structure VectorSpace (R A: Type*) where
  [smul: SMul R A]
  [scalar_field_ops: FieldOps R]
  [scalar_field: IsField R]
  [vector_add_group_ops: AddGroupOps A]
  [vector_add_group: IsAddGroup A]
  [vector_add_comm: IsAddCommMagma A]
  [is_module: IsModule R A]

namespace VectorSpace

def Scalar (_: VectorSpace R A) := R
def Vector (_: VectorSpace R A) := A

section

variable (V: VectorSpace R A)

instance : FieldOps V.Scalar := V.scalar_field_ops
instance : IsField V.Scalar := V.scalar_field
instance : AddGroupOps V.Vector := V.vector_add_group_ops
instance : IsAddGroup V.Vector := V.vector_add_group
instance : IsAddCommMagma V.Vector := V.vector_add_comm
instance : SMul V.Scalar V.Vector := V.smul
instance : IsModule V.Scalar V.Vector := V.is_module

end

def linear_combination (V: VectorSpace R A) : List (V.Scalar × V.Vector) -> V.Vector
| [] => 0
| (r, x)::xs => r • x + linear_combination V xs

def smul_linear_combination (V: VectorSpace R A) (r: V.Scalar) (xs: List (V.Scalar × V.Vector)) :
  r • V.linear_combination xs = V.linear_combination  (xs.map fun (r₀, x) => (r * r₀, x)) := by
  induction xs with
  | nil => apply smul_zero
  | cons x xs ih =>
    obtain ⟨r₀, x⟩ := x
    dsimp
    unfold linear_combination
    rw [smul_add, mul_smul, ih]

def linear_combination_extract
  (V: VectorSpace R A) (xs: List (V.Scalar × V.Vector)) (i: Nat) (hi: i < xs.length):
  V.linear_combination xs = xs[i].fst • xs[i].snd + V.linear_combination (xs.eraseIdx i) := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => contradiction
    | cons x xs => rfl
  | succ i ih =>
    cases xs with
    | nil => contradiction
    | cons x xs =>
      dsimp
      unfold linear_combination
      rw [add_left_comm, ih]

-- a finite set is linearly indepenedent iff the the only linear combination
-- of vectors equals zero is if all the scalars are equal to zero, i.e. the
-- trivial linear combination
def IsFiniteLinearlyIndependent (V: VectorSpace R A) (xs: List V.Vector) :=
  (∀(rs: List V.Scalar), rs.length = xs.length ->
    linear_combination V (rs.zip xs) = 0 -> ∀r ∈ rs, r = 0)

-- a possibly infinite set is linearly independent iff all
-- finite subsets are linearly independent
def IsLinearlyIndependent (V: VectorSpace R A) (s: Set V.Vector) :=
  ∀l: List V.Vector, l.Nodup -> Set.ofList l ⊆ s -> IsFiniteLinearlyIndependent V l

-- the span of a set of vectors is the set of all vectors
-- which can be made from any finite subset of `S`
def Span (V: VectorSpace R A) (S: Set V.Vector): Set V.Vector :=
  Set.mk fun v =>
  ∃(rs: List V.Scalar) (xs: List V.Vector), rs.length = xs.length ∧
  Set.ofList xs ⊆ S ∧ v = V.linear_combination (rs.zip xs)

-- a linearly independent set of vectors whose span is the entire vector space
def IsBasis (V: VectorSpace R A) (S: Set V.Vector) := V.IsLinearlyIndependent S ∧ V.Span S = ⊤

end VectorSpace
