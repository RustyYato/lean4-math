import Math.Algebra.LinearMap
import Math.Algebra.Field.Defs
import Math.Algebra.Group.Action.Basic

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

def linear_combination
  (V: VectorSpace R A) : ∀(rs: List V.Scalar) (xs: List V.Vector), rs.length = xs.length -> V.Vector
| [], [], .refl _ => 0
| r::rs, x::xs, h => r • x + linear_combination V rs xs (Nat.succ.inj h)

def smul_linear_combination
  (V: VectorSpace R A) (r: V.Scalar) (rs: List V.Scalar) (xs: List V.Vector) (h: rs.length = xs.length) :
  r • V.linear_combination rs xs h = V.linear_combination (rs.map (fun r₀ => r * r₀)) xs (by
    rw [List.length_map]
    assumption) := by
  induction xs generalizing rs with
  | nil =>
    cases rs with
    | cons r rs => contradiction
    | nil =>
      unfold linear_combination
      dsimp
      rw [smul_zero]
  | cons x xs ih =>
    cases rs with
    | nil => contradiction
    | cons r₀ rs =>
    unfold linear_combination
    dsimp
    rw [smul_add, mul_smul]
    congr
    apply ih

def linear_combination_extract
  (V: VectorSpace R A) (rs: List V.Scalar) (xs: List V.Vector) (h: rs.length = xs.length)
  (i: Nat) (hi: i < xs.length):
  V.linear_combination rs xs h = rs[i] • xs[i] + V.linear_combination (rs.eraseIdx i) (xs.eraseIdx i) (by
    rw [List.length_eraseIdx, List.length_eraseIdx, if_pos, if_pos, h]
    assumption
    rw [h]; assumption) := by
  induction i generalizing xs rs with
  | zero =>
    cases xs with
    | nil => contradiction
    | cons x xs =>
    cases rs with
    | nil => contradiction
    | cons r rs => rfl
  | succ i ih =>
    cases xs with
    | nil => contradiction
    | cons x xs =>
    cases rs with
    | nil => contradiction
    | cons r rs =>
    dsimp
    unfold linear_combination
    rw [←add_assoc, add_comm _ (r • x), add_assoc]
    congr
    apply ih

end VectorSpace
