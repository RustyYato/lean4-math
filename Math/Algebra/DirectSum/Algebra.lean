import Math.Algebra.DirectSum.Ring
import Math.Algebra.Algebra.Defs

variable (R: Type*) (A : γ -> Type*) [DecidableEq γ]
  [AddMonoidOps γ] [IsAddMonoid γ] [∀i, AddMonoidOps (A i)]
  [GSemiringOps A] [IsGSemiring A]
  [SemiringOps R] [IsSemiring R]
  [∀i, SMul R (A i)] [∀i, IsModule R (A i)]

class GAlgebraMap [Zero γ] where
  toFun: R →+ A 0

class IsGAlgebra [GAlgebraMap R A] [IsGSemiring A] : Prop where
  map_one : GAlgebraMap.toFun (A := A) (1: R) = GOne.gOne
  map_mul (a b: R) : GradedMonoid.mk (A := A) (GAlgebraMap.toFun (a * b)) =
    GradedMonoid.mk (GAlgebraMap.toFun a) * GradedMonoid.mk (GAlgebraMap.toFun b)
  commutes {i} (r: R) (a: A i) :
    GradedMonoid.mk (GAlgebraMap.toFun r: A 0) * GradedMonoid.mk a =
    GradedMonoid.mk a * GradedMonoid.mk (GAlgebraMap.toFun r: A 0)
  smul_def {i} (r: R) (a: A i) :
    GradedMonoid.mk (r • a) =
    GradedMonoid.mk (GAlgebraMap.toFun r: A 0) * GradedMonoid.mk a

namespace DirectSum

variable [GAlgebraMap R A] [IsGAlgebra R A]

instance : AlgebraMap R (A 0) where
  toFun := GAlgebraMap.toFun
  map_zero := map_zero GAlgebraMap.toFun
  map_add := map_add GAlgebraMap.toFun
  map_one := IsGAlgebra.map_one
  map_mul := by
    intro a b
    let x : GradedMonoid A := GradedMonoid.mk (GAlgebraMap.toFun (a * b))
    let a' : GradedMonoid A := GradedMonoid.mk (GAlgebraMap.toFun a)
    let b' : GradedMonoid A := GradedMonoid.mk (GAlgebraMap.toFun b)
    symm; apply cast_eq_of_heq
    apply (GradedMonoid.mk_inj _ _ _).right
    symm; apply IsGAlgebra.map_mul

instance [GAlgebraMap R A] : AlgebraMap R (⊕i, A i) :=
  AlgebraMap.ofHom (ιHom.comp algebraMap)

instance [IsGAlgebra R A] : IsAlgebra R (⊕i, A i) where
  commutes r a := by
    induction a with
    | zero => simp
    | add => rw [mul_add, add_mul]; congr
    | ι i a =>
      show ι 0 (algebraMap r) * _ = _ * ι 0 (algebraMap r)
      rw [mul_ι, mul_ι]
      let r' := GradedMonoid.mk (algebraMap r: A 0)
      let a' := GradedMonoid.mk a
      let x := r' * a'
      let y := a' * r'
      show ι x.fst x.snd = ι y.fst y.snd
      suffices x = y by rw [this]
      apply IsGAlgebra.commutes
  smul_def r a := by
    induction a with
    | zero => simp
    | add => rw [smul_add, mul_add]; congr
    | ι i a =>
      suffices r • (ι i a) = ι i (r • a) by
        rw [this]
        let r' := GradedMonoid.mk (algebraMap r: A 0)
        let a' := GradedMonoid.mk a
        let x := GradedMonoid.mk (r • a)
        let y := r' * a'
        show ι x.fst x.snd = ι 0 (algebraMap r) * _
        rw [mul_ι]; show ι x.fst x.snd = ι y.fst y.snd
        suffices x = y by rw [this]
        apply IsGAlgebra.smul_def
      ext j; simp [apply_ι]
      split; subst j; rfl
      simp

end DirectSum
