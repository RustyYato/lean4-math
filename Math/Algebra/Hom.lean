import Math.Algebra.RingHom
import Math.Algebra.Basic

variable (F R A B: Type*)
  [FunLike F A B]
  [Zero R] [One R] [Add R] [Mul R]
  [Zero A] [One A] [Add A] [Mul A]
  [Zero B] [One B] [Add B] [Mul B]
  [AlgebraMap R A] [AlgebraMap R B]

structure AlgebraMapHom where
  toFun: A -> B
  resp_algebraMap : ∀r: R, toFun (algebraMap r: A) = (algebraMap r: B)

notation:25 A " →ₐ₀[" R "] " B => AlgebraMapHom R A B

class AlgebraMapHomClass where
  resp_algebraMap (f: F) : ∀r: R, f (algebraMap r: A) = (algebraMap r: B)

export AlgebraMapHomClass (resp_algebraMap)

structure AlgHom extends SemiringHom A B where
  resp_algebraMap : ∀r: R, toFun (algebraMap r: A) = (algebraMap r: B)

notation:25 A " →ₐ[" R "] " B => AlgHom R A B

instance : FunLike (AlgHom R A B) A B where
  coe f := f.toFun
  coe_inj := by
    intro x y eq
    cases x; cases y
    congr
    apply DFunLike.coe_inj eq

instance : ZeroHomClass (AlgHom R A B) A B where
  resp_zero f := f.resp_zero

instance : OneHomClass (AlgHom R A B) A B where
  resp_one f := f.resp_one

instance : AddHomClass (AlgHom R A B) A B where
  resp_add f := f.resp_add

instance : MulHomClass (AlgHom R A B) A B where
  resp_mul f := f.resp_mul

instance : AlgebraMapHomClass (AlgHom R A B) R A B where
  resp_algebraMap f := f.resp_algebraMap

variable [ZeroHomClass F A B] [OneHomClass F A B] [AddHomClass F A B] [MulHomClass F A B]
   [AlgebraMapHomClass F R A B]

@[coe]
def toAlgebraMapHom (f: F) : AlgebraMapHom R A B where
  toFun := f
  resp_algebraMap := resp_algebraMap f

@[coe]
def toAlgHom (f: F) : AlgHom R A B where
  toSemiringHom := toSemiringHom f
  resp_algebraMap := resp_algebraMap f
