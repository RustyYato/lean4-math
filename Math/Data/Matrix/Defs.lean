import Math.Function.Basic
import Math.Data.Like.Func

structure Matrix (α n m: Type*) where
  of :: toFun : n -> m -> α

namespace Matrix

def transpose : Matrix α n m -> Matrix α m n
| .of f => .of (flip f)

postfix:max "ᵀ" => transpose

attribute [coe] toFun

instance : FunLike (Matrix α n m) n (m -> α) where
  coe := toFun
  coe_inj := by
    intro a b eq
    cases a; congr

@[ext]
def ext (a b: Matrix α n m) : (∀i j, a i j = b i j) -> a = b := by
  intro h
  apply DFunLike.coe_inj
  ext i j
  apply h

end Matrix
