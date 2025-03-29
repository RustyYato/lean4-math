import Math.Function.Basic
import Math.Data.Like.Func
import Math.Logic.Equiv.Defs

structure Matrix (α N M: Type*) where
  of :: toFun : N -> M -> α

namespace Matrix

def transpose : Matrix α N M -> Matrix α M N
| .of f => .of (flip f)

postfix:max "ᵀ" => transpose

attribute [coe] toFun

instance : FunLike (Matrix α N M) N (M -> α) where
  coe := toFun
  coe_inj := by
    intro a b eq
    cases a; congr

@[ext]
def ext (a b: Matrix α N M) : (∀i j, a i j = b i j) -> a = b := by
  intro h
  apply DFunLike.coe_inj
  ext i j
  apply h

def submatrix (a: Matrix α N M) (f: N₀ -> N) (g: M₀ -> M) : Matrix α N₀ M₀ where
  toFun n m := a.toFun (f n) (g m)

@[simp]
def apply_submatrix (a: Matrix α N M) (f: N₀ -> N) (g: M₀ -> M) (n: N₀) (m: M₀) :
  a.submatrix f g n m = a (f n) (g m) := rfl

def submatrixEquiv (f: N ≃ N₀) (g: M ≃ M₀) : Matrix α N M ≃ Matrix α N₀ M₀ where
  toFun a := a.submatrix f.symm g.symm
  invFun a := a.submatrix f g
  leftInv a := by ext n m; simp
  rightInv a := by ext n m; simp

end Matrix
