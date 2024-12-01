import Math.Function.Basic
import Math.Data.Like.Embedding
import Math.Type.Notation

class IsEquivLike (E: Sort*) (α β: outParam (Sort*)) where
  coe: E -> α -> β
  inv: E -> β -> α
  leftInv: ∀e, Function.IsLeftInverse (inv e) (coe e)
  rightInv: ∀e, Function.IsRightInverse (inv e) (coe e)
  inj: ∀a b, coe a = coe b -> inv a = inv b -> a = b

namespace IsEquivLike

variable {E F α β γ : Sort*} [hE: IsEquivLike E α β] [hF: IsEquivLike F β γ]

def coe.inj : Function.Injective (IsEquivLike.coe: E -> _) := by
  intro x y h
  apply IsEquivLike.inj
  assumption
  exact Function.inverse_congr (IsEquivLike.leftInv x) (h ▸ IsEquivLike.rightInv y)

instance : FunLike E α β where
  coe := IsEquivLike.coe
  coe_inj := coe.inj

instance : IsEmbeddingLike E α β where
  coe_inj e := (leftInv e).Injective

@[symm]
def symm (h: IsEquivLike E α β) : IsEquivLike E β α where
  coe := h.inv
  inv := h.coe
  leftInv := h.rightInv
  rightInv := h.leftInv
  inj := fun _ _ a b => h.inj _ _ b a

def inv.inj : Function.Injective (IsEquivLike.inv: E -> _) := IsEquivLike.coe.inj (hE := hE.symm)

def Injective (e: E) : Function.Injective e := (leftInv e).Injective
def Surjective (e: E) : Function.Surjective e := (rightInv e).Surjective

end IsEquivLike
