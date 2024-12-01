import Math.Function.Basic
import Math.Data.Like.Func
import Math.Type.Notation

class IsEmbeddingLike (F: Sort*) (α β: outParam (Sort*)) [FunLike F α β]: Prop where
  coe_inj: ∀f: F, Function.Injective (DFunLike.coe f)

namespace IsEmbeddingLike

variable {F α β γ : Sort*} [FunLike F α β] [i : IsEmbeddingLike F α β]

def Injective (f : F) : Function.Injective f :=
  coe_inj f

def apply_eq_iff_eq (f : F) {x y : α} : f x = f y ↔ x = y := (IsEmbeddingLike.Injective f).eq_iff

def comp_injective {F : Sort*} [FunLike F β γ] [IsEmbeddingLike F β γ] (f : α → β) (e : F) :
    Function.Injective (e ∘ f) ↔ Function.Injective f :=
  (IsEmbeddingLike.Injective e).of_comp_iff f

end IsEmbeddingLike
