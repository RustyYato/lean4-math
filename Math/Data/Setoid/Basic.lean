import Math.Relation.Basic

namespace Setoid

-- relates two elements if they evaluate to the same value
def kernel (f: α -> β) : Setoid α where
  r a b := f a = f b
  iseqv := {
    refl _ := rfl
    symm := Eq.symm
    trans := Eq.trans
  }

def forallSetoid {ι: Sort _} (α: ι -> Sort _) [∀i: ι, Setoid (α i)] : Setoid (∀i, α i) where
  r f g:= ∀i, f i ≈ g i
  iseqv := {
    refl x _ := by rfl
    symm h i := Relation.symm (h i)
    trans h g i := trans (h i) (g i)
  }

def trueSetoid (α: Sort _) : Setoid α where
  r := Relation.trivial
  iseqv := Relation.equiv _

def subtypeSetoid (P: α -> Prop) [Setoid α] : Setoid (Subtype P) where
  r a b := a.val ≈ b.val
  iseqv := {
    refl _ := Relation.refl _
    symm := Relation.symm
    trans := Relation.trans'
  }

end Setoid

def Quotient.apply
  {α: ι -> Sort u}
  {s: ∀i, Setoid (α i)}
  (Q: Quotient (Setoid.forallSetoid α))
  (i: ι) : Quotient (s i) := by
  apply Q.lift (fun f => Quotient.mk _ (f i))
  intro f g eqv
  apply Quotient.sound
  apply eqv
