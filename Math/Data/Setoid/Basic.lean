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

def trueSetoid (α: Sort _) : Setoid α where
  r := Relation.trivial
  iseqv := Relation.equiv _

end Setoid
