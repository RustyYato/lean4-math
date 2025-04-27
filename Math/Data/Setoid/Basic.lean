import Math.Relation.Defs

namespace Setoid

-- relates two elements if they evaluate to the same value
def kernel (f: α -> β) : Setoid α where
  r a b := f a = f b
  iseqv := {
    refl _ := rfl
    symm := Eq.symm
    trans := Eq.trans
  }

def comap (f: α -> β) (s: Setoid β) : Setoid α where
  r a b := s.r (f a) (f b)
  iseqv := {
    refl _ := s.iseqv.refl _
    symm := s.iseqv.symm
    trans := s.iseqv.trans
  }

def forallSetoid {ι: Sort _} (α: ι -> Sort _) [∀i: ι, Setoid (α i)] : Setoid (∀i, α i) where
  r f g:= ∀i, f i ≈ g i
  iseqv := {
    refl x _ := by rfl
    symm h i := Relation.symm (h i)
    trans h g i := trans (h i) (g i)
  }

def forallsetoid_eval {ι: Sort _} {α: ι -> Sort _} [S: ∀i: ι, Setoid (α i)] : Quotient (forallSetoid α) -> ∀i, Quotient (S i) := by
  intro q i; revert q
  refine Quotient.lift ?_ ?_
  intro f; exact Quotient.mk _ (f i)
  intro a b h
  apply Quotient.sound
  apply h


def forallsetoid_ext {ι: Sort _} (α: ι -> Sort _) [∀i: ι, Setoid (α i)] (a b: Quotient (forallSetoid α)) :
  (∀i, forallsetoid_eval a i = forallsetoid_eval b i) -> a = b := by
  intro h
  induction a using Quotient.ind with | _ a =>
  induction b using Quotient.ind with | _ b =>
  apply Quotient.sound
  intro i
  exact Quotient.exact (h i)

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

def eqSetoid : Setoid α where
  r a b := a = b
  iseqv := Relation.equiv _

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
