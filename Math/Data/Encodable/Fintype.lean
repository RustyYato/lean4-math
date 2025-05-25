import Math.Data.Encodable.Basic
import Math.Data.Fintype.Defs

def Fintype.toEncodable (α: Type*) [f: Fintype α] [DecidableEq α] : Trunc (Encodable α) :=
  f.toEquiv.map fun eqv =>
  let c := Fintype.card α
  {
    encode a := eqv.symm a
    decode' i :=  if h:i < c then eqv ⟨i, h⟩ else .none
    spec x := by
      rw [dif_pos]
      simp
      apply Fin.isLt
  }

namespace Encodable

section

variable {α : Type*} [Fintype α] [DecidableEq α] (p : α → Prop) [DecidablePred p] [h: Nonempty α]

-- a computable version of Hilbert's Epsilon function for fintypes, but wrapped in trunc
-- since Fintype is subsingleton, we can't just choose an ordering
def strongIndefiniteDescription : Trunc {x : α // (∃ y : α, p y) → p x} :=
  (Fintype.toEncodable α).map fun enc =>
    @dite _ (∃ x : α, p x) (inferInstance)
      (fun (hp : ∃ x : α, p x) =>
        show {x : α // (∃ y : α, p y) → p x} from
        let xp := @indefiniteDescription α enc _ _ hp;
        ⟨xp.val, fun _ => xp.property⟩)
      (fun hp => ⟨@choice α enc h, fun h => absurd h hp⟩)

-- a computable version of Hilbert's Epsilon function
-- def epsilon : α := strongIndefiniteDescription p
-- def epsilon_spec (h: ∃x, p x) : p (@epsilon _ _ _ p _ (nonempty_of_exists h)) := (@strongIndefiniteDescription _ _ _ p _ (nonempty_of_exists h)).property h

end

end Encodable
