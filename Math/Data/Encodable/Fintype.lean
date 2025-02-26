import Math.Data.Encodable.Basic
import Math.Data.Fintype.Defs

instance [f: Fintype α] [DecidableEq α] : Encodable α where
  encode a := f.idxOf a
  decode' x :=
    if h:x < f.card then
      .some f[x]
    else
      .none
  spec := by
    intro x
    dsimp
    erw [dif_pos, Fintype.getElem_idxOf]

namespace Encodable

section

variable {α : Type*} [Fintype α] [DecidableEq α] (p : α → Prop) [DecidablePred p] [h: Nonempty α]

def strongIndefiniteDescription : {x : α // (∃ y : α, p y) → p x} :=
  @dite _ (∃ x : α, p x) (inferInstance)
    (fun (hp : ∃ x : α, p x) =>
      show {x : α // (∃ y : α, p y) → p x} from
      let xp := indefiniteDescription hp;
      ⟨xp.val, fun _ => xp.property⟩)
    (fun hp => ⟨choice h, fun h => absurd h hp⟩)

-- a computable version of Hilbert's Epsilon function
def epsilon : α := strongIndefiniteDescription p
def epsilon_spec (h: ∃x, p x) : p (@epsilon _ _ _ p _ (nonempty_of_exists h)) := (@strongIndefiniteDescription _ _ _ p _ (nonempty_of_exists h)).property h

end

end Encodable
