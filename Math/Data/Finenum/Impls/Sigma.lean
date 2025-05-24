import Math.Data.Finenum.Defs

namespace Finenum

variable {α: ι -> Type*} [fι: Finenum ι] [fα: ∀i, Finenum (α i)]

def fin_sum (f: Fin n -> ℕ) : ℕ :=
  Fin.foldr n (fun x acc => acc + f x) 0

private def card_sigma' (rι: Repr cardι ι) := fin_sum fun x: Fin cardι => card (α (rι.decode x))

instance {α: ι -> Type*} [fι: Finenum ι] [fα: ∀i, Finenum (α i)] : Finenum (Σi, α i) :=
  fι.toRepr.recOnSubsingleton fun rι => {
    card_thunk := Thunk.mk fun _ => (card_sigma' rι (α := α))
    toRepr := sorry
  }

end Finenum
