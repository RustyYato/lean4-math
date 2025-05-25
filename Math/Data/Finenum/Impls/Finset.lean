import Math.Data.Finset.Basic
import Math.Data.Finenum.Defs

instance (f: Finset α) : Finenum f :=
  {
    card_thunk := f.val.length
    toRepr := f.recOnSubsingleton (motive := fun f => Trunc (Finenum.Repr f.val.length _)) fun l h =>
      Trunc.mk (α := Finenum.Repr l.length _) {
        encode := .none
        decode x := {
          val := l[x]'x.isLt
          property := List.getElem_mem x.isLt
        }
        bij := by
          apply And.intro
          · intro x y g
            dsimp at g
            rw [←Fin.val_inj]
            exact l.nodup_getElem_inj h (Subtype.mk.inj g)
          · intro ⟨x, hx⟩
            have ⟨i, h, _⟩ := List.getElem_of_mem hx
            exists ⟨i, h⟩
            congr; symm; assumption
      }
  }
