import Math.Data.List.Defs
import Math.Data.Fintype.Defs

def Fintype.ofArray (as: Array α) (nodup: as.toList.Nodup) (h: ∀x, x ∈ as) : Fintype α where
  card_thunk := as.size
  toRepr := Trunc.mk (α := Fintype.Repr as.size _) {
    encode := Thunk.mk fun _ => none
    decode := {
      toFun i := as[i]
      inj' := by
        intro a b g
        simp at g
        exact List.nodup_iff_getElem_inj.mp nodup g
      surj' := by
        intro x
        dsimp
        have ⟨i, h, hi⟩ := List.getElem_of_mem (Array.mem_toList.mpr (h x))
        exists ⟨i, h⟩
        rw [←hi]
        rfl
    }
  }
