import Math.Data.Fintype.Array

instance List.VectorFintype [f: Fintype α] : Fintype { x: List α // x.length = n } := by
  apply Fintype.ofEquiv' (Subtype.congrEquiv Array.equivList (P := fun x => x.size = n) (Q := fun x => x.length = n) _)
  intro ⟨as⟩
  rfl

def List.card (f: Fintype α) : Fintype.card { x: List α // x.length = n } = f.card ^ n := by
  show (Fintype.ofEquiv' _).card = _
  rw [Fintype.ofEquiv'_card_eq]
  exact Array.card _
