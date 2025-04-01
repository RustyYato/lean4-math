-- import Math.Data.CauchySeq.Basic

-- namespace CauchySeq

-- variable {α: Type*} {γ: Type*} [AbsoluteValue α α]
--   [FieldOps α] [LT α] [LE α] [Min α] [Max α]
--   [IsField α] [IsLinearLattice α] [IsOrderedRing α]
--   [IsOrderedAbsAddGroup α] [IsOrderedAddCommMonoid α]

-- def IsPos (c: CauchySeq α) : Prop := ∃B: α, B > 0 ∧ Eventually fun n => B < c n

-- def notLimZero (c: CauchySeq α) (h: c.IsPos) (g: c.IsLimZero) : False := by
--   obtain ⟨B, Bpos, k, pos⟩ := h
--   replace ⟨k', g⟩ := g |B| ?_
--   have := g (max k k') (le_max_right _ _)
--   have := pos (max k k') (le_max_left _ _)
--   dsimp at this
--   repeat sorry

-- end CauchySeq
