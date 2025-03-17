import Math.Order.Linear
import Math.Order.TopBot

instance [LE α] [LT α] [IsLinearOrder α] : IsLinearOrder (WithTop α) :=
  inferInstance
instance [LE α] [LT α] [IsLinearOrder α] : IsLinearOrder (WithBot α) :=
  inferInstance

instance [LE α] [LT α] [Min α] [Max α] [IsLinearMinMaxOrder α] : IsLinearMinMaxOrder (WithBot α) where
  min_iff_le_left := by
    intro a b
    cases a <;> cases b <;> simp [min]
    apply bot_le
    exact nofun
    rw [WithBot.of_inj, ←min_iff_le_left]
  min_iff_le_right := by
    intro a b
    cases a <;> cases b <;> simp [min]
    exact nofun
    apply bot_le
    rw [WithBot.of_inj, ←min_iff_le_right]
  max_iff_le_left := by
    intro a b
    cases a <;> cases b <;> simp [max]
    rfl
    apply bot_le
    exact nofun
    rw [WithBot.of_inj, ←max_iff_le_left]
  max_iff_le_right := by
    intro a b
    cases a <;> cases b <;> simp [max]
    rfl
    exact nofun
    apply bot_le
    rw [WithBot.of_inj, ←max_iff_le_right]

instance [LE α] [LT α] [Min α] [Max α] [IsLinearMinMaxOrder α] : IsLinearMinMaxOrder (WithTop α) where
  min_iff_le_left := by
    intro a b
    cases a <;> cases b <;> simp [min]
    rfl
    exact nofun
    apply le_top
    rw [WithBot.of_inj, ←min_iff_le_left]
  min_iff_le_right := by
    intro a b
    cases a <;> cases b <;> simp [min]
    rfl
    apply le_top
    exact nofun
    rw [WithBot.of_inj, ←min_iff_le_right]
  max_iff_le_left := by
    intro a b
    cases a <;> cases b <;> simp [max]
    exact nofun
    apply le_top
    rw [WithBot.of_inj, ←max_iff_le_left]
  max_iff_le_right := by
    intro a b
    cases a <;> cases b <;> simp [max]
    apply le_top
    exact nofun
    rw [WithBot.of_inj, ←max_iff_le_right]
