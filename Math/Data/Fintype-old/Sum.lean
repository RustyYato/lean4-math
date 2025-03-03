import Math.Data.Fintype.Defs

instance [as: Fintype α] [bs: Fintype β] : Fintype (α ⊕ β) where
  all := as.all.map .inl ++ bs.all.map .inr
  complete := by
    intro x
    apply List.mem_append.mpr
    cases x
    left
    apply List.mem_map.mpr
    refine ⟨_, ?_, rfl⟩
    apply as.complete
    right
    apply List.mem_map.mpr
    refine ⟨_, ?_, rfl⟩
    apply bs.complete
  nodup := by
    apply List.nodup_append
    apply List.nodup_map
    apply Sum.inl.inj
    exact as.nodup
    apply List.nodup_map
    apply Sum.inr.inj
    exact bs.nodup
    intro x  meml memr
    have ⟨a, _, aeq⟩  := List.mem_map.mp meml
    have ⟨b, _, beq⟩  := List.mem_map.mp memr
    have := aeq.trans beq.symm
    contradiction

def Sum.fintypeLeft (f: Fintype (α ⊕ β)) : Fintype α where
  all := f.all.filterMap fun
    | .inl a => .some a
    | .inr _ => .none
  complete := by
    intro x
    apply List.mem_filterMap.mpr
    exists .inl x
    apply And.intro
    apply Fintype.complete
    rfl
  nodup := by
    apply List.nodup_filterMap
    apply Fintype.nodup
    intro x y
    cases x <;> cases  y <;> dsimp
    intro _ h
    cases h; rfl
    all_goals
      intros
      contradiction

def Sum.fintypeRight (f: Fintype (α ⊕ β)) : Fintype β where
  all := f.all.filterMap fun
    | .inr a => .some a
    | .inl _ => .none
  complete := by
    intro x
    apply List.mem_filterMap.mpr
    exists .inr x
    apply And.intro
    apply Fintype.complete
    rfl
  nodup := by
    apply List.nodup_filterMap
    apply Fintype.nodup
    intro x y
    cases x <;> cases  y <;> dsimp
    any_goals
      intro _ h
      cases h; rfl
    all_goals
      intros
      contradiction

def Sum.card_eq (as: Fintype α) (bs: Fintype β) : Fintype.card (α ⊕ β) = Fintype.card α + Fintype.card β := by
  rw [Fintype.card_eq (α := α ⊕ β)]
  show (_ ++ _: List _).length = _
  rw [List.length_append, List.length_map, List.length_map]
  rfl
