import Math.Data.Fintype.Defs

instance {P: α -> Prop} [dec: DecidablePred P] [fa: Fintype α] : Fintype { x: α // P x } where
  all := fa.all.filterMap fun x =>
    match dec x with
    | .isTrue h => .some ⟨x, h⟩
    | .isFalse h => .none
  nodup := by
    apply List.nodup_filterMap
    apply Fintype.nodup
    intro x y hx hy
    split at hx <;> rename_i px h
    clear hx
    rw [h] at hy
    dsimp at hy
    split at hy
    cases hy
    rfl
    contradiction
    contradiction
  complete := by
    intro ⟨x, px⟩
    apply List.mem_filterMap.mpr
    refine ⟨x, ?_⟩
    apply And.intro
    apply Fintype.complete
    split
    rfl
    contradiction
