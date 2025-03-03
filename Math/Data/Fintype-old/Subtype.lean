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

instance {α: Type _} {P Q: α -> Prop} [DecidableEq α] [fp: Fintype (Subtype P)] [fq: Fintype (Subtype Q)] : Fintype { x: α // P x ∨ Q x } where
  all :=
    have fp' : List (Subtype fun x => P x ∨ Q x) := fp.all.map (fun x => ⟨x.val, Or.inl x.property⟩)
    have fq' : List (Subtype fun x => P x ∨ Q x) := fq.all.map (fun x => ⟨x.val, Or.inr x.property⟩)
    fp' ++ fq'.filter (· ∉ fp')
  nodup := by
    dsimp
    apply List.nodup_append
    apply List.nodup_map
    intro ⟨x,_⟩ ⟨y, _⟩  eq
    cases eq
    rfl
    apply Fintype.nodup
    apply List.nodup_filter
    apply List.nodup_map
    intro ⟨x,_⟩ ⟨y, _⟩  eq
    cases eq
    rfl
    apply Fintype.nodup
    intro ⟨x, _⟩ memp memq
    replace ⟨_, memq⟩  := List.mem_filter.mp memq
    have := of_decide_eq_true memq
    contradiction
  complete := by
    intro ⟨x, hx⟩
    rcases hx with px | qx
    apply List.mem_append.mpr
    left
    apply List.mem_map.mpr
    exists ⟨x, px⟩
    apply And.intro
    apply Fintype.complete
    rfl
    dsimp
    if h:(Subtype.mk x (Or.inr qx)) ∈ fp.all.map (fun x => (⟨x.val, Or.inl x.property⟩: Subtype fun x => P x ∨ Q x)) then
      apply List.mem_append.mpr
      left; assumption
    else
      apply List.mem_append.mpr
      right
      apply List.mem_filter.mpr
      apply And.intro
      apply List.mem_map.mpr
      exists ⟨x, qx⟩
      apply And.intro
      apply Fintype.complete
      rfl
      apply decide_eq_true_iff.mpr
      assumption

instance {α: Type _} {P Q: α -> Prop} [DecidableEq α] [fp: Fintype (Subtype P)] [fq: Fintype (Subtype Q)] : Fintype { x: α // P x ∧ Q x } where
  all :=
    fp.all.filterMap fun x =>
      if h:∃q: Subtype Q, x.val = q.val then
        .some ⟨x.val, by
          obtain ⟨⟨y, qy⟩, h⟩ := h
          apply And.intro x.property
          rw [h]
          assumption⟩
      else
        .none
  nodup := by
    dsimp
    apply List.nodup_filterMap
    apply Fintype.nodup
    intro ⟨x, xprop⟩ ⟨y, yprop⟩  hx eq
    split at eq <;> rename_i hx'
    <;> split at eq <;> rename_i hy'
    obtain ⟨x', _⟩ := hx'
    cases eq
    rfl
    contradiction
    contradiction
    rw [dif_neg hx'] at hx
    contradiction
  complete := by
    intro ⟨x, px, qx⟩
    apply List.mem_filterMap.mpr
    exists ⟨x, px⟩
    apply And.intro
    apply Fintype.complete
    rw [dif_pos]
    exists ⟨x, qx⟩

instance {α: Type _} {P Q: α -> Prop} [DecidablePred Q] [fp: Fintype (Subtype P)] : Fintype { x: α // P x ∧ Q x } where
  all := fp.all.filterMap fun x: Subtype P => if h:Q x then .some ⟨x, x.property, h⟩ else .none
  nodup := by
    apply List.nodup_filterMap
    apply Fintype.nodup
    intro ⟨x, xprop⟩ ⟨y, yprop⟩  hx eq
    split at eq <;> rename_i hx'
    <;> split at eq <;> rename_i hy'
    cases eq
    rfl
    contradiction
    contradiction
    rw [dif_neg hx'] at hx
    contradiction
  complete := by
    intro ⟨x, px, qx⟩
    apply List.mem_filterMap.mpr
    exists ⟨x, px⟩
    apply And.intro
    apply Fintype.complete
    rw [dif_pos]
    assumption
