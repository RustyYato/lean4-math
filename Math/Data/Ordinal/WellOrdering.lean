import Math.Data.Ordinal.Basic


namespace WellOrdering

open Classical

private noncomputable def to_ord_func (α: Type u) (o: Ordinal.{u}) : Option α :=
  let f: ∀s: Set α, s.Nonempty -> α := fun _ h => Classical.choose h
  -- the set of all values that have already been assigned to smaller ordinals
  let assigned := Set.mk fun x => ∃o', ∃_: o' < o, to_ord_func α o' = .some x
  -- if there is a value that hasn't yet been assigned, assign it
  if h:(assignedᶜ).Nonempty then .some (f _ h) else .none
termination_by o

private def set_of_lt (α: Type _) (a: Ordinal): Set α :=
  (Set.mk fun x => ∃o', ∃_: o' < a, to_ord_func α o' = .some x)

private
def to_ord_func_inj : ∀x y, to_ord_func α x = to_ord_func α y -> (to_ord_func α x).isSome -> x = y := by
  intro a b eq ha
  have hb : (to_ord_func α b).isSome := by
    rw [←eq]
    assumption
  unfold to_ord_func at eq ha hb
  dsimp at eq ha hb
  replace eq : (if h:((set_of_lt α a)ᶜ).Nonempty then _ else _) =
    (if h:((set_of_lt α b)ᶜ).Nonempty then _ else _) := eq
  replace ha : Option.isSome (if h:((set_of_lt α a)ᶜ).Nonempty then _ else _) := ha
  replace hb : Option.isSome (if h:((set_of_lt α b)ᶜ).Nonempty then _ else _) := hb

  have ha' : ((set_of_lt α a)ᶜ).Nonempty := by
    apply Classical.byContradiction
    intro h
    rw [dif_neg h] at ha
    contradiction
  have hb' : ((set_of_lt α b)ᶜ).Nonempty := by
    apply Classical.byContradiction
    intro h
    rw [dif_neg h] at hb
    contradiction

  rw [dif_pos ha', dif_pos hb'] at eq
  replace eq := Option.some.inj eq
  have ha'': choose ha' ∉ set_of_lt α a := Classical.choose_spec ha'
  have hb'': choose hb' ∉ set_of_lt α b := Classical.choose_spec hb'
  replace ha'' := fun x => not_exists.mp (not_exists.mp ha'' x)
  replace hb'' := fun x => not_exists.mp (not_exists.mp hb'' x)
  apply Relation.eq_of_not_lt_or_gt (α := Ordinal) (· < ·)
  · intro ab
    apply hb'' _ ab
    unfold to_ord_func
    dsimp
    show (if h : ((set_of_lt α a)ᶜ).Nonempty then Option.some (choose h) else Option.none) = _
    rw [dif_pos ha']
    congr
  · conv at hb'' => { intro; intro; rw [←eq] }
    intro ba
    apply ha'' _ ba
    unfold to_ord_func
    dsimp
    show (if h : ((set_of_lt α b)ᶜ).Nonempty then Option.some (choose h) else Option.none) = _
    rw [dif_pos hb', eq]

noncomputable
def to_ord_func_bool₀ (o: Ordinal.{0}) : Option Bool :=
  if o = 0 then false
  else if o = 1 then true
  else .none

noncomputable
def to_ord_func_bool₁ (o: Ordinal.{0}) : Option Bool :=
  if o = 0 then true
  else if o = 1 then false
  else .none

example : to_ord_func Bool = to_ord_func_bool₀ ∨ to_ord_func Bool = to_ord_func_bool₁ := by
  cases h:to_ord_func Bool 0
  unfold to_ord_func at h
  dsimp at h
  split at h
  contradiction
  rename_i g
  have := fun x => Classical.not_not.mp ((not_exists.mp g) x)
  have ⟨of, lt₀, eq₀⟩ := this false
  have := Ordinal.not_lt_zero _ lt₀
  contradiction
  rename_i b
  cases b
  · left
    have g : to_ord_func Bool 1 = some true := by
      unfold to_ord_func
      dsimp
      have : (set_of_lt Bool 1)ᶜ = {true} := sorry
      rw [←set_of_lt, this]
      have : Set.Nonempty {true} := ⟨_, Set.mem_singleton.mpr rfl⟩
      rw [dif_pos this]
      congr
      exact Set.mem_singleton.mp (Classical.choose_spec this)
    apply funext
    intro x
    unfold to_ord_func_bool₀
    split; subst x
    assumption
    split; subst x
    assumption
    unfold to_ord_func
    dsimp
    rw [dif_neg]
    intro ⟨x, eq⟩
    apply eq; clear eq
    cases x
    exists 0
    refine ⟨?_, h⟩
    apply lt_of_le_of_ne
    -- apply le_of_lt_succ
    repeat sorry
  sorry

private
def to_ord_func_surj {α: Type u} : ∀a: α, ∃o: Ordinal.{u}, a = to_ord_func α o := by
  intro a
  let s := Set.mk fun o: Ordinal => a ∈ set_of_lt α o
  let x := Ordinal.sSup_lift s
  by_cases h:∃y: Ordinal, x = Ordinal.lift.{u, u+1} y
  sorry
  · rw [not_exists] at h
    have : x = Ordinal.ord.{u} := by

      sorry
    sorry

  -- apply Classical.byContradiction
  -- rw [not_exists]
  -- intro h
  -- have : ∀x: Ordinal, (set_of_lt α x)ᶜ.Nonempty := by
  --   intro x
  --   exists a
  --   intro ⟨_, _, g⟩
  --   exact h _ g.symm
  -- unfold to_ord_func at h
  -- dsimp at h
  -- replace h : ∀x, a ≠ choose (this x) := by
  --   intro x
  --   have := h x
  --   rw [dif_pos] at this
  --   intro h
  --   apply this
  --   congr
  --   sorry
  -- sorry

def order {α: Type u} (a b: α) : Prop :=
  ∃oa ob: Ordinal.{u}, to_ord_func α oa = a ∧ to_ord_func α ob = b ∧ oa < ob

noncomputable
def order_embed_ord {α: Type u} : order (α := α) ↪r (· < (·: Ordinal.{u})) where
  toFun x := Classical.choose (to_ord_func_surj x)
  inj := by
    intro x y eq
    dsimp at eq
    have hx := Classical.choose_spec (to_ord_func_surj x)
    have hy := Classical.choose_spec (to_ord_func_surj y)
    rw [←eq] at hy
    exact Option.some.inj (hx.trans hy.symm)
  resp_rel := by
    intro a b
    apply Iff.intro
    intro ⟨oa, ob, oa_spec, ob_spec, oa_lt_ob⟩
    dsimp
    have ha := Classical.choose_spec (to_ord_func_surj a)
    have hb := Classical.choose_spec (to_ord_func_surj b)
    have := to_ord_func_inj _ _ (oa_spec.trans ha) (by rw [oa_spec]; rfl)
    rw [←this]
    have := to_ord_func_inj _ _ (ob_spec.trans hb) (by rw [ob_spec]; rfl)
    rw [←this]
    assumption
    dsimp
    intro h
    refine ⟨_, _, ?_, ?_, h⟩
    symm; apply Classical.choose_spec (to_ord_func_surj a)
    symm; apply Classical.choose_spec (to_ord_func_surj b)

instance : Relation.IsWellOrder (order (α := α)) :=
  order_embed_ord.wo

end WellOrdering
