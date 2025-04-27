import Math.Data.Ordinal.Basic

namespace Ordinal

def add_zero (o: Ordinal) : o + 0 = o := by
  cases o with | mk o =>
  apply sound
  symm
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  exact .inl
  intro x
  match x with
  | .inl x => exact x
  | .inr x => exact (elim_empty x: False).elim
  intro; rfl
  intro x
  cases x
  rfl
  dsimp
  contradiction
  dsimp
  intro x y
  apply Iff.intro
  apply Sum.Lex.inl
  intro h
  cases h
  assumption

def zero_add (o: Ordinal) : 0 + o = o := by
  cases o with | mk o =>
  apply sound
  symm
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  exact .inr
  intro x
  match x with
  | .inr x => exact x
  | .inl x => exact (elim_empty x: False).elim
  intro; rfl
  intro x
  cases x
  dsimp
  contradiction
  rfl
  dsimp
  intro x y
  apply Iff.intro
  apply Sum.Lex.inr
  intro h
  cases h
  assumption

def add_succ (a b: Ordinal) : a + (b + 1) = (a + b) + 1 := by
  rw [one_eq]
  induction a, b using ind₂ with | mk a b =>
  apply sound
  unfold Pre.add Pre.one
  dsimp
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  intro x
  match x with
  | .inl x => exact .inl (.inl x)
  | .inr (.inl x) => exact .inl (.inr x)
  | .inr (.inr x) => exact .inr x
  intro x
  match x with
  | .inl (.inl x) => exact .inl x
  | .inl (.inr x) => exact .inr (.inl x)
  | .inr x => exact .inr (.inr x)
  intro x
  rcases x with x | x
  rfl
  rcases x with x | x
  rfl
  rfl
  intro x
  rcases x with x | x
  rcases x with x | x
  rfl
  rfl
  rfl
  intro x y
  dsimp
  rcases x with x | x | x <;> rcases y with y | y | y
  all_goals
    dsimp
    apply Iff.intro <;> intro h
  any_goals cases h
  any_goals apply Sum.Lex.sep
  any_goals apply Sum.Lex.inl
  any_goals apply Sum.Lex.inr
  any_goals apply Sum.Lex.sep
  any_goals apply Sum.Lex.inl
  any_goals apply Sum.Lex.inr
  any_goals assumption
  all_goals
    rename_i h
    cases h
    try assumption

def add_lt_add_left (k a b: Ordinal) : a < b -> k + a < k + b := by
  induction a, b, k using ind₃ with | mk a b k =>
  intro ⟨h⟩
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
  intro x
  match x with
  | .inl x => exact .inl x
  | .inr x => exact .inr (h x)
  intro x y eq
  cases x <;> cases y <;> dsimp at eq
  cases eq; rfl
  contradiction
  contradiction
  rw [h.inj (Sum.inr.inj eq)]
  intro x y
  · cases x <;> cases y
    all_goals
      apply Iff.intro <;> intro h
    any_goals contradiction
    any_goals apply Sum.Lex.inl
    any_goals apply Sum.Lex.inr
    any_goals apply Sum.Lex.sep
    all_goals cases h
    assumption
    assumption
    apply h.resp_rel.mp; assumption
    apply h.resp_rel.mpr; assumption
  have ⟨top, spec⟩ := h.exists_top
  exists .inr top
  intro x
  rw [Set.mem_range]
  cases x
  all_goals
      apply Iff.intro <;> intro h
  rename_i x
  exists .inl x
  apply Sum.Lex.sep
  rename_i x
  cases h; rename_i h
  have ⟨a₀, mem⟩ := Set.mem_range.mp <| (spec _).mp h
  subst x
  exists .inr a₀
  obtain ⟨x, eq⟩ := h
  rw [eq]
  cases x
  apply Sum.Lex.sep
  apply Sum.Lex.inr
  apply (spec _).mpr
  apply Set.mem_range'

def succ_lt_limit_of_lt (a b: Ordinal) (alim: a.IsLimitOrdinal) : b < a -> b + 1 < a := by
  intro xj
  apply lt_of_le_of_ne
  apply succ_le_of_lt
  assumption
  apply alim

def limit_iff_le (a b: Ordinal) (alim: a.IsLimitOrdinal) : a ≤ b ↔ ∀a' < a, a' ≤ b := by
  apply Iff.intro
  · intro h
    intro k  k_lt_a
    apply le_trans
    apply le_of_lt
    assumption
    assumption
  · intro h
    apply le_of_not_lt
    intro g
    have := h _ (succ_lt_limit_of_lt _ _ alim g)
    have := not_le_of_lt (lt_succ_self b)
    contradiction

def limit_eq_max (a: Ordinal) (lim: a.IsLimitOrdinal) : a = ⨆x: a, x.val := by
  have : (Set.range fun x: a => x.val).BoundedAbove := by
    exists a
    intro x mem
    rw [Set.mem_range] at mem
    obtain ⟨x, eq⟩ := mem; subst eq
    apply le_of_lt
    apply x.property
  apply le_antisymm
  apply (limit_iff_le _ _ lim).mpr
  intro a' h
  apply le_sSup
  assumption
  rw [Set.mem_range]
  exists ⟨a', h⟩
  apply sSup_le
  assumption
  intro x mem
  rw [Set.mem_range] at mem
  obtain ⟨x, eq⟩ := mem; subst eq
  apply le_of_lt
  apply x.property

def ofNat_add_ofNat' (n m: Nat) : ((Pre.ofNat n).add (Pre.ofNat m)).rel ≃r (Pre.ofNat (m + n)).rel where
  toFun
  | .inl x => x.castLE (Nat.le_add_left _ _)
  | .inr x => x.addNat n
  invFun x := if h:x.val < n then .inl ⟨x.val, h⟩ else .inr (x.subNat n (le_of_not_lt h))
  leftInv := by
    intro x
    cases x <;> dsimp
    rw [dif_pos]
    apply Fin.isLt
    rw [dif_neg]
    rw [Fin.subNat_addNat]
    apply not_lt_of_le
    apply Nat.le_add_left
  rightInv := by
    intro x
    dsimp
    by_cases h:x.val < n
    rw [dif_pos h]
    rfl
    rw [dif_neg h]
    dsimp
    rw [Fin.addNat_subNat]
  resp_rel := by
    intro a b
    dsimp
    apply Iff.intro
    · intro h
      cases h
      assumption
      apply Nat.add_lt_add_right
      assumption
      dsimp
      rename_i a b
      show a.val < b.val + n
      apply Nat.lt_of_lt_of_le a.isLt
      apply Nat.le_add_left
    · cases a <;> cases b <;> rename_i a b
      all_goals
        dsimp
        intro h
      apply Sum.Lex.inl
      assumption
      apply Sum.Lex.sep
      · replace h : a.val + n < b.val := h
        have g : b.val < a.val + n := by
          apply Nat.lt_of_lt_of_le b.isLt
          apply Nat.le_add_left
        have := lt_asymm h g
        contradiction
      apply Sum.Lex.inr
      apply Nat.lt_of_add_lt_add_right
      assumption

def ofNat_add_ofNat (n m: Nat) : ofNat n + ofNat m = ofNat (n + m) := by
  apply sound
  rw [Nat.add_comm]
  apply ofNat_add_ofNat'

def natCast_add_natCast (n m: Nat) : (n + m: Ordinal) = ((n + m: Nat): Ordinal) := by
  apply sound
  unfold Pre.lift
  apply RelIso.trans
  apply Pre.add.spec
  dsimp; apply (ULift.relIso _)
  dsimp; apply (ULift.relIso _)
  dsimp; apply RelIso.trans _ (ULift.relIso _).symm
  rw [Nat.add_comm]
  apply ofNat_add_ofNat'

def omega_first_limit :
  ∀x > 0, x.IsLimitOrdinal -> ω ≤ x := by
  intro x x_pos x_limit
  apply le_of_not_lt
  intro h
  have ⟨n, eq⟩ := lt_omega _ h
  subst x
  clear h
  replace x_pos := (natCast_lt_natCast _ _).mp x_pos
  match n with
  | n + 1 =>
  apply x_limit n
  rw [←natCast_add_natCast]
  rfl

def Pre.non_zero_limit_is_infinite (p: Pre) (lim: ⟦p⟧.IsLimitOrdinal) :
  ∀x, ∃y, p.rel x y := by
  apply Classical.byContradiction
  conv => {
    rw [Classical.not_forall]; arg 1; arg 1; intro; rw [not_exists]
  }
  intro ⟨max, spec⟩
  apply lim (Ordinal.typein p.rel max)
  rw [add_one_eq_succ]
  apply sound
  refine ⟨⟨?_, ?_, ?_, ?_⟩ , ?_⟩
  intro x
  match x with
  | .some x => exact x.val
  | .none => exact max
  intro x
  if h:p.rel x max then
    exact .some ⟨x, h⟩
  else
    exact .none
  intro x
  cases x
  dsimp
  rw [dif_neg (spec _)]
  rename_i x
  dsimp
  rw [dif_pos x.property]
  rfl
  intro x
  dsimp
  by_cases h:p.rel x max
  rw [dif_pos h]
  rw [dif_neg h]
  dsimp
  have := spec x
  rcases Relation.connected p.rel max x with lt | eq | gt
  contradiction
  assumption
  contradiction
  intro x y
  cases x <;> cases y
  all_goals
    apply Iff.intro <;> intro r
  contradiction
  have := spec _ r
  contradiction
  dsimp
  contradiction
  rename_i x
  have := spec _ r
  contradiction
  dsimp
  rename_i x
  exact x.property
  apply Pre.succRel.none
  dsimp
  cases r
  assumption
  apply Pre.succRel.some
  assumption

def add_is_limit (a b: Ordinal) (blim: b.IsLimitOrdinal) (bpos: 0 < b) : (a + b).IsLimitOrdinal := by
  intro x
  rw [add_one_eq_succ]
  induction a, b, x using ind₃ with | mk A B X =>
  intro h
  replace ⟨h⟩ := Quotient.exact h
  have : ∀x, x ≠ h .none -> (A.add B).rel x (h .none) := by
    intro x g
    apply h.symm.resp_rel.mpr
    show X.succ.rel (h.symm _) (h.symm _)
    rw [h.coe_symm]
    have : h.symm x ≠ .none := by
      intro g'
      apply g
      rw [←g', h.symm_coe]
    cases h':h.symm x
    rw [h'] at this; contradiction
    apply Pre.succRel.none
  rw [zero_eq] at bpos
  match h₀:h .none with
  | .inl _ =>
    obtain ⟨bpos⟩ := bpos
    obtain ⟨max, _⟩ := bpos.exists_top
    rw [h₀] at this
    have := this (.inr max) Sum.noConfusion
    contradiction
  | .inr b =>
    rw [h₀] at this; clear h₀
    have ⟨b', b_lt_b'⟩ := Pre.non_zero_limit_is_infinite _ blim b
    have := this (.inr b') (fun eq => Relation.irrefl <| Sum.inr.inj eq ▸ b_lt_b')
    cases this
    have := Relation.asymm b_lt_b'
    contradiction

-- def add_le_of_limit (a b k: Ordinal) (blim: b.IsLimitOrdinal) (bpos: 0 < b) : a + b ≤ k ↔ ∀b' < b, a + b' ≤ k := by
--   induction a, b, k using ind₃ with | mk A B K =>
--   rw [zero_eq] at bpos
--   obtain ⟨bpos⟩ := bpos
--   apply Iff.intro
--   · intro ⟨h⟩ b'
--     cases b' with | mk B' =>
--     intro ⟨g⟩
--     refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
--     · intro x
--       apply fun x => h x
--       match x with
--       | .inl x => exact (.inl x)
--       | .inr x => exact (.inr (g x))
--     · apply Function.Injective.comp
--       apply h.inj
--       intro x y
--       cases x <;> cases y
--         <;> dsimp <;> intro h
--       cases h; rfl
--       contradiction
--       contradiction
--       rw [g.inj (Sum.inr.inj h)]
--     · intro x y
--       cases x <;> cases y <;>
--         apply Iff.intro <;> intro g₀
--       cases g₀
--       dsimp
--       apply h.resp_rel.mp
--       apply Sum.Lex.inl
--       assumption
--       replace g := h.resp_rel.mpr g₀
--       apply Sum.Lex.inl
--       cases g; assumption
--       apply h.resp_rel.mp
--       apply Sum.Lex.sep
--       apply Sum.Lex.sep
--       contradiction
--       replace g := h.resp_rel.mpr g₀
--       contradiction
--       apply h.resp_rel.mp
--       apply Sum.Lex.inr
--       apply g.resp_rel.mp
--       cases g₀
--       assumption
--       replace g₀ := h.resp_rel.mpr g₀
--       cases g₀; rename_i g₀
--       replace g₀ := g.resp_rel.mpr g₀
--       apply Sum.Lex.inr
--       assumption
--     · intro x k r
--       have ⟨x', eq⟩ := Set.mem_range.mp <| h.isInitial _ _ r
--       subst eq
--       replace r := h.resp_rel.mpr r
--       apply Set.mem_range.mpr
--       cases x <;> dsimp at r
--       cases r
--       rename_i x _
--       exists .inl x
--       cases r with
--       | sep =>
--         rename_i x
--         exists .inl x
--       | inr h =>
--         rename_i x _
--         have ⟨b₀, eq⟩ := Set.mem_range.mp <| g.init _ _ h
--         subst eq
--         exists .inr b₀
--   · intro h
--     refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
--     · intro x
--       sorry
--     · sorry
--     · sorry
--     · sorry

-- def add_limit (a b: Ordinal) (h: b.IsLimitOrdinal) : a + b = iSup fun x: b => a + x.val := by
--   apply le_antisymm
--   apply le_sSup'
--   exists a + b
--   intro x hx
--   have ⟨⟨x, x_lt_b⟩, eq⟩ := Set.mem_range.mp hx
--   subst eq; clear hx
--   dsimp
--   apply le_of_lt
--   apply add_lt_add_left
--   assumption
--   intro x mem
--   rw [Set.mem_upperBounds] at mem
--   replace mem := fun a₀ => mem a₀
--   conv at mem => { intro; rw [Set.mem_range] }
--   sorry

--   repeat sorry


end Ordinal
