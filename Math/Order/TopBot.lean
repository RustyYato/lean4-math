import Math.Order.Notation
import Math.Order.OrderIso

def WithTop := Option
def WithBot := Option

@[coe]
abbrev WithTop.of : α -> WithTop α := Option.some
@[coe]
abbrev WithBot.of : α -> WithBot α := Option.some

def WithTop.of_inj : ∀{x y: α}, WithTop.of x = .of y ↔ x = y :=
  Function.Injective.eq_iff (fun _ _ => Option.some.inj)
def WithBot.of_inj : ∀{x y: α}, WithBot.of x = .of y ↔ x = y :=
  Function.Injective.eq_iff (fun _ _ => Option.some.inj)

instance : Coe α (WithTop α) := ⟨.of⟩
instance : Coe α (WithBot α) := ⟨.of⟩

instance : Top (WithTop α) where
  top := .none
instance : Bot (WithBot α) where
  bot := .none

instance [Top α] : Top (WithBot α) where
  top := .of ⊤
instance [Bot α] : Bot (WithTop α) where
  bot := .of ⊥

@[cases_eliminator]
def WithTop.cases {motive: WithTop α -> Sort*}
  (top: motive ⊤)
  (of: ∀x, motive (.of x)):
  ∀x, motive x
| ⊤ => top
| .of x => of x

@[cases_eliminator]
def WithBot.cases {motive: WithBot α -> Sort*}
  (bot: motive ⊥)
  (of: ∀x, motive (.of x)):
  ∀x, motive x
| ⊥ => bot
| .of x => of x

inductive WithTop.LE [LE α] : WithTop α -> WithTop α -> Prop where
| top (x: WithTop α) : LE x ⊤
| of {x y: α} : x ≤ y -> LE x y

inductive WithTop.LT [LT α] : WithTop α -> WithTop α -> Prop where
| top (x: α) : LT x ⊤
| of {x y: α} : x < y -> LT x y

inductive WithBot.LE [LE α] : WithBot α -> WithBot α -> Prop where
| bot (x: WithBot α) : LE ⊥ x
| of {x y: α} : x ≤ y -> LE x y

inductive WithBot.LT [LT α] : WithBot α -> WithBot α -> Prop where
| bot (x: α) : LT ⊥ x
| of {x y: α} : x < y -> LT x y

instance [LE α] : LE (WithTop α) := ⟨WithTop.LE⟩
instance [LE α] : LE (WithBot α) := ⟨WithBot.LE⟩
instance [LT α] : LT (WithTop α) := ⟨WithTop.LT⟩
instance [LT α] : LT (WithBot α) := ⟨WithBot.LT⟩

instance [Max α] : Max (WithTop α) where
  max
  | ⊤, _ | _, ⊤ => ⊤
  | .of a, .of b => .of (a ⊔ b)

instance [Min α] : Min (WithTop α) where
  min
  | ⊤, a | a, ⊤ => a
  | .of a, .of b => .of (a ⊓ b)

instance [Max α] : Max (WithBot α) where
  max
  | ⊥, a | a, ⊥ => a
  | .of a, .of b => .of (a ⊔ b)

instance [Min α] : Min (WithBot α) where
  min
  | ⊥, _ | _, ⊥ => ⊥
  | .of a, .of b => .of (a ⊓ b)

def WithTop.orderIsoWithBot [_root_.LE α] : WithTop α ≃o Opposite (WithBot (Opposite α)) where
  toFun
  | ⊤ => .mk ⊥
  | .of x => .mk (.of (.mk x))
  invFun
  | .mk ⊥ => ⊤
  | .mk (.of (.mk x)) => .of x
  leftInv
  | ⊤ | .of x => rfl
  rightInv
  | .mk ⊥
  | .mk (.of (.mk x)) => rfl
  resp_rel := by
    intro a b
    dsimp
    apply Iff.intro
    intro h
    cases h with
    | top => exact WithBot.LE.bot _
    | of h => exact WithBot.LE.of h
    intro h
    cases b
    apply WithTop.LE.top
    cases a
    contradiction
    apply WithTop.LE.of
    cases h
    assumption

def WithTop.orderIsoCongr [_root_.LE α] [_root_.LE β] (h: α ≃o β) : WithTop α ≃o WithTop β where
  toFun
  | ⊤ => ⊤
  | .of x => of (h x)
  invFun
  | ⊤ => ⊤
  | .of x => .of (h.symm x)
  leftInv
  | ⊤ => rfl
  | .of x => by
    dsimp
    rw [h.coe_symm]
  rightInv
  | ⊤ => rfl
  | .of x =>  by
    dsimp
    rw [h.symm_coe]
  resp_rel := by
    intro a b
    dsimp
    apply Iff.intro
    intro h
    cases h with
    | top => exact WithTop.LE.top _
    | of r => exact WithTop.LE.of (h.resp_rel.mp r)
    intro h
    cases b
    apply WithTop.LE.top
    cases a
    contradiction
    apply WithTop.LE.of
    cases h; rename_i r
    exact h.resp_rel.mpr r

def WithBot.orderIsoCongr [_root_.LE α] [_root_.LE β] (h: α ≃o β) : WithBot α ≃o WithBot β := by
  show (Opposite (Opposite (WithBot (Opposite (Opposite α))))) ≃o (Opposite (Opposite (WithBot (Opposite (Opposite β)))))
  apply Opposite.orderIsoCongr
  apply OrderIso.trans
  apply WithTop.orderIsoWithBot.symm
  apply flip OrderIso.trans
  apply WithTop.orderIsoWithBot
  apply WithTop.orderIsoCongr
  apply Opposite.orderIsoCongr
  assumption

def WithBot.orderIsoWithTop [_root_.LE α] : WithBot α ≃o Opposite (WithTop (Opposite α)) := by
  apply flip OrderIso.trans
  apply Opposite.orderIsoCongr
  symm
  apply WithTop.orderIsoWithBot
  rfl

instance [LE α] : IsLawfulTop (WithTop α) where
  le_top := WithTop.LE.top
instance [LE α] : IsLawfulBot (WithBot α) where
  bot_le := WithBot.LE.bot

instance [LE α] [Bot α] [IsLawfulBot α] : IsLawfulBot (WithTop α) where
  bot_le := by
    intro x
    cases x
    apply le_top
    apply WithTop.LE.of
    apply bot_le
instance [LE α] [Top α] [IsLawfulTop α] : IsLawfulTop (WithBot α) where
  le_top := by
    intro x
    cases x
    apply bot_le
    apply WithBot.LE.of
    apply le_top

instance [LE α] [LT α] [IsPreOrder α] : IsPreOrder (WithTop α) where
  lt_iff_le_and_not_le := by
    intro a b
    cases a <;> cases b
    all_goals apply Iff.intro
    any_goals
      intro
      contradiction
    any_goals
      intro ⟨_, _⟩
      contradiction
    intro
    apply And.intro (WithTop.LE.top _) nofun
    intro
    exact (WithTop.LT.top _)
    intro (WithTop.LT.of h)
    replace h := lt_iff_le_and_not_le.mp h
    apply And.intro
    exact WithTop.LE.of h.left
    intro (WithTop.LE.of g)
    exact h.right g
    intro ⟨WithTop.LE.of h, g⟩
    apply WithTop.LT.of
    apply lt_iff_le_and_not_le.mpr
    apply And.intro h
    intro r
    exact g (.of r)
  le_refl a := by
    cases a
    exact .top _
    exact .of (le_refl (α := α) _)
  le_trans := by
    intro a b c ab bc
    cases ab <;> cases bc
    exact .top _
    exact .top _
    apply WithTop.LE.of
    apply le_trans <;> assumption

instance [LE α] [LT α] [IsLawfulLT α] : IsLawfulLT (WithBot α) where
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.intro
    intro h
    cases h
    apply And.intro
    exact WithBot.LE.bot _
    intro h
    contradiction
    rename_i h
    rw [lt_iff_le_and_not_le] at h
    obtain ⟨h, g⟩ := h
    apply And.intro
    apply WithBot.LE.of
    assumption
    intro h; apply g
    cases h; assumption
    intro ⟨h, g⟩
    cases h
    cases b; have := g (bot_le _)
    contradiction
    apply WithBot.LT.bot
    apply WithBot.LT.of
    rw [lt_iff_le_and_not_le]
    apply And.intro
    assumption
    intro h; apply g
    apply WithBot.LE.of
    assumption

instance [LE α] [LT α] [IsPreOrder α] : IsPreOrder (WithBot α) :=
  WithBot.orderIsoWithTop.symm.instIsPreOrder

instance [LE α] [LT α] [IsPartialOrder α] : IsPartialOrder (WithTop α) where
  le_antisymm := by
    intro a b ab ba
    cases ab <;> cases ba
    rfl
    congr
    apply le_antisymm <;> assumption

instance [LE α] [LT α] [IsPartialOrder α] : IsPartialOrder (WithBot α) :=
  WithBot.orderIsoWithTop.symm.instIsPartialOrder

instance [LE α] [dec: ∀a b: α, Decidable (a ≤ b)] : ∀a b: WithTop α,  Decidable (a ≤ b)
| .of a, .of b =>
  match dec a b with
  | .isTrue h => .isTrue (.of h)
  | .isFalse h => .isFalse (fun
    | .of g => h g)
| .none, .of _ => .isFalse nofun
| _, .none => .isTrue (WithTop.LE.top _)

instance [LT α] [dec: ∀a b: α, Decidable (a < b)] : ∀a b: WithTop α,  Decidable (a < b)
| .of a, .of b =>
  match dec a b with
  | .isTrue h => .isTrue (.of h)
  | .isFalse h => .isFalse (fun
    | .of g => h g)
| .none, .of _ => .isFalse nofun
| .of _, .none => .isTrue (WithTop.LT.top _)
| .none, .none => .isFalse nofun

instance [LE α] [dec: ∀a b: α, Decidable (a ≤ b)] : ∀a b: WithBot α, Decidable (a ≤ b)
| .of a, .of b =>
  match dec a b with
  | .isTrue h => .isTrue (.of h)
  | .isFalse h => .isFalse (fun
    | .of g => h g)
| .none, _ => .isTrue (WithBot.LE.bot _)
| .of _, .none => .isFalse nofun

instance [LT α] [dec: ∀a b: α, Decidable (a < b)] : ∀a b: WithBot α,  Decidable (a < b)
| .of a, .of b =>
  match dec a b with
  | .isTrue h => .isTrue (.of h)
  | .isFalse h => .isFalse (fun
    | .of g => h g)
| .none, .of _ => .isTrue (WithBot.LT.bot _)
| _, .none => .isFalse nofun

instance instWfLT [LT α] [wf: @Relation.IsWellFounded α (· < ·)] : @Relation.IsWellFounded (WithBot α) (· < ·) where
  wf := by
    apply WellFounded.intro
    intro x
    cases wf with | mk wf =>
    cases x
    apply Acc.intro
    intro y h; contradiction
    rename_i x
    induction x using wf.induction with
    | h x ih =>
    apply Acc.intro
    intro y h
    cases h
    apply Acc.intro
    intro y h; contradiction
    apply ih
    assumption

instance [wf: WellFoundedRelation α] : WellFoundedRelation (WithBot α) where
  rel := @WithBot.LT α ⟨wf.rel⟩
  wf := by
    have : Relation.IsWellFounded wf.rel := ⟨wf.wf⟩
    have : Relation.IsWellFounded (@WithBot.LT α ⟨wf.rel⟩) := @instWfLT (α := α) ⟨wf.rel⟩ inferInstance
    apply this.wf

instance [DecidableEq α] : DecidableEq (WithBot α) := inferInstanceAs (DecidableEq (Option α))
instance [DecidableEq α] : DecidableEq (WithTop α) := inferInstanceAs (DecidableEq (Option α))

instance [LE α] [@Relation.IsTotal α (· ≤ ·)] : @Relation.IsTotal (WithTop α) (· ≤ ·) where
  total := by
    intro a b
    cases a <;> cases b
    any_goals right; apply WithTop.LE.top
    left; apply WithTop.LE.top
    rename_i a b
    rcases Relation.total (· ≤ ·) a b with h | h
    left; apply WithTop.LE.of; assumption
    right; apply WithTop.LE.of; assumption

instance [LE α] [@Relation.IsTotal α (· ≤ ·)] : @Relation.IsTotal (WithBot α) (· ≤ ·) where
  total := by
    intro a b
    cases a <;> cases b
    any_goals left; apply WithBot.LE.bot
    right; apply WithBot.LE.bot
    rename_i a b
    rcases Relation.total (· ≤ ·) a b with h | h
    left; apply WithBot.LE.of; assumption
    right; apply WithBot.LE.of; assumption

instance [Min α] : Min (WithBot α) where
  min
  | ⊥, _ | _, ⊥ => ⊥
  | .of x, .of y => .of (min x y)
instance [Max α] : Max (WithBot α) where
  max
  | ⊥, x | x, ⊥ => x
  | .of x, .of y => .of (max x y)

instance [Min α] : Min (WithTop α) where
  min
  | ⊤, x | x, ⊤ => x
  | .of x, .of y => .of (min x y)
instance [Max α] : Max (WithTop α) where
  max
  | ⊤, _ | _, ⊤ => ⊤
  | .of x, .of y => .of (max x y)

@[simp, norm_cast]
def WithTop.of_le [_root_.LE α] : ∀{x y: α}, WithTop.of x ≤ .of y ↔ x ≤ y := by
  intro a b
  apply Iff.intro
  rintro ⟨h⟩; assumption
  exact WithTop.LE.of
@[simp, norm_cast]
def WithBot.of_le [_root_.LE α] : ∀{x y: α}, WithBot.of x ≤ .of y ↔ x ≤ y := by
  intro a b
  apply Iff.intro
  rintro ⟨h⟩; assumption
  exact WithBot.LE.of
@[simp, norm_cast]
def WithTop.of_lt [_root_.LT α] : ∀{x y: α}, WithTop.of x < .of y ↔ x < y := by
  intro a b
  apply Iff.intro
  rintro ⟨h⟩; assumption
  exact WithTop.LT.of
@[simp, norm_cast]
def WithBot.of_lt [_root_.LT α] : ∀{x y: α}, WithBot.of x < .of y ↔ x < y := by
  intro a b
  apply Iff.intro
  rintro ⟨h⟩; assumption
  exact WithBot.LT.of
