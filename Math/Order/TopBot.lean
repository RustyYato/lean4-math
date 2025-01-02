import Math.Order.Notation
import Math.Order.OrderIso

def WithTop := Option
def WithBot := Option

@[coe]
abbrev WithTop.of : α -> WithTop α := Option.some
@[coe]
abbrev WithBot.of : α -> WithBot α := Option.some

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

instance [Sup α] : Sup (WithTop α) where
  sup
  | ⊤, _ | _, ⊤ => ⊤
  | .of a, .of b => .of (a ⊔ b)

instance [Inf α] : Inf (WithTop α) where
  inf
  | ⊤, a | a, ⊤ => a
  | .of a, .of b => .of (a ⊓ b)

instance [Sup α] : Sup (WithBot α) where
  sup
  | ⊥, a | a, ⊥ => a
  | .of a, .of b => .of (a ⊔ b)

instance [Inf α] : Inf (WithBot α) where
  inf
  | ⊥, _ | _, ⊥ => ⊥
  | .of a, .of b => .of (a ⊓ b)

def WithTop.orderIsoWithBot [_root_.LE α] : WithTop α ≃o OrderDual (WithBot (OrderDual α)) where
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
  show (OrderDual (OrderDual (WithBot (OrderDual (OrderDual α))))) ≃o (OrderDual (OrderDual (WithBot (OrderDual (OrderDual β)))))
  apply OrderDual.orderIsoCongr
  apply OrderIso.trans
  apply WithTop.orderIsoWithBot.symm
  apply flip OrderIso.trans
  apply WithTop.orderIsoWithBot
  apply WithTop.orderIsoCongr
  apply OrderDual.orderIsoCongr
  assumption

def WithBot.orderIsoWithTop [_root_.LE α] : WithBot α ≃o OrderDual (WithTop (OrderDual α)) := by
  apply flip OrderIso.trans
  apply OrderDual.orderIsoCongr
  symm
  apply WithTop.orderIsoWithBot
  rfl

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

instance [LE α] [LT α] [IsPreOrder α] : IsPreOrder (WithBot α) :=
  WithBot.orderIsoWithTop.symm.instIsPreOrder (by
    intro a b
    apply Iff.intro
    intro h
    cases h
    exact WithBot.LT.bot _
    rename_i r
    exact WithBot.LT.of r
    intro h
    cases a; cases b
    contradiction
    show ⊥ < _
    exact WithTop.LT.top _
    cases b
    contradiction
    cases h; rename_i h
    exact WithTop.LT.of h)

instance [LE α] [LT α] [IsPartialOrder α] : IsPartialOrder (WithTop α) where
  le_antisymm := by
    intro a b ab ba
    cases ab <;> cases ba
    rfl
    congr
    apply le_antisymm <;> assumption

instance [LE α] [LT α] [IsPartialOrder α] : IsPartialOrder (WithBot α) :=
  WithBot.orderIsoWithTop.symm.instIsPartialOrder
