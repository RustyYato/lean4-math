import Math.Type.Notation
import Math.Data.Opposite

variable (α: Type*)

infixl:68 " ⊔ " => max

infixl:69 " ⊓ " => min

/-- Typeclass for the `⊤` (`\top`) notation -/
@[ext]
class Top (α : Type*) where
  /-- The top (`⊤`, `\top`) element -/
  top : α

/-- Typeclass for the `⊥` (`\bot`) notation -/
@[ext]
class Bot (α : Type*) where
  /-- The bot (`⊥`, `\bot`) element -/
  bot : α

/-- The top (`⊤`, `\top`) element -/
notation "⊤" => Top.top

/-- The bot (`⊥`, `\bot`) element -/
notation "⊥" => Bot.bot

instance (priority := 100) top_nonempty (α : Type*) [Top α] : Nonempty α :=
  ⟨⊤⟩

instance (priority := 100) bot_nonempty (α : Type*) [Bot α] : Nonempty α :=
  ⟨⊥⟩

attribute [match_pattern] Bot.bot Top.top

class IsLawfulTop (α: Type*) [LE α] [Top α]: Prop where
  le_top: ∀x: α, x ≤ ⊤

class IsLawfulBot (α: Type*) [LE α] [Bot α]: Prop where
  bot_le: ∀x: α, ⊥ ≤ x

export IsLawfulTop (le_top)
export IsLawfulBot (bot_le)

-- do not use this in bounds directly, this is only meant to be used to create a LawfulTop
-- for example, via `GaloisConnection`
class LawfulTop (α: Type*) [LE α] extends Top α where
  le_top: ∀x, x ≤ top

-- do not use this in bounds directly, this is only meant to be used to create a LawfulBot
-- for example, via `GaloisConnection`
class LawfulBot (α: Type*) [LE α] extends Bot α where
  bot_le: ∀x: α, ⊥ ≤ x

instance [LE α] [LawfulTop α] : IsLawfulTop α where
  le_top := LawfulTop.le_top
instance [LE α] [LawfulBot α] : IsLawfulBot α where
  bot_le := LawfulBot.bot_le

instance [Min α] : Max (Opposite α) where
  max a b := .mk (a.get ⊓ b.get)
instance [Max α] : Min (Opposite α) where
  min a b := .mk (a.get ⊔ b.get)

instance [Top α] : Bot (Opposite α) where
  bot := .mk ⊤
instance [Bot α] : Top (Opposite α) where
  top := .mk ⊥

instance [LE α] [Top α] [IsLawfulTop α] : IsLawfulBot (Opposite α) where
  bot_le := le_top (α := α)
instance [LE α] [Bot α] [IsLawfulBot α] : IsLawfulTop (Opposite α) where
  le_top := bot_le (α := α)

instance [LE α] [LawfulTop α] : LawfulBot αᵒᵖ where
  bot := ⊥
  bot_le := le_top (α := α)

instance [LE α] [LawfulBot α] : LawfulTop αᵒᵖ where
  top := ⊤
  le_top := bot_le (α := α)

-- `LawfulInf` states that the min is always at most as large as it's inputs
-- this does *not* provide a tight bound on min, if you need that use
-- `IsSemiLatticeMin`
class IsLawfulMin (α: Type*) [LE α] [Min α] where
  min_le_left: ∀(x y: α), x ⊓ y ≤ x
  min_le_right: ∀(x y: α), x ⊓ y ≤ y

-- `LawfulSup` states that the max is always at least as large as it's inputs
-- this does *not* provide a tight bound on min, if you need that use
-- `IsSemiLatticeMax`
class IsLawfulMax (α: Type*) [LE α] [Max α] where
  le_max_left: ∀(x y: α), x ≤ x ⊔ y
  le_max_right: ∀(x y: α), y ≤ x ⊔ y

-- do not use this in bounds directly, this is only meant to be used to create a LawfulInf
-- for example, via `GaloisConnection`
class LawfulInf (α: Type*) [LE α] extends Min α where
  min_le_left: ∀(x y: α), x ⊓ y ≤ x
  min_le_right: ∀(x y: α), x ⊓ y ≤ y
-- do not use this in bounds directly, this is only meant to be used to create a LawfulSup
-- for example, via `GaloisConnection`
class LawfulSup (α: Type*) [LE α] extends Max α where
  le_max_left: ∀(x y: α), x ≤ x ⊔ y
  le_max_right: ∀(x y: α), y ≤ x ⊔ y

export IsLawfulMin (min_le_left min_le_right)
export IsLawfulMax (le_max_left le_max_right)

instance [LE α] [Max α] [IsLawfulMax α] : IsLawfulMin αᵒᵖ where
  min_le_left := le_max_left (α := α)
  min_le_right := le_max_right (α := α)
instance [LE α] [Min α] [IsLawfulMin α] : IsLawfulMax αᵒᵖ where
  le_max_left := min_le_left (α := α)
  le_max_right := min_le_right (α := α)

instance [LE α] [LawfulInf α] : IsLawfulMin α where
  min_le_left := LawfulInf.min_le_left
  min_le_right := LawfulInf.min_le_right

instance [LE α] [LawfulSup α] : IsLawfulMax α where
  le_max_left := LawfulSup.le_max_left
  le_max_right := LawfulSup.le_max_right

instance [LE α] [LawfulInf α] : LawfulSup αᵒᵖ where
  le_max_left := min_le_left (α := α)
  le_max_right := min_le_right (α := α)
instance [LE α] [LawfulSup α] : LawfulInf αᵒᵖ where
  min_le_left := le_max_left (α := α)
  min_le_right := le_max_right (α := α)

instance [Top α] : Nonempty α := ⟨⊤⟩
instance [Bot α] : Nonempty α := ⟨⊥⟩
