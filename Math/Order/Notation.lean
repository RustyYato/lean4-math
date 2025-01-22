import Math.Type.Notation
import Math.Data.Opposite

variable (α: Type*)

class Sup where
  sup: α -> α -> α

class Inf where
  inf: α -> α -> α

infixl:68 " ⊔ " => Sup.sup

infixl:69 " ⊓ " => Inf.inf

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

class LawfulTop (α: Type*) [LE α] [Top α]: Prop where
  le_top: ∀x: α, x ≤ ⊤

class LawfulBot (α: Type*) [LE α] [Bot α]: Prop where
  bot_le: ∀x: α, ⊥ ≤ x

export LawfulTop (le_top)
export LawfulBot (bot_le)

instance [Inf α] : Sup (Opposite α) where
  sup a b := .mk (a.get ⊓ b.get)
instance [Sup α] : Inf (Opposite α) where
  inf a b := .mk (a.get ⊔ b.get)

instance [Top α] : Bot (Opposite α) where
  bot := .mk ⊤
instance [Bot α] : Top (Opposite α) where
  top := .mk ⊥

instance [LE α] [Top α] [LawfulTop α] : LawfulBot (Opposite α) where
  bot_le := le_top (α := α)
instance [LE α] [Bot α] [LawfulBot α] : LawfulTop (Opposite α) where
  le_top := bot_le (α := α)
