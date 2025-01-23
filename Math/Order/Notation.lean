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

instance [Inf α] : Sup (Opposite α) where
  sup a b := .mk (a.get ⊓ b.get)
instance [Sup α] : Inf (Opposite α) where
  inf a b := .mk (a.get ⊔ b.get)

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

-- `LawfulInf` states that the inf is always at most as large as it's inputs
-- this does *not* provide a tight bound on inf, if you need that use
-- `IsSemiLatticeInf`
class IsLawfulInf (α: Type*) [LE α] [Inf α] where
  inf_le_left: ∀(x y: α), x ⊓ y ≤ x
  inf_le_right: ∀(x y: α), x ⊓ y ≤ y

-- `LawfulSup` states that the sup is always at least as large as it's inputs
-- this does *not* provide a tight bound on inf, if you need that use
-- `IsSemiLatticeSup`
class IsLawfulSup (α: Type*) [LE α] [Sup α] where
  le_sup_left: ∀(x y: α), x ≤ x ⊔ y
  le_sup_right: ∀(x y: α), y ≤ x ⊔ y

-- do not use this in bounds directly, this is only meant to be used to create a LawfulInf
-- for example, via `GaloisConnection`
class LawfulInf (α: Type*) [LE α] extends Inf α where
  inf_le_left: ∀(x y: α), x ⊓ y ≤ x
  inf_le_right: ∀(x y: α), x ⊓ y ≤ y
-- do not use this in bounds directly, this is only meant to be used to create a LawfulSup
-- for example, via `GaloisConnection`
class LawfulSup (α: Type*) [LE α] extends Sup α where
  le_sup_left: ∀(x y: α), x ≤ x ⊔ y
  le_sup_right: ∀(x y: α), y ≤ x ⊔ y

export IsLawfulInf (inf_le_left inf_le_right)
export IsLawfulSup (le_sup_left le_sup_right)

instance [LE α] [Sup α] [IsLawfulSup α] : IsLawfulInf αᵒᵖ where
  inf_le_left := le_sup_left (α := α)
  inf_le_right := le_sup_right (α := α)
instance [LE α] [Inf α] [IsLawfulInf α] : IsLawfulSup αᵒᵖ where
  le_sup_left := inf_le_left (α := α)
  le_sup_right := inf_le_right (α := α)

instance [LE α] [LawfulInf α] : IsLawfulInf α where
  inf_le_left := LawfulInf.inf_le_left
  inf_le_right := LawfulInf.inf_le_right

instance [LE α] [LawfulSup α] : IsLawfulSup α where
  le_sup_left := LawfulSup.le_sup_left
  le_sup_right := LawfulSup.le_sup_right

instance [LE α] [LawfulInf α] : LawfulSup αᵒᵖ where
  le_sup_left := inf_le_left (α := α)
  le_sup_right := inf_le_right (α := α)
instance [LE α] [LawfulSup α] : LawfulInf αᵒᵖ where
  inf_le_left := le_sup_left (α := α)
  inf_le_right := le_sup_right (α := α)
