import Math.Relation.Defs
import Math.Type.Notation

section

variable {β α: Type*} (μ: β -> α -> α) (r: α -> α -> Prop)

def Covariant : Prop :=
  ∀ (b: β) {a₁ a₂: α}, r a₁ a₂ → r (μ b a₁) (μ b a₂)
def Contravariant : Prop :=
  ∀ (b: β) {a₁ a₂: α}, r (μ b a₁) (μ b a₂) -> r a₁ a₂

class CovariantClass : Prop where
  elim : Covariant μ r
class ContravariantClass : Prop where
  elim : Contravariant μ r

theorem rel_iff_cov [CovariantClass μ r] [ContravariantClass μ r] (b: β) {a₁ a₂: α} :
  r (μ b a₁) (μ b a₂) ↔ r a₁ a₂ := ⟨ContravariantClass.elim _, CovariantClass.elim _⟩

end

variable {α β: Type*} {μ: β -> α -> α} {r: α -> α -> Prop}

def Contravariant.flip (h: Contravariant μ r) : Contravariant μ (flip r) :=
  fun a _ _ => h a

def Covariant.flip (h: Covariant μ r) : Covariant μ (flip r) :=
  fun a _ _ => h a

instance [h: CovariantClass μ r] : CovariantClass μ (flip r) where
  elim := h.elim.flip
instance [h: ContravariantClass μ r] : ContravariantClass μ (flip r) where
  elim := h.elim.flip

section

variable [h: CovariantClass μ r]

def act_rel_act_of_rel (b: β) {a₀ a₁: α} (ra: r a₀ a₁) : r (μ b a₀) (μ b a₁) := h.elim b ra

variable [Relation.IsTrans r]

def act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) : r (μ m a) c :=
  trans (act_rel_act_of_rel m ab) rl

def rel_act_of_rel_of_rel_act (ab : r a b) (rr : r c (μ m a)) : r c (μ m b) :=
  trans rr (act_rel_act_of_rel _ ab)

end

section

variable [h: ContravariantClass μ r]

def rel_of_act_rel_act (b: β) {a₀ a₁: α} (ra: r (μ b a₀) (μ b a₁)) : r a₀ a₁ := h.elim b ra

end
