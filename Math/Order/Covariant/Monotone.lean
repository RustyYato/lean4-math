import Math.Order.Covariant.Defs
import Math.Order.Monotone

variable {μ: β -> α -> α} {r: α -> α -> Prop} [LE α]
variable {f : α → γ} [LE γ]

def Covariant.monotone_of_const [CovariantClass μ (· ≤ ·)] (b: β) : Monotone (μ b) :=
  fun _ _ => act_rel_act_of_rel b

theorem Monotone.covariant_of_const [CovariantClass μ (· ≤ ·)] (hf : Monotone f) (b: β) :
  Monotone (f <| μ b ·) := hf.comp (Covariant.monotone_of_const b)
