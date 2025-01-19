import Math.Data.Group.Basic

namespace Group

@[simp]
def mul (a b: Group) : Group where
  ty := a.ty × b.ty
  one' := ⟨1, 1⟩
  inv' | ⟨x, y⟩ => ⟨x⁻¹, y⁻¹⟩
  mul' | ⟨a, b⟩, ⟨x, y⟩ => ⟨a * x, b * y⟩
  mul_assoc' := by
    intro ⟨a₀, a₁⟩ ⟨b₀, b₁⟩ ⟨c₀, c₁⟩
    simp [mul_assoc]
  one_mul' := by
    intro ⟨a₀, a₁⟩
    simp [one_mul]
  inv_mul' := by
    intro ⟨a₀, a₁⟩
    simp [inv_mul_cancel]

instance : Mul Group := ⟨.mul⟩

def gmul_def (a b: Group) : a * b = a.mul b := rfl

def gmul.spec (a b c d: Group) : a ≈ c -> b ≈ d -> a * b ≈ c * d := by
  intro ⟨ac, ac_resp_one, ac_resp_inv, ac_resp_mul⟩
  intro ⟨bd, bd_resp_one, bd_resp_inv, bd_resp_mul⟩
  apply IsIsomorphic.intro (ac.toProd bd)
  simp [Equiv.toProd]
  show (ac.toFun 1, bd.toFun 1) = (1, 1)
  erw [ac_resp_one, bd_resp_one]
  intro ⟨x, y⟩
  show (_, _) = (_, _)
  congr
  apply ac_resp_inv
  apply bd_resp_inv
  intro ⟨x₀, y₀⟩ ⟨x₁, y₁⟩
  simp [Equiv.toProd]
  show (_, _) = (_, _)
  congr
  apply ac_resp_mul
  apply bd_resp_mul

def IsoClass.mul : IsoClass -> IsoClass -> IsoClass := by
  apply Quotient.lift₂ (⟦· * ·⟧)
  intros
  apply Quot.sound
  apply gmul.spec <;> assumption

instance : Mul IsoClass := ⟨IsoClass.mul⟩

def mk_mul (a b: Group) : ⟦a⟧ * ⟦b⟧ = ⟦a * b⟧ := rfl

def of_gmul_eq_one (a b: Group) : a * b ≈ 1 -> a ≈ 1 ∧ b ≈ 1 := by
  intro ⟨iso⟩
  apply And.intro
  · apply IsIsomorphic.intro ⟨(fun _ => ()), (fun x => (iso.invFun x).1), _, _⟩
    rfl
    any_goals try intro x; intros; rfl
    intro x
    simp [Equiv.symm]
    show (iso.invFun 1).fst = _
    rw [iso.inv_resp_one]
    show 1 = x
    symm
    have : Prod.mk x 1 = (1: (a * b).ty) := by
      apply iso.toFun_inj
      rfl
    exact (Prod.mk.inj this).left
  · apply IsIsomorphic.intro ⟨(fun _ => ()), (fun x => (iso.invFun x).2), _, _⟩
    rfl
    any_goals try intro x; intros; rfl
    intro x
    simp [Equiv.symm]
    show (iso.invFun 1).snd = _
    rw [iso.inv_resp_one]
    show 1 = x
    symm
    have : Prod.mk 1 x = (1: (a * b).ty) := by
      apply iso.toFun_inj
      rfl
    exact (Prod.mk.inj this).right

end Group
