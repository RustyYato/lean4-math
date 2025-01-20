import Math.Data.Group.Basic
import Math.Data.Quotient.Fintype

namespace Group

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

-- the direct indexed product of groups
def imul {ι: Type*} (G: ι -> Group) : Group where
  ty := ∀x: ι, (G x).ty
  one' := fun x => 1
  inv' f := fun x => (f x)⁻¹
  mul' f g := fun x => f x * g x
  mul_assoc' := by
    intro a b c
    dsimp
    ext
    rw [mul_assoc]
  one_mul' := by
    intro a
    dsimp
    ext
    rw [one_mul]
  inv_mul' := by
    intro a
    dsimp; ext
    rw [inv_mul_cancel]

def gmul_def (a b: Group) : a * b = a.mul b := rfl

def gmul.spec (a b c d: Group) : a ≈ c -> b ≈ d -> a * b ≈ c * d := by
  intro ⟨ac, ac_resp_inv, ac_resp_mul⟩
  intro ⟨bd, bd_resp_inv, bd_resp_mul⟩
  apply IsIsomorphic.intro (ac.toProd bd)
  simp [Equiv.toProd]
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

def imul.spec
  (a b: ι -> Group)
  (eq: ∀x, Isomorphsism (a x) (b x)): Isomorphsism (imul a) (imul b) where
  toEquiv := Pi.congrEquiv Equiv.refl <| fun x => (eq x).toEquiv
  resp_mul' := by
    intro x y
    show (fun z => (eq z) (x z * y z)) = _
    conv => {
      lhs; intro z
      rw [(eq z).resp_mul]
    }
    rfl
  resp_inv' := by
    intro x
    show (fun z => (eq z) (x z)⁻¹) = _
    conv => {
      lhs; intro z
      rw [(eq z).resp_inv]
    }
    rfl

def IsoClass.mul : IsoClass -> IsoClass -> IsoClass := by
  apply Quotient.lift₂ (⟦· * ·⟧)
  intros
  apply Quot.sound
  apply gmul.spec <;> assumption

instance : Mul IsoClass := ⟨IsoClass.mul⟩

noncomputable
def IsoClass.imul (f: ι -> IsoClass) : IsoClass := by
  refine Quotient.ilift ?_ ?_ f
  intro f
  exact ⟦Group.imul f⟧
  intro g₀ g₁ eqv
  apply Quotient.sound
  refine ⟨?_⟩
  apply imul.spec
  intro x
  apply Classical.choice
  obtain ⟨eq⟩ := (eqv x)
  exact ⟨eq⟩

def IsoClass.fimul [Fintype ι] [DecidableEq ι] (f: ι -> IsoClass) : IsoClass := by
  refine Quotient.flift ?_ ?_ f
  intro f
  exact ⟦Group.imul f⟧
  intro g₀ g₁ eqv
  replace eqv  := Fintype.axiomOfChoice (α := ι) <| fun x => by
    obtain ⟨x⟩ := eqv x
    exact ⟨x⟩
  obtain ⟨eqv⟩ := eqv
  apply Quotient.sound
  refine ⟨?_⟩
  apply imul.spec
  exact eqv

def IsoClass.fimul_eq_imul [Fintype ι] [DecidableEq ι] (f: ι -> IsoClass) : fimul f = imul f := by
  induction f using Quotient.iind with | mk f =>
  unfold imul fimul
  rw [Quotient.mk_ilift, Quotient.mk_flift]

def mk_mul (a b: Group) : ⟦a⟧ * ⟦b⟧ = ⟦a * b⟧ := rfl
def mk_imul (f: ι -> Group) : IsoClass.imul (fun x => ⟦f x⟧) = ⟦Group.imul f⟧ :=
  Quotient.mk_ilift _ _ _
def mk_fimul [Fintype ι] [DecidableEq ι] (f: ι -> Group) : IsoClass.fimul (fun x => ⟦f x⟧) = ⟦Group.imul f⟧ :=
  Quotient.mk_flift _ _ _

def of_gmul_eq_one (a b: Group) : a * b ≈ 1 -> a ≈ 1 ∧ b ≈ 1 := by
  intro ⟨iso⟩
  apply And.intro
  · apply IsIsomorphic.intro ⟨(fun _ => ()), (fun x => (iso.invFun x).1), _, _⟩
    any_goals try intro x; intros; rfl
    intro x
    simp [Equiv.symm]
    show (iso.symm 1).fst = _
    rw [iso.symm.resp_one]
    show 1 = x
    symm
    have : Prod.mk x 1 = (1: (a * b).ty) := by
      apply iso.toFun_inj
      rfl
    exact (Prod.mk.inj this).left
  · apply IsIsomorphic.intro ⟨(fun _ => ()), (fun x => (iso.invFun x).2), _, _⟩
    any_goals try intro x; intros; rfl
    intro x
    simp [Equiv.symm]
    show (iso.symm 1).snd = _
    rw [iso.symm.resp_one]
    show 1 = x
    symm
    have : Prod.mk 1 x = (1: (a * b).ty) := by
      apply iso.toFun_inj
      rfl
    exact (Prod.mk.inj this).right

def gmul_eq_imul (a b: Group) : Isomorphsism (a * b) (imul fun x: Bool => bif x then a else b) where
  toFun | (x, y) => fun
    | true => x
    | false => y
  invFun f := (f true, f false)
  leftInv := by
    intro (x, y)
    rfl
  rightInv := by
    intro f
    dsimp
    apply funext
    intro x
    cases x <;> rfl
  resp_inv' := by
    dsimp
    intro (x, y)
    dsimp
    apply funext
    intro z
    cases z
    rfl
    rfl
  resp_mul' := by
    dsimp
    intro (x₀, y₀) (x₁, y₁)
    apply funext
    intro z
    cases z
    rfl
    rfl

def IsoClass.gmul_eq_fimul (a b: IsoClass) :
  a * b = fimul (fun x: Bool => bif x then a else b) := by
  induction a, b with | mk a b=>
  show _ = fimul fun x => ⟦bif x then a else b⟧
  rw [mk_fimul]
  apply Quotient.sound
  refine ⟨?_⟩
  apply gmul_eq_imul

end Group
