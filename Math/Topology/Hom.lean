import Math.Topology.Constructions
import Math.Logic.Equiv.Defs

namespace Topology

structure Homeomorphism (ht: Topology α) (hb: Topology β) extends α ≃ β where
  toFun_continuous: IsContinuous toFun := by infer_instance
  invFun_continuous: IsContinuous invFun := by infer_instance

scoped infixl:25 " ≈ₜ " => Homeomorphism

-- a homeomorphism is an isomorphism for topologies
def Iso (α β: Type*) [Topology α] [Topology β] :=
  Homeomorphism (inferInstanceAs (Topology α)) (inferInstanceAs (Topology β))

scoped infixl:25 " ≃ₜ " => Iso

namespace Homeomorphism

variable {a : Topology α} {b: Topology β} {c: Topology γ}

instance (h: a ≈ₜ b) : IsContinuous h.toFun := h.toFun_continuous
instance {a : Topology α} {b: Topology β} (h: a ≈ₜ b) : IsContinuous h.invFun := h.invFun_continuous

instance : FunLike (a ≈ₜ b) α β where
  coe h := h.toEquiv
  coe_inj := by
    intro a b h; cases a; cases b; congr
    apply DFunLike.coe_inj
    assumption

instance (h: a ≈ₜ b) : IsContinuous h := h.toFun_continuous

def rfl {a: Topology α} : a ≈ₜ a where
  toEquiv := .rfl
  toFun_continuous := inferInstanceAs (IsContinuous id)
  invFun_continuous := inferInstanceAs (IsContinuous id)

def refl (a: Topology α) : a ≈ₜ a where
  toEquiv := .rfl
  toFun_continuous := inferInstanceAs (IsContinuous id)
  invFun_continuous := inferInstanceAs (IsContinuous id)

def symm (h: a ≈ₜ b) : b ≈ₜ a where
  toEquiv := h.toEquiv.symm
  toFun_continuous := h.invFun_continuous
  invFun_continuous := h.toFun_continuous

def trans (h: a ≈ₜ b) (g: b ≈ₜ c) : a ≈ₜ c where
  toEquiv := h.toEquiv.trans g.toEquiv
  toFun_continuous := IsContinuous.comp h.toFun _
  invFun_continuous := IsContinuous.comp g.invFun _

end Homeomorphism

namespace Iso

def ofHomeomorphsim {topoa: Topology α} {topob: Topology β} : topoa ≈ₜ topob -> α ≃ₜ β := id

variable [topoa: Topology α] [topob: Topology β] [Topology γ]
  [Topology α₀] [Topology β₀]

instance : FunLike (α ≃ₜ β) α β :=
  inferInstanceAs (FunLike (topoa ≈ₜ topob) α β)

instance (h: α ≃ₜ β) : IsContinuous h := h.toFun_continuous

def toHomeomorphsim : α ≃ₜ β -> topoa ≈ₜ topob := id

def rfl : α ≃ₜ α := .ofHomeomorphsim .rfl
def refl (α: Type*) [Topology α] : α ≃ₜ α := .ofHomeomorphsim .rfl
def symm (h: α ≃ₜ β) : β ≃ₜ α := h.toHomeomorphsim.symm
def trans (h: α ≃ₜ β) (g: β ≃ₜ γ) : α ≃ₜ γ := h.toHomeomorphsim.trans g

def congrProd (h: α ≃ₜ β) (g: α₀ ≃ₜ β₀) : α × α₀ ≃ₜ β × β₀ where
  toEquiv := Equiv.congrProd h.toEquiv g.toEquiv
  toFun_continuous := by
    show IsContinuous <| (fun (a, b) => (h a, g b))
    apply Topology.IsContinuous.prod_mk
    rw [←Function.comp_def]
    apply Topology.IsContinuous.comp
    apply Topology.IsContinuous.comp
  invFun_continuous := by
    show IsContinuous <| (fun (a, b) => (h.symm a, g.symm b))
    apply Topology.IsContinuous.prod_mk
    rw [←Function.comp_def]
    apply Topology.IsContinuous.comp
    apply Topology.IsContinuous.comp

def comm_prod : α × β ≃ₜ β × α where
  toEquiv := Equiv.commProd _ _
  toFun_continuous := by
    show IsContinuous <| (fun x: α × β => (x.2, x.1))
    apply Topology.IsContinuous.prod_mk
    infer_instance
    infer_instance
  invFun_continuous := by
    show IsContinuous <| (fun x: β × α => (x.2, x.1))
    apply Topology.IsContinuous.prod_mk
    infer_instance
    infer_instance

def subsing_prod_left [Subsingleton α₀] [Inhabited α₀] : α₀ × α ≃ₜ α where
  toEquiv := Equiv.subsing_prod_left
  toFun_continuous := by
    show IsContinuous <| (fun x: α₀ × α => x.2)
    infer_instance
  invFun_continuous := by
    show IsContinuous <| (fun x: α => (default, x))
    apply Topology.IsContinuous.comp'
    infer_instance
    apply Topology.IsContinuous.prod_mk
    infer_instance
    infer_instance

def subsing_prod_right [Subsingleton α₀] [Inhabited α₀] : α × α₀ ≃ₜ α :=
  comm_prod.trans subsing_prod_left

-- def congrPi {α: ι₀ -> Type*} {β: ι₁ -> Type*} [∀i, Topology (α i)] [∀i, Topology (β i)]
--   (hι: ι₀ ≃ ι₁) (h: ∀i: ι₀, α i ≃ₜ β (hι i)) : (∀i, α i) ≃ₜ (∀i, β i) where
--   toEquiv := Equiv.congrPi hι (fun i => (h i).toEquiv)
--   toFun_continuous := by
--     show IsContinuous <| _
--     simp [Equiv.congrPi]
--     sorry
--   invFun_continuous := by
--     show IsContinuous <| _
--     simp [Equiv.congrPi]
--     refine ⟨?_⟩
--     intro S hS
--     sorry

def coe_symm (h: α ≃ₜ β) (x: α) : h.symm (h x) = x := h.leftInv _
def symm_coe (h: α ≃ₜ β) (x: β) : h (h.symm x) = x := h.rightInv _

end Iso

end Topology
