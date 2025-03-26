import Math.Topology.Basic
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

instance {a : Topology α} {b: Topology β} (h: a ≈ₜ b) : IsContinuous h.toFun := h.toFun_continuous
instance {a : Topology α} {b: Topology β} (h: a ≈ₜ b) : IsContinuous h.invFun := h.invFun_continuous

def Homeomorphism.rfl {a: Topology α} : a ≈ₜ a where
  toEquiv := .rfl
  toFun_continuous := inferInstanceAs (IsContinuous id)
  invFun_continuous := inferInstanceAs (IsContinuous id)

def Homeomorphism.refl (a: Topology α) : a ≈ₜ a where
  toEquiv := .rfl
  toFun_continuous := inferInstanceAs (IsContinuous id)
  invFun_continuous := inferInstanceAs (IsContinuous id)

def Homeomorphism.symm {a: Topology α} {b: Topology β} (h: a ≈ₜ b) : b ≈ₜ a where
  toEquiv := h.toEquiv.symm
  toFun_continuous := h.invFun_continuous
  invFun_continuous := h.toFun_continuous

def Homeomorphism.trans {a: Topology α} {b: Topology β} {c: Topology γ} (h: a ≈ₜ b) (g: b ≈ₜ c) : a ≈ₜ c where
  toEquiv := h.toEquiv.trans g.toEquiv
  toFun_continuous := IsContinuous.comp h.toFun _
  invFun_continuous := IsContinuous.comp g.invFun _

def Iso.ofHomeomorphsim {topoa: Topology α} {topob: Topology β} : topoa ≈ₜ topob -> α ≃ₜ β := id

variable [topoa: Topology α] [topob: Topology β] [Topology γ]

def Iso.toHomeomorphsim : α ≃ₜ β -> topoa ≈ₜ topob := id

def Iso.rfl : α ≃ₜ α := .ofHomeomorphsim .rfl
def Iso.refl (α: Type*) [Topology α] : α ≃ₜ α := .ofHomeomorphsim .rfl
def Iso.symm (h: α ≃ₜ β) : β ≃ₜ α := h.toHomeomorphsim.symm
def Iso.trans (h: α ≃ₜ β) (g: β ≃ₜ γ) : α ≃ₜ γ := h.toHomeomorphsim.trans g

end Topology
