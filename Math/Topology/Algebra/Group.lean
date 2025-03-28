import Math.Algebra.Group.Defs
import Math.Topology.Algebra.Monoid

open Topology

section

variable (α: Type*) [Topology α]

class IsContinuousNeg [Neg α]: Prop where
  continuous_neg: IsContinuous (fun x: α => -x) := by continuity

class IsContinuousInv [Inv α]: Prop where
  continuous_inv: IsContinuous (fun x: α => x⁻¹)

class IsTopologicalAddGroup [AddGroupOps α] extends IsAddGroup α, IsContinuousAdd α, IsContinuousNeg α where
class IsTopologicalGroup [GroupOps α] extends IsGroup α, IsContinuousMul α, IsContinuousInv α where

instance [Neg α] [h: IsContinuousNeg α] : IsContinuous (fun x: α => -x) := h.continuous_neg
instance [Inv α] [h: IsContinuousInv α] : IsContinuous (fun x: α => x⁻¹) := h.continuous_inv

end

section

variable {ι α: Type*} [Topology ι] [Topology α]

@[continuity]
def continuous_neg [Neg α] [IsContinuousNeg α] (f: ι -> α) (hf: IsContinuous f) : IsContinuous (fun x => -f x) := by
  show IsContinuous <| (fun x: α => -x) ∘ f
  apply IsContinuous.comp

@[continuity]
def continuous_inv [Inv α] [IsContinuousInv α] (f: ι -> α) (hf: IsContinuous f) : IsContinuous (fun x => (f x)⁻¹) := by
  show IsContinuous <| (fun x: α => x⁻¹) ∘ f
  apply IsContinuous.comp

instance [AddGroupOps α] [IsSubNegMonoid α] [IsContinuousAdd α] [IsContinuousNeg α] : IsContinuous (fun x: α × α => x.1 - x.2) := by
  simp [sub_eq_add_neg]
  apply continuous_add
  apply IsContinuous.prod_fst
  apply IsContinuous.id
  apply continuous_neg
  apply IsContinuous.prod_snd
  apply IsContinuous.id

instance [GroupOps α] [IsDivInvMonoid α] [IsContinuousMul α] [IsContinuousInv α] : IsContinuous (fun x: α × α => x.1 / x.2) := by
  simp [div_eq_mul_inv]
  apply continuous_mul
  apply IsContinuous.prod_fst
  apply IsContinuous.id
  apply continuous_inv
  apply IsContinuous.prod_snd
  apply IsContinuous.id

instance [AddGroupOps α] [IsAddGroup α] [IsContinuousAdd α] [IsContinuousNeg α] : IsContinuous (fun x: ℤ × α => x.1 • x.2) := by
  apply IsContinuous.push_discrete
  intro x
  simp
  cases x
  simp [zsmul_ofNat]
  apply continuous_nsmul
  continuity
  continuity
  simp [zsmul_negSucc]
  apply continuous_neg
  apply continuous_nsmul
  continuity
  continuity

instance [GroupOps α] [IsGroup α] [IsContinuousMul α] [IsContinuousInv α] : IsContinuous (fun x: ℤ × α => x.2 ^ x.1) := by
  apply IsContinuous.push_discrete
  intro x
  simp
  cases x
  simp [zpow_ofNat]
  apply continuous_npow
  continuity
  continuity
  simp [zpow_negSucc]
  apply continuous_inv
  apply continuous_npow
  continuity
  continuity

@[continuity]
def continuous_sub [AddGroupOps α] [IsTopologicalAddGroup α] (f g: ι -> α) (hf: IsContinuous f) (hg: IsContinuous g) : IsContinuous (fun x => f x - g x) := by
  show IsContinuous <| (fun x: α × α => x.1 - x.2) ∘ (fun _ => (_, _))
  apply IsContinuous.comp

@[continuity]
def continuous_div [GroupOps α] [IsTopologicalGroup α] (f g: ι -> α) (hf: IsContinuous f) (hg: IsContinuous g) : IsContinuous (fun x => f x / g x) := by
  show IsContinuous <| (fun x: α × α => x.1 / x.2) ∘ (fun _ => (_, _))
  apply IsContinuous.comp

@[continuity]
def continuous_zsmul [AddGroupOps α] [IsTopologicalAddGroup α] (f: ι -> ℤ) (g: ι -> α) (hf: IsContinuous f) (hg: IsContinuous g) : IsContinuous (fun x => f x • g x) := by
  show IsContinuous <| (fun x: ℤ × α => x.1 • x.2) ∘ (fun _ => (_, _))
  apply IsContinuous.comp

@[continuity]
def continuous_zpow [GroupOps α] [IsTopologicalGroup α] (f: ι -> ℤ) (g: ι -> α) (hf: IsContinuous f) (hg: IsContinuous g) : IsContinuous (fun x => g x ^ f x) := by
  show IsContinuous <| (fun x: ℤ × α => x.2 ^ x.1) ∘ (fun _ => (_, _))
  apply IsContinuous.comp

end
