import Math.Algebra.Semigroup.Defs
import Math.Topology.Constructions

open Topology

section

variable (α: Type*) [Topology α]

class IsContinuousAdd [Add α]: Prop where
  continuous_add: IsContinuous (fun x: α × α => x.1 + x.2) := by continuity

class IsContinuousMul [Mul α]: Prop where
  continuous_mul: IsContinuous (fun x: α × α => x.1 * x.2) := by continuity

instance [Add α] [h: IsContinuousAdd α] : IsContinuous (fun x: α × α => x.1 + x.2) := h.continuous_add
instance [Mul α] [h: IsContinuousMul α] : IsContinuous (fun x: α × α => x.1 * x.2) := h.continuous_mul

end

section

variable {ι α: Type*} [Topology ι] [Topology α]

@[continuity]
def continuous_add [Add α] [IsContinuousAdd α] (f g: ι -> α) (hf: IsContinuous f) (hg: IsContinuous g) : IsContinuous (fun x => f x + g x) := by
  show IsContinuous <| (fun x: α × α => x.1 + x.2) ∘ (fun _ => (_, _))
  apply IsContinuous.comp

@[continuity]
def continuous_mul [Mul α] [IsContinuousMul α] (f g: ι -> α) (hf: IsContinuous f) (hg: IsContinuous g) : IsContinuous (fun x => f x * g x) := by
  show IsContinuous <| (fun x: α × α => x.1 * x.2) ∘ (fun _ => (_, _))
  apply IsContinuous.comp

end
