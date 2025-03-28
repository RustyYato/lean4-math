import Math.Algebra.Monoid.Defs
import Math.Topology.Algebra.Semigroup

section

open Topology

variable {ι α: Type*} [Topology ι] [Topology α]

instance [AddMonoidOps α] [IsAddMonoid α] [IsContinuousAdd α] : IsContinuous (fun x: ℕ × α => x.1 • x.2) := by
  apply IsContinuous.push_discrete
  intro n
  simp
  induction n with
  | zero => continuity
  | succ n ih =>
    simp [succ_nsmul]
    continuity

instance [MonoidOps α] [IsMonoid α] [IsContinuousMul α] : IsContinuous (fun x: ℕ × α => x.2 ^ x.1) := by
  apply IsContinuous.push_discrete
  intro n
  simp
  induction n with
  | zero => continuity
  | succ n ih =>
    simp [npow_succ]
    continuity

@[continuity]
def continuous_nsmul [AddMonoidOps α] [IsAddMonoid α] [IsContinuousAdd α] (f: ι -> ℕ) (g: ι -> α) (hf: IsContinuous f) (hg: IsContinuous g) : IsContinuous (fun x => f x • g x) := by
  show IsContinuous <| (fun x: ℕ × α => x.1 • x.2) ∘ (fun _ => (_, _))
  apply IsContinuous.comp

@[continuity]
def continuous_npow [MonoidOps α] [IsMonoid α] [IsContinuousMul α] (f: ι -> ℕ) (g: ι -> α) (hf: IsContinuous f) (hg: IsContinuous g) : IsContinuous (fun x => g x ^ f x) := by
  show IsContinuous <| (fun x: ℕ × α => x.2 ^ x.1) ∘ (fun _ => (_, _))
  apply IsContinuous.comp

end
