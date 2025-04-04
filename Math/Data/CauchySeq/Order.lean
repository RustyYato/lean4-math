import Math.Data.CauchySeq.Basic

namespace CauchySeq

variable {α: Type*}
  [FieldOps γ] [LT γ] [LE γ] [Min γ] [Max γ]
  [IsField γ] [IsLinearLattice γ] [IsStrictOrderedSemiring γ]
  [FieldOps α] [IsField α] [Norm α γ]
  [SMul γ α] [IsModule γ α] [IsLawfulNorm α]

open Norm.ofAbs

local instance : Dist α γ := Norm.instDist α
local instance : IsMetric α := Norm.instIsMetric α
local instance : @Std.Commutative α (· + ·) := ⟨add_comm⟩
local instance :  @Std.Associative α (· + ·) := ⟨add_assoc⟩

-- def

end CauchySeq
