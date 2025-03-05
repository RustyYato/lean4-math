import Math.Logic.Small.Basic
import Math.Data.Fintype.Defs

-- every fintype is always small in any universe
instance [Fintype α] : Small.{u} α := by
  classical
  induction (Fintype.equivFin α) with | mk eqv =>
  refine ⟨_, ⟨eqv.trans (Equiv.ulift _).symm⟩⟩
