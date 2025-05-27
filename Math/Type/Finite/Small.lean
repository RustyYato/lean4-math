import Math.Type.Finite
import Math.Logic.Small.Basic

-- every finite type is always small in any universe
-- since it is isomorphic to `Fin n` which is `Small.{0}`
instance [IsFinite α] : Small.{u} α := by
  classical
  obtain ⟨n, ⟨eqv⟩⟩ := IsFinite.existsEquiv α
  exists ULift (Fin n)
  refine ⟨?_⟩
  apply eqv.symm.trans
  apply (Equiv.ulift _).symm
