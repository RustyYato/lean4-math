import Math.Data.Countable.Card
import Math.Logic.Small.Basic

instance (priority := 10000) [Encodable α] : Small.{u} α where
  exists_equiv := by
    exists ULift (Encodable.Encoding α)
    refine ⟨?_⟩
    apply Equiv.trans
    apply Encodable.equivEncoding
    symm; apply Equiv.ulift

instance [IsCountable α] : Small.{u} α := by
    have := IsCountable.encodable α
    infer_instance
