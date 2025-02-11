import Math.GroupTheory.Basic
import Math.Algebra.Units

namespace Group

-- the group of units of a monoid
def ofUnits (α: Type u) [MonoidOps α] [IsMonoid α] : Group (Units α) where

-- the group of additive units of a add monoid
def ofAddUnits (α: Type u) [AddMonoidOps α] [IsAddMonoid α] : Group (AddUnits α) := Group.ofAdd _

end Group
