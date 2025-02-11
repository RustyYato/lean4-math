import Math.GroupTheory.Subgroup
import Math.GroupTheory.Units
import Math.Algebra.Impls.Fin

namespace Group

-- the group of units of a Fin
def FinMul : Group (Units (Fin (n + 1))) := ofUnits _

end Group
