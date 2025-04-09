import Math.Algebra.Semifield.Localization.Defs
import Math.Algebra.Ring.Localization.Defs
import Math.Algebra.Field.Defs

namespace Localization

variable {R: Type*} [RingOps R] [IsRing R] [IsCommMagma R] [NoZeroDivisors R]
  [IsNontrivial R]

instance : IsField (Localization (Submonoid.Dividends R)) where

end Localization
