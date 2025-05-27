import Math.Data.Encodable.Basic
import Math.Data.Rat.Basic

instance : Encodable Rat.Fract := Encodable.ofEquiv Equiv.fract_equiv_int_pnat
instance : Encodable ℚ := Encodable.ofEquiv Equiv.rat_equiv_reduced_fract
