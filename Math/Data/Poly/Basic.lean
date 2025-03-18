import Math.Data.Poly.Defs
import Math.Algebra.Ring.Char
import Math.Algebra.AddMonoidWithOne.Hom

variable [SemiringOps P] [IsSemiring P]

open Poly

instance [HasChar P n] : HasChar P[X] n := by
  apply HasChar.of_natCast_eq_zero
  rw [←resp_natCast (Poly.C (P := P))]
  rw [HasChar.natCast_eq_zero, resp_zero]
  intro m h
  rw [←resp_natCast (Poly.C (P := P)), ←resp_zero (Poly.C (P := P))] at h
  have := C.inj h
  exact HasChar.char_dvd_natCast_eq_zero m this
