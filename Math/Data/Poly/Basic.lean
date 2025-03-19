import Math.Data.Poly.Defs
import Math.Algebra.Ring.Char
import Math.Algebra.AddMonoidWithOne.Hom

variable [SemiringOps P] [IsSemiring P]

open Poly

instance [HasChar P n] : HasChar P[X] n := HasChar.of_ring_emb C
