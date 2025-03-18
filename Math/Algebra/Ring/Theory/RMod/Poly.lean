import Math.Data.Poly.Dvd
import Math.Algebra.Ring.Theory.RMod.Basic

open Poly

namespace RMod

variable [RingOps P] [IsRing P] [IsCommMagma P] [DecidableEq P] [IsNontrivial P] [NoZeroDivisors P]

def modPoly {p: P[X]} (_: IsInvertible p.lead) : RMod p -> P[X] := by
  apply Quotient.lift (Poly.mod · p)
  intro a b eq
  apply (Poly.mod_eq_iff_sub_dvd _ _).mp
  assumption

def modPoly_degree_lt {p: P[X]} (h: IsInvertible p.lead) (x: RMod p) : (x.modPoly h).degree < p.degree := by
  induction x with | mk x =>
  apply Poly.mod_degree_lt

def algebraMap_modPoly {p: P[X]} (h: IsInvertible p.lead) (x: RMod p) : algebraMap (x.modPoly h) = x := by
  induction x with | mk x =>
  apply Quotient.sound
  show p ∣ Poly.mod x p - x
  rw (occs := [2]) [←Poly.div_mul_add_mod x p h]
  rw [sub_eq_add_neg, neg_add_rev, ←add_assoc, add_neg_cancel, zero_add]
  apply dvd_neg.mp
  apply dvd_mul_right

def modPoly_zero {p: P[X]} (h: IsInvertible p.lead) : (0: RMod p).modPoly h = 0 := by
  show Poly.mod 0 p = 0
  rw [Poly.mod_of_lt]
  apply Poly.deg_nontrivial_of_invertible
  assumption

def modPoly_const {p: P[X]} (h: IsInvertible p.lead) {x: P} (g: .of 0 < p.degree) : modPoly h (algebraMap (A := RMod p) (C x)) = C x := by
  show Poly.mod (C x) p = C x
  rw [Poly.mod_of_lt]
  apply lt_of_le_of_lt _ g
  apply degree_is_minimal
  intro i hi
  match i with
  | n + 1 =>
  rfl

def modPoly_add {p: P[X]} (h: IsInvertible p.lead) (a b: P[X]) : modPoly h (algebraMap (A := RMod p) (a + b)) = modPoly h (algebraMap a) + modPoly h (algebraMap b) := by
  apply Poly.add_mod

end RMod
