import Math.Data.Poly.Dvd
import Math.Algebra.Ring.Theory.RMod.Basic

open Poly

namespace RMod

variable [RingOps P] [IsRing P] [IsCommMagma P] [DecidableEq P] [IsNontrivial P] [NoZeroDivisors P]

def modPoly {p: P[X]} (_: IsInvertible (p.toFinsupp p.degreeNat)) : RMod p -> P[X] := by
  apply Quotient.lift (Poly.mod · p)
  intro a b eq
  rw [←div_mul_add_mod a p inferInstance, ←div_mul_add_mod b p inferInstance] at eq
  replace eq : p ∣ _ := eq
  rw [sub_eq_add_neg, neg_add_rev, ←add_assoc, add_assoc (_ * _),
    add_comm_right, ←sub_eq_add_neg, ←sub_eq_add_neg, ←sub_mul] at eq
  replace eq := dvd_add eq (dvd_mul_right p (b.div p - a.div p))
  rw [add_comm_right, ←neg_sub, ←neg_mul_left, neg_add_cancel,
    zero_add] at eq
  have := Poly.eq_zero_of_dvd_of_degree_lt _ _ eq ?_
  apply eq_of_sub_eq_zero
  assumption
  rw [sub_eq_add_neg]
  apply lt_of_le_of_lt
  apply Poly.add_degree
  rw [Poly.neg_degree]
  apply max_lt_iff.mpr
  apply And.intro
  apply mod_degree_lt
  apply mod_degree_lt

def modPoly_degree_lt {p: P[X]} (h: IsInvertible (p.toFinsupp p.degreeNat)) (x: RMod p) : (x.modPoly h).degree < p.degree := by
  induction x with | mk x =>
  apply Poly.mod_degree_lt

def mk_modPoly {p: P[X]} (h: IsInvertible (p.toFinsupp p.degreeNat)) (x: RMod p) : RMod.mk (x.modPoly h) = x := by
  induction x with | mk x =>
  apply Quotient.sound
  show p ∣ Poly.mod x p - x
  rw (occs := [2]) [←Poly.div_mul_add_mod x p h]
  rw [sub_eq_add_neg, neg_add_rev, ←add_assoc, add_neg_cancel, zero_add]
  apply dvd_neg.mp
  apply dvd_mul_right

end RMod
