import Math.Algebra.Group.Theory.Basic
import Math.Algebra.Impls.Fin
import Math.Algebra.Group.SetLike.Basic
import Math.Order.OrderIso
import Math.Data.Free.Group
import Math.Algebra.GroupQuot

inductive Cyclic.Rel (n: ℕ) : FreeGroup Unit -> FreeGroup Unit -> Prop where
| intro (a: FreeGroup Unit) : Rel n (a ^ n) 1

def Cyclic (n: ℕ) := GroupQuot (Cyclic.Rel n)

-- -- the cyclic group of order n
-- instance Cyclic (n: ℕ) [h: NeZero n] : Group (Fin n) := by
--   match n, h with
--   | n + 1, h =>
--   apply Group.ofAdd

namespace Cyclic

variable {n: ℕ}

instance : GroupOps (Cyclic n) := GroupQuot.instGroupOps
instance : IsGroup (Cyclic n) := GroupQuot.instIsGroup

def unit (n: ℕ) : Cyclic n := GroupQuot.mk _ (FreeGroup.of ())

def npow_n_eq_one (a: Cyclic n) : a ^ n = 1 := by
  induction a using GroupQuot.ind with | mk a =>
  rw [←map_one (GroupQuot.mk _), ←map_npow (GroupQuot.mk _)]
  apply GroupQuot.mk_rel
  apply Cyclic.Rel.intro

instance : Subsingleton (Cyclic 1) where
  allEq a b := by rw [←npow_one a, ←npow_one b, npow_n_eq_one, npow_n_eq_one]

def npow_fin_add (a: Cyclic n) (x y: Fin n) : a ^ (x + y).val = a ^ (x.val + y.val) := by
  rw [←one_mul (a ^ (x + y).val), ←npow_n_eq_one (a ^ ((x.val + y.val) / n)),
    ←npow_mul]
  show _ * a ^ (Fin.mk _ _).val = _
  simp
  rw [←npow_add, Nat.div_add_mod]

def toFin [NeZero n] : Cyclic n →* MulOfAdd (Fin n) := GroupQuot.lift {
    val := FreeGroup.lift (fun () => MulOfAdd.mk 1)
    property := by
      intro x y (.intro a)
      rw [map_npow, map_one]
      induction a with
      | one => rw [map_one, one_npow]
      | of x =>
        rw [FreeGroup.lift_of]
        show MulOfAdd.mk (n • 1) = MulOfAdd.mk 0
        congr
        show Fin.mk _ _ = Fin.mk _ _
        congr 1
        simp
      | inv _ ih => rw [map_inv, inv_npow, ih, inv_one]
      | mul a b iha ihb => rw [map_mul, mul_npow, iha, ihb, mul_one]
  }

def toFin_mk_of [NeZero n] (x: Unit) : toFin (n := n) (GroupQuot.mk _ (FreeGroup.of x)) = MulOfAdd.mk 1 := by
  show GroupQuot.lift _ _ = _
  rw [GroupQuot.lift_mk_apply, FreeGroup.lift_of]

def equiv_fin_add [NeZero n] : Cyclic n ≃* MulOfAdd (Fin n) := {
    toFin with
    invFun x := (unit n) ^ x.get.val
    leftInv x := by
      induction x using GroupQuot.ind with | mk x =>
      simp
      induction x with
      | one =>
        rw [map_one, map_one]
        show _ ^ 0 = _
        rw [npow_zero]
      | of a =>
        rw [toFin_mk_of]
        simp
        rename_i h
        match n, h with
        | 1, h => apply Subsingleton.allEq
        | n + 2, h =>
          show _ ^ 1 = _
          rw [npow_one]
          rfl
      | inv a ih =>
        rename_i h
        rw [map_inv, map_inv, toFin_mk_of]
        rw [toFin_mk_of] at ih
        simp at *
        rw [←ih]; clear ih
        match n, h with
        | 1, h => apply Subsingleton.allEq
        | n + 2, h =>
          rw [←zpow_ofNat, ←zpow_ofNat, ←zpow_neg]
          rw (occs := [2]) [←one_mul (unit _ ^ _)]
          rw [←npow_n_eq_one (unit _), ←zpow_ofNat, ←zpow_add]
          congr 1
          simp
          show Nat.cast (Fin.val (Fin.sub _ _)) = _
          unfold Fin.sub
          simp only
          rw [add_zero, Nat.mod_eq_of_lt (a := 1), Nat.mod_eq_of_lt]
          simp; rw [add_assoc]
          congr
          apply Nat.lt_succ_self
          omega
      | mul a b iha ihb =>
        simp [map_mul]
        rw [npow_fin_add, npow_add, iha, ihb]
    rightInv x := by
      simp
      rw [map_npow, unit, toFin_mk_of, ←MulOfAdd.mk_nsmul]
      rw [←natCast_eq_nsmul_one]
      simp
      cases x with | mk x =>
      congr
      simp
      show Fin.mk _ _ = _
      congr; rw [Nat.mod_eq_of_lt x.isLt]
  }

def toInt : Cyclic 0 →* MulOfAdd ℤ := GroupQuot.lift {
    val := FreeGroup.lift (fun () => MulOfAdd.mk 1)
    property := by
      intro x y (.intro a)
      rw [map_npow, map_one]
      induction a with
      | one => rw [map_one, one_npow]
      | of x =>
        rw [FreeGroup.lift_of]
        simp
      | inv _ ih => rw [map_inv, inv_npow, ih, inv_one]
      | mul a b iha ihb => rw [map_mul, mul_npow, iha, ihb, mul_one]
  }

def toInt_mk_of (x: Unit) : toInt (GroupQuot.mk _ (FreeGroup.of x)) = MulOfAdd.mk 1 := by
  show GroupQuot.lift _ _ = _
  rw [GroupQuot.lift_mk_apply, FreeGroup.lift_of]

def equiv_int_add : Cyclic 0 ≃* MulOfAdd ℤ := {
  toInt with
  invFun x := (unit 0) ^ x.get
  rightInv x := by simp [map_zpow, unit, toInt_mk_of, ←MulOfAdd.mk_zsmul]
  leftInv x := by
    induction x using GroupQuot.ind with | mk x =>
    simp
    induction x with
    | one => simp [map_one]
    | of =>
      simp [toInt_mk_of]
      rfl
    | inv a ih =>
      rw [map_inv, ←ih]
      simp [toInt_mk_of, map_inv]
      rw [unit, toInt_mk_of]
      simp
      rw [zpow_neg_one]
    | mul a b iha ihb =>
      simp [map_mul, zpow_add, iha, ihb]
}

end Cyclic
