import Math.Algebra.Group.Theory.Basic
import Math.Algebra.Impls.Fin
import Math.Algebra.Group.SetLike.Basic
import Math.Order.OrderIso
import Math.Data.Free.Group
import Math.Algebra.GroupQuot
import Math.Data.ZMod.Defs

inductive Cyclic.Rel (n: ℕ) : FreeGroup Unit -> FreeGroup Unit -> Prop where
| intro (a: FreeGroup Unit) : Rel n (a ^ n) 1

-- the cylic group of order `n` is the group with one
-- generator and the relation `a ^ n = 1` for all `a`
def Cyclic (n: ℕ) := GroupQuot (Cyclic.Rel n)

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

def toZMod (n: ℕ) :  Cyclic n →* MulOfAdd (ZMod n) := GroupQuot.lift {
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
        rw [ZMod.n_nsmul_eq_zero]
      | inv _ ih => rw [map_inv, inv_npow, ih, inv_one]
      | mul a b iha ihb => rw [map_mul, mul_npow, iha, ihb, mul_one]
  }

def toZMod_unit : toZMod n (unit n) = MulOfAdd.mk 1 := by
  show GroupQuot.lift _ _ = _
  rw [unit, GroupQuot.lift_mk_apply, FreeGroup.lift_of]

def equiv_zmod_add : Cyclic n ≃* MulOfAdd (ZMod n) := {
  toZMod n with
  invFun x := (unit n) ^ (ZMod.toInt x.get)
  rightInv x := by
    simp
    rw [map_zpow, toZMod_unit, ←MulOfAdd.mk_zsmul]
    cases x with | mk x =>
    congr
    rw [←intCast_eq_zsmul_one]
    show ZMod.ofInt _ _ = _
    rw [ZMod.ofInt_toInt]
    simp
  leftInv x := by
    induction x using GroupQuot.ind with | mk x =>
    simp
    induction x with
    | one => simp [map_one, map_zero, ZMod.toInt_zero]
    | of =>
      rw [←unit]
      simp [toZMod_unit]
      match n with
      | 1 => apply Subsingleton.allEq
      | 0 | n + 2 =>
        show unit _ ^ 1 = _
        rw [zpow_one]
    | inv a ih =>
      rw [map_inv, ←ih, ←unit]
      clear ih
      simp [map_inv, map_zpow, toZMod_unit, ←intCast_eq_zsmul_one]
      rw [ZMod.intCast_toInt]
      match n with
      | 1 => apply Subsingleton.allEq
      | 0 => rw [←zpow_neg]; rfl
       | n + 2 =>
        symm; apply inv_eq_of_mul_left
        rw [←zpow_add]
        rw [ZMod.toInt_neg, zpow_ofNat, npow_n_eq_one]
        symm; apply zero_ne_one
    | mul a b iha ihb =>
      simp [map_mul]
      conv => { rhs; rw [←iha, ←ihb] }
      rw [←zpow_add]
      generalize (toZMod n (GroupQuot.mk _ a)).get = a'
      generalize (toZMod n (GroupQuot.mk _ b)).get = b'
      clear iha ihb a b
      have ⟨k, eq⟩ := ZMod.toInt_add a' b'
      rw [eq.left]
      rw [zpow_sub, zpow_add]
      rcases eq.right with rfl | rfl
      simp
      rw [zpow_ofNat, npow_n_eq_one]
      simp
}

instance : IsCommMagma (Cyclic n) where
  mul_comm a b := by
    apply equiv_zmod_add.inj
    rw [map_mul, map_mul, mul_comm]

end Cyclic
