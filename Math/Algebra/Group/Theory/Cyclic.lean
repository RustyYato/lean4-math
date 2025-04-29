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

def toZMod (n: ℕ) : Cyclic n →ₘ+ ZMod n := GroupQuot.lift_log {
    val := FreeGroup.lift_log (fun () => 1)
    property := by
      intro x y (.intro a)
      rw [map_npow_to_nsmul, map_one_to_zero]
      induction a with
      | one => rw [map_one_to_zero, nsmul_zero]
      | of x =>
        rw [FreeGroup.lift_log_of, ZMod.n_nsmul_eq_zero]
      | inv _ ih => rw [map_inv_to_neg, nsmul_neg, ih, neg_zero]
      | mul a b iha ihb => rw [map_mul_to_add, nsmul_add, iha, ihb, add_zero]
  }

def toZMod_unit : toZMod n (unit n) = 1 := by
  show GroupQuot.lift_log _ _ = _
  rw [unit, GroupQuot.lift_log_mk_apply, FreeGroup.lift_log_of]

def equiv_zmod_add : Cyclic n ≃ₘ+ ZMod n := {
  toZMod n with
  invFun x := (unit n) ^ (ZMod.toInt x)
  rightInv x := by
    simp
    rw [map_zpow_to_zsmul, toZMod_unit, ←intCast_eq_zsmul_one,
      ZMod.intCast_toInt]
  leftInv x := by
    induction x using GroupQuot.ind with | mk x =>
    simp
    induction x with
    | one => simp [map_one, map_one_to_zero]
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
      simp [map_inv_to_neg, map_zpow_to_zsmul, toZMod_unit,
        ←intCast_eq_zsmul_one, map_one_to_zero, ZMod.intCast_toInt]
      match n with
      | 1 => apply Subsingleton.allEq
      | 0 => rw [←zpow_neg]; rfl
       | n + 2 =>
        symm; apply inv_eq_of_mul_left
        rw [←zpow_add]
        rw [ZMod.toInt_neg, zpow_ofNat, npow_n_eq_one]
        symm; apply zero_ne_one
    | mul a b iha ihb =>
      simp [map_mul, map_mul_to_add]
      conv => { rhs; rw [←iha, ←ihb] }
      rw [←zpow_add]
      generalize (toZMod n (GroupQuot.mk _ a)) = a'
      generalize (toZMod n (GroupQuot.mk _ b)) = b'
      clear iha ihb a b
      have ⟨k, eq⟩ := ZMod.toInt_add a' b'
      rw [eq.left]
      rw [zpow_sub, zpow_add]
      rcases eq.right with rfl | rfl
      simp
      rw [zpow_ofNat, npow_n_eq_one]
      simp
}

def equiv_zmod_add_unit : equiv_zmod_add (unit n) = 1 := by apply toZMod_unit

def pow (c: Cyclic n) : ℤ := ZMod.toInt (toZMod _ c)

instance : Repr (Cyclic n) where
  reprPrec c := reprPrec (pow c)

def pow_spec (c: Cyclic n) : unit n ^ pow c = c := equiv_zmod_add.coe_symm _
def pow_one : pow (n := n) 1 = 0 := by
  unfold pow
  rw [map_one_to_zero, ZMod.toInt_zero]
def pow_mul (a b: Cyclic n) : pow (a * b) = (pow a + pow b) % n := by
  cases n with
  | zero =>
    rw [natCast_zero, Int.emod_zero]
    unfold pow
    simp [map_mul_to_add]
    rfl
  | succ n =>
    unfold pow
    simp [map_mul_to_add]
    rfl
def pow_unit : pow (unit n) = 1 % n := by
  unfold pow
  rw [toZMod_unit]
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => rfl

@[cases_eliminator]
def cases {motive: Cyclic n -> Sort*} (pow: ∀m: ℤ, m < n ∨ n = 0 -> motive (unit n ^ m)) (c: Cyclic n) : motive c :=
  c.pow_spec ▸ pow c.pow <| by
    cases n
    right; rfl
    left
    rename_i n
    apply Int.ofNat_lt.mpr
    apply Fin.isLt

def of_npow_eq_one : (unit n) ^ m = 1 ->  n ∣ m := by
  intro h
  have : equiv_zmod_add (unit n ^ m) = 0 := by rw [h, map_one_to_zero]
  rw [map_npow_to_nsmul, equiv_zmod_add_unit] at this
  replace : m • 1 = (0: ZMod _) := this
  apply HasChar.char_dvd_natCast_eq_zero (α := ZMod n)
  rwa [natCast_eq_nsmul_one]

def of_zpow_eq_one (m: ℤ) : (unit n) ^ m = 1 -> Nat.cast n ∣ m := by
  intro h
  have : unit n ^ m.natAbs = 1 := by
    rw [←zpow_ofNat]
    rcases Int.natAbs_eq m  with g | g
    rw [←g, h]
    rw [←neg_neg (Nat.cast m.natAbs), ←g, zpow_neg, h, inv_one]
  have := of_npow_eq_one this
  apply Int.dvd_natAbs.mp
  apply Int.ofNat_dvd.mpr
  assumption

instance : IsCommMagma (Cyclic n) where
  mul_comm a b := by
    rw [←pow_spec a, ←pow_spec b, ←zpow_add, ←zpow_add, Int.add_comm]

private def lift_zpow_mod (G: Type*) [GroupOps G] [IsGroup G] (g: G) (hg: g ^ n = 1) (k: ℤ) :
  g ^ (k % n)  = g ^ k := by
  rw (occs := [2]) [←Int.ediv_add_emod k n]
  rw [zpow_add , mul_comm (Nat.cast n), zpow_mul, zpow_ofNat, hg, one_zpow, one_mul]

private def preLift (G: Type*) [GroupOps G] [IsGroup G] (g: G) (hg: g ^ n = 1) : Cyclic n →* G where
  toFun n := g ^ n.pow
  map_one := by rw [pow_one, zpow_zero]
  map_mul {x y} := by
    rw [pow_mul, ←zpow_add, lift_zpow_mod]
    assumption

def lift {G: Type*} [GroupOps G] [IsGroup G] : { g: G // g ^ n = 1 } ≃ (Cyclic n →* G) := {
  toFun g := preLift G g.val g.property
  invFun f := {
    val := f (unit _)
    property := by rw [←map_npow, npow_n_eq_one, map_one]
  }
  leftInv x := by
    simp
    congr
    show x.val ^ (unit n).pow = x.val
    rw [pow_unit, lift_zpow_mod, zpow_one]
    exact x.property
  rightInv f := by
    ext x
    simp
    show (f (unit n)) ^ x.pow = f x
    rw (occs := [2]) [←pow_spec x]
    rw [map_zpow]
}

def lift_unit [GroupOps G] [IsGroup G] (g: {g : G // g ^ n = 1}) : lift g (unit n) = g := by
  show g.val ^ (unit n).pow = _
  rw [pow_unit, lift_zpow_mod, zpow_one]
  exact g.property

def npow_congr (x y: ℤ) (a: Cyclic n) : x % n = y % n -> a ^ x = a ^ y := by
  intro h
  rw [←Int.ediv_add_emod x n, ←Int.ediv_add_emod y n,
    zpow_add, zpow_add, h]
  congr 1
  rw [mul_comm, zpow_mul, mul_comm, zpow_mul,
    zpow_ofNat, npow_n_eq_one, one_zpow, one_zpow]

def equiv_cyclic_iff_generated_by_unit (G: Type*) [GroupOps G] [IsGroup G] :
  (∃u: G, ∀g: G, ∃n: ℤ, g = u ^ n) ↔ ∃n, Nonempty (G ≃* Cyclic n) := by
  apply Iff.intro
  · intro ⟨u, hu⟩
    let n := char (AddOfMul G)
    have n_spec : ∀g: G, g ^ n = 1 := char_spec (AddOfMul G)
    have n_dvd : ∀m, (∀g: G, g ^ m = 1) -> n ∣ m := char_dvd (AddOfMul G)
    have ⟨f, hf⟩ := Classical.axiomOfChoice hu; clear hu
    exists n
    let toG : Cyclic n →* G := Cyclic.lift {
      val := u
      property := n_spec _
    }
    refine ⟨?_⟩; apply GroupEquiv.symm
    refine { toG with invFun := fun g => (unit _) ^ f g, leftInv := ?_, rightInv := ?_ }
    · intro x
      simp
      cases x with | pow m hm =>
      rw [map_zpow, lift_unit]
      simp
      apply npow_congr
      have := hf (u ^ m)
      sorry
    · intro g
      simp
      rw [map_zpow, lift_unit]
      simp; rw [←hf]
  · intro ⟨n, ⟨hn⟩⟩
    exists (hn.symm (unit n))
    intro g
    cases h:hn g with | _ m hm =>
    exists m
    rw [←map_zpow, ←h, GroupEquiv.coe_symm]

def subgroup_cyclic (s: Subgroup (Cyclic n)) : ∃m: ℕ, Nonempty (s ≃* Cyclic m) := by
  classical
  let m := char (AddOfMul s)
  have m_spec : ∀x: s, x ^ m = 1 := char_spec (AddOfMul s)
  have m_dvd : ∀k, (∀x: s, x ^ k = 1) -> m ∣ k := char_dvd (AddOfMul s)
  exists m
  let u := (equiv_zmod_add (n := n)).symm (n - m)
  have : ∀x: Cyclic n, x ^ m = 1 -> x ∈ s := by
    intro x hx
    rw [←pow_spec x, ←zpow_ofNat, ←zpow_mul] at hx
    have := of_zpow_eq_one (n := n) _ hx


    sorry
  have : u ∈ s := by
    sorry
  -- have u : ∃u: s, ∀ := sorry
  sorry
  -- match n with
  -- | 0 =>
  --   rcases subsingleton_or_nontrivial s with sub | nontriv
  --   exists 1
  --   exact ⟨{
  --     toFun _ := 1
  --     invFun _ := 1
  --     leftInv _ := Subsingleton.allEq _ _
  --     rightInv _ := Subsingleton.allEq _ _
  --     map_one := Subsingleton.allEq _ _
  --     map_mul {_ _} := Subsingleton.allEq _ _
  --   }⟩
  --   exists 0
  --   have ⟨a, ha⟩ := exists_ne (α := s) 1
  --   have exists_card : ∃m: ℕ, Nat.cast m ∣ (equiv_int_add a.val).get := by
  --     exists (equiv_int_add a.val).get.natAbs
  --     apply Int.natAbs_dvd.mpr
  --     apply Int.dvd_refl
  --   let m := Nat.findP exists_card
  --   let m_spec := Nat.findP_spec exists_card
  --   let m_smallest := Nat.lt_findP_spec exists_card



  --   sorry
  -- | n + 1 =>
  -- have exists_card : ∃m: ℕ, (∀x: s, x ^ m = 1) ∧ (0 < m) := by
  --   exists n + 1
  --   apply And.intro
  --   intro x
  --   apply Subtype.val_inj
  --   simp
  --   rw [npow_n_eq_one]
  --   apply Nat.zero_lt_succ
  -- let m := Nat.findP exists_card
  -- let m_spec := Nat.findP_spec exists_card
  -- let m_smallest := Nat.lt_findP_spec exists_card
  -- -- match m with
  -- -- | 0 => sorry
  -- exists m
  -- sorry

end Cyclic
