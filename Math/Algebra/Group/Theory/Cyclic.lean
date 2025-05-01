import Math.Algebra.Group.Theory.Basic
import Math.Algebra.Group.SetLike.Basic
import Math.Algebra.Group.Impls.Prod
import Math.Algebra.Group.Impls.Fin
import Math.Order.OrderIso
import Math.Data.Free.Group
import Math.Algebra.GroupQuot
import Math.Data.ZMod.Defs
import Math.Relation.Basic
import Math.Data.Int.Gcd

inductive Cyclic.Rel (n: ℕ) : FreeGroup Unit -> FreeGroup Unit -> Prop where
| intro (a: FreeGroup Unit) : Rel n (a ^ n) 1

-- the cylic group of order `n` is the group with one
-- generator and the relation `a ^ n = 1` for all `a`
def Cyclic (n: ℕ) := GroupQuot (Cyclic.Rel n)

class IsGroup.IsCyclic (G: Type*) [GroupOps G] extends IsGroup G where
  exists_generator: ∃u: G, ∀g: G, ∃n: ℤ, g = u ^ n

class IsAddGroup.IsCyclic (G: Type*) [AddGroupOps G] extends IsAddGroup G where
  exists_generator: ∃u: G, ∀g: G, ∃n: ℤ, g = n • u

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

def npow_emod (a: Cyclic n) (k: ℤ) : a ^ (k % n) = a ^ k := by
  rw (occs := [2]) [←Int.ediv_add_emod k n]
  rw [zpow_add, zpow_mul, zpow_ofNat, npow_n_eq_one, one_mul]

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

def ofZMod (n: ℕ) : ZMod n →ₐ* Cyclic n := ZMod.lift_exp n {
  val := {
    toFun x := unit n ^ x
    map_zero_to_one := by simp
    map_add_to_mul {a b} := by rw [zpow_add]

  }
  property := by apply npow_n_eq_one
}

def toZMod_unit : toZMod n (unit n) = 1 := by
  show GroupQuot.lift_log _ _ = _
  rw [unit, GroupQuot.lift_log_mk_apply, FreeGroup.lift_log_of]

def apply_ofZMod (n: ℕ) (x: ZMod n) : ofZMod n x = unit n ^ ZMod.toInt x := by
  rw [ofZMod, ZMod.apply_lift_exp]
  rfl

def toZMod_ofZMod (n: ℕ) (c: ZMod n) : toZMod n (ofZMod n c) = c := by
  rw [apply_ofZMod, map_zpow_to_zsmul, toZMod_unit, smul_one]
  apply ZMod.ofInt_toInt

def ofZMod_toZMod (n: ℕ) (c: Cyclic n) : ofZMod n (toZMod n c) = c := by
  induction c using GroupQuot.ind with | mk c =>
  induction c with
  | one => simp [map_one, map_one_to_zero, map_zero_to_one]
  | of => rw [←unit, toZMod_unit, apply_ofZMod, ←map_one (ZMod.ofInt n),
      ZMod.toInt_ofInt, npow_emod, zpow_one]
  | inv a ih => rw [map_inv, map_inv_to_neg, map_neg_to_inv, ih]
  | mul a b iha ihb => rw [map_mul, map_mul_to_add, map_add_to_mul, iha, ihb]

def pow (c: Cyclic n) : ℤ := ZMod.toInt (toZMod _ c)

instance : Repr (Cyclic n) where
  reprPrec c := reprPrec (pow c)

def pow_spec (c: Cyclic n) : unit n ^ pow c = c := by
  unfold pow
  suffices ofZMod n (toZMod n c) = c by
    rw [ofZMod, ZMod.apply_lift_exp] at this
    assumption
  apply ofZMod_toZMod

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

def equiv_zmod_add : Cyclic n ≃ₘ+ ZMod n := {
  toZMod n with
  invFun := ofZMod n
  rightInv := toZMod_ofZMod n
  leftInv := ofZMod_toZMod n
}

def equiv_zmod_add_unit : equiv_zmod_add (unit n) = 1 := by apply toZMod_unit

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

def lift_log {G: Type*} [AddGroupOps G] [IsAddGroup G] : { g: G // n • g = 0 } ≃ (Cyclic n →ₘ+ G) :=
  Equiv.trans (lift (G := MulOfAdd G)) <| Equiv.log_hom_equiv_group_hom.symm

def lift_unit [GroupOps G] [IsGroup G] (g: {g : G // g ^ n = 1}) : lift g (unit n) = g := by
  show g.val ^ (unit n).pow = _
  rw [pow_unit, lift_zpow_mod, zpow_one]
  exact g.property

def lift_log_unit [AddGroupOps G] [IsAddGroup G] (g: {g : G // n • g = 0}) : lift_log g (unit n) = g :=
  lift_unit (G := MulOfAdd G) _

def npow_congr (x y: ℤ) (a: Cyclic n) : x % n = y % n -> a ^ x = a ^ y := by
  intro h
  rw [←Int.ediv_add_emod x n, ←Int.ediv_add_emod y n,
    zpow_add, zpow_add, h]
  congr 1
  rw [mul_comm, zpow_mul, mul_comm, zpow_mul,
    zpow_ofNat, npow_n_eq_one, one_zpow, one_zpow]

def equiv_cyclic_iff_generated_by_unit (G: Type*) [GroupOps G] [IsGroup G] : (∃u: G, ∀g: G, ∃n: ℤ, g = u ^ n) ↔ ∃n, Nonempty (G ≃* Cyclic n) := by
  classical
  apply Iff.intro
  · intro ⟨u, hu⟩
    refine if ueq:u = 1 then ?_ else ?_
    · subst u
      simp at hu
      exists 1
      refine ⟨{
        toFun _ := 1
        invFun _ := 1
        leftInv x := by
          dsimp
          symm; apply hu
        rightInv _ := Subsingleton.allEq _ _
        map_one := rfl
        map_mul {_ _} := by rw [mul_one]
      }⟩
    let n := char (AddOfMul G)
    have n_spec : ∀g: G, g ^ n = 1 := char_spec (AddOfMul G)
    have n_dvd : ∀m, (∀g: G, g ^ m = 1) -> n ∣ m := char_dvd (AddOfMul G)
    replace hu (g: G) : ∃n: ℤ, g = u ^ n ∧ ∀m: ℤ, g = u ^ m -> n.natAbs ≤ m.natAbs := by
      have ⟨k, geq, hk⟩ := Relation.exists_min Int.abs_lt (hu g)
      exists k
      apply And.intro
      assumption
      intro m hm
      have : ¬m.natAbs < k.natAbs := (hk m · hm)
      simpa using this
    have ⟨f, hf⟩ := Classical.axiomOfChoice hu; clear hu

    have f_inj : Function.Injective f := by
      intro x y h
      rw [(hf x).left, (hf y).left, h]

    let f' : ZMod n →ₐ* G := {
      toFun i := u ^ ZMod.toInt i
      map_zero_to_one := by simp
      map_add_to_mul {a b} := by
        have ⟨k, eq, hk⟩ := ZMod.toInt_add a b
        rw [eq, zpow_sub, zpow_add]
        rcases hk with rfl | rfl
        simp
        rw [zpow_ofNat, n_spec, div_one]
    }
    have f'_surj : Function.Surjective f' := by
      intro x
      exists f x
      show x = u ^ ZMod.toInt (f x)
      rw [ZMod.toInt_intCast]
      rw [←one_mul (u ^ _), ←one_zpow (f x / n), ←n_spec u, ←zpow_ofNat, ←zpow_mul, ←zpow_add,
        Int.mul_comm, Int.ediv_add_emod, ←(hf _).left]
    have f'_inj : Function.Injective f' := by
      suffices ∀(i: ZMod n), u ^ (ZMod.toInt i) = 1 -> i = 0 by
        intro x y h
        replace h : f' x / f' y = 1 := by rw [h, div_self]
        rw [←map_sub_to_div] at h
        replace h : u ^ (ZMod.toInt (x - y)) = 1 := h
        apply eq_of_sub_eq_zero
        exact this (x - y) h
      intro i h
      have := n_dvd (ZMod.toInt i).natAbs ?_
      · apply Decidable.byContradiction
        intro inz
        have n_le_i := Nat.le_of_dvd ?_ this
        match hn:n with
        | 0 =>
          rw (occs := [1]) [hn] at this
          simp at this
          have := ZMod.toInt_eq_zero this
          contradiction
        | n' + 1 =>
          rw (occs := [1]) [hn] at this
          have := ZMod.toInt_natAbs_lt_n i (by rw [hn]; nofun)
          rw [←Int.ofNat_le] at n_le_i
          replace := Int.lt_of_lt_of_le this n_le_i
          rcases Int.natAbs_eq (ZMod.toInt i) with h' | h'
          rw [←h'] at this
          exact Int.lt_irrefl _ this
          rw [←neg_neg (Nat.cast _), ←h'] at this
          replace : ZMod.toInt i < 0 := by omega
          rw [←Int.not_le] at this
          refine this (ZMod.toInt_nonneg i ?_)
          rw [hn]; nofun
        apply Nat.zero_lt_of_ne_zero
        intro h
        rw [Int.natAbs_eq_zero] at h
        have := ZMod.toInt_eq_zero h
        contradiction
      · intro g
        rw [(hf g).left, ←zpow_ofNat, ←zpow_mul, mul_comm, zpow_mul]
        rcases Int.natAbs_eq (ZMod.toInt i) with h' | h'
        rw [←h', h, one_zpow]
        rw [←neg_neg (Nat.cast _), ←h', zpow_neg, h, inv_one, one_zpow]

    have ⟨eqv, heqv⟩ := Equiv.ofBij ⟨f'_inj, f'_surj⟩
    exists n
    refine ⟨?_⟩
    apply GroupEquiv.of_log_exp (β := ZMod n) _ equiv_zmod_add.symm
    exact ExpEquiv.symm {
      eqv with
      map_add_to_mul := by simp [heqv, map_add_to_mul]
      map_zero_to_one := by simp [heqv, map_zero_to_one]
    }
  · intro ⟨n, ⟨hn⟩⟩
    exists (hn.symm (unit n))
    intro g
    cases h:hn g with | _ m hm =>
    exists m
    rw [←map_zpow, ←h, GroupEquiv.coe_symm]

def subgroup_cyclic (s: Subgroup (Cyclic n)) : ∃m: ℕ, Nonempty (s ≃* Cyclic m) := by
  classical
  rw [←equiv_cyclic_iff_generated_by_unit]
  rcases subsingleton_or_nontrivial s with hs | hs
  exists 1
  intro x; exists 0
  apply Subsingleton.allEq
  have ⟨⟨x, hx⟩, x_ne_one⟩ := exists_ne (1: s)
  cases x with | pow i hi' =>
  have i_ne_zero : i ≠ 0 := by
    rintro rfl; simp at x_ne_one
    contradiction
  have n_not_dvd_i : ¬(n: ℤ) ∣ i := by
    rintro ⟨k, rfl⟩
    apply x_ne_one
    congr
    rw [zpow_mul, zpow_ofNat, npow_n_eq_one]
  have m_exists : ∃i: ℕ, unit n ^ i ∈ s ∧ 0 < i := ⟨i.natAbs, by
    apply And.intro
    apply mem_npow_natAbs_of_mem_zpow
    assumption
    omega⟩
  let m := Nat.findP m_exists
  let m_spec : unit n ^ m ∈ s := (Nat.findP_spec m_exists).left
  let m_pos : 0 < m := (Nat.findP_spec m_exists).right
  let lt_m_spec : ∀i, i < m -> _ := Nat.lt_findP_spec m_exists
  simp at lt_m_spec
  let u : s := ⟨unit n ^ m, m_spec⟩
  exists u
  intro ⟨g, hg⟩
  cases g with | pow g hg' =>
  simp [u]
  suffices (m: ℤ) ∣ g by
    obtain ⟨k, rfl⟩ := this
    exists k
    congr 1
    rw [mul_comm, zpow_mul, zpow_ofNat]
  clear hg'
  induction g using Relation.wfInduction Int.abs_lt with
  | h g ih =>
  have : unit n ^ (Int.gcd g m) ∈ s := by
    rw [←zpow_ofNat, Int.gcd_eq_gcd_ab, zpow_add]
    apply mem_mul
    rw [mul_comm, zpow_mul]
    apply mem_zpow
    assumption
    rw [mul_comm, zpow_mul]
    apply mem_zpow
    assumption
  refine if hg':g.gcd m < g.natAbs then ?_ else ?_
  replace this := ih (g.gcd m) hg' this
  apply Int.dvd_trans
  assumption
  apply Int.gcd_dvd_left
  simp at hg'
  have : g.gcd m ∣ g.natAbs := by apply Nat.gcd_dvd_left
  refine if hg₁:g = 0 then ?_ else ?_
  rw [hg₁]; apply Int.dvd_zero
  replace :=  Nat.le_antisymm (Nat.dvd_le _ _ this (by omega)) hg'
  have : g ∣ m := by
    apply Int.natAbs_dvd.mp
    rw [←this]
    apply Int.ofNat_dvd.mpr
    apply Nat.gcd_dvd_right
  rw [←Int.natAbs_dvd, Int.ofNat_dvd] at this
  have gnatabs_le_m := Nat.le_of_dvd m_pos this
  rcases Nat.lt_or_eq_of_le gnatabs_le_m with g_lt_m | g_eq_m
  · have := lt_m_spec g.natAbs g_lt_m (by
      apply mem_npow_natAbs_of_mem_zpow
      assumption)
    rw [Int.natAbs_eq_zero] at this
    subst g
    apply Int.dvd_zero
  · rw [←g_eq_m]
    exact Int.natAbs_dvd_self

attribute [irreducible] lift lift_log instGroupOps Cyclic

def equiv_prod (n m: ℕ) (h: Nat.gcd n m = 1) : Cyclic (n * m) ≃* Cyclic n × Cyclic m := by
  apply GroupEquiv.of_log_exp equiv_zmod_add
  apply ExpEquiv.add_trans (ZMod.equiv_prod _ _ h)
  apply ExpEquiv.congrProd
  exact equiv_zmod_add.symm
  exact equiv_zmod_add.symm

end Cyclic

instance [GroupOps G] [h: IsGroup.IsCyclic G] : IsAddGroup.IsCyclic (AddOfMul G) where
  exists_generator := h.exists_generator
instance [AddGroupOps G] [h: IsAddGroup.IsCyclic G] : IsGroup.IsCyclic (MulOfAdd G) where
  exists_generator := h.exists_generator

def IsGroup.IsCyclic.existsEquivCyclic (G: Type*) [GroupOps G] [h: IsCyclic G] : ∃n, Nonempty (G ≃* Cyclic n) := by
  rw [←Cyclic.equiv_cyclic_iff_generated_by_unit]
  exact h.exists_generator

def IsAddGroup.IsCyclic.existsEquivCyclic (G: Type*) [AddGroupOps G] [IsCyclic G] : ∃n, Nonempty (G ≃ₐ* Cyclic n) := by
  have ⟨n, ⟨h⟩⟩ := IsGroup.IsCyclic.existsEquivCyclic (MulOfAdd G)
  refine ⟨n, ⟨?_⟩⟩
  apply ExpEquiv.trans_mul (ExpEquiv.MulOfAdd G) h

namespace IsGroup.IsCyclic

def exists_minimal_generator (G: Type*) [GroupOps G] [IsCyclic G] :
  ∃u: G, ∀g: G, ∃n: ℤ, g = u ^ n ∧ ∀m: ℤ, g = u ^ m -> n.natAbs ≤ m.natAbs := by
  have ⟨u, hu⟩ := exists_generator (G := G)
  exists u; intro g
  have ⟨k, geq, hk⟩ := Relation.exists_min Int.abs_lt (hu g)
  exists k
  apply And.intro
  assumption
  intro m hm
  have : ¬m.natAbs < k.natAbs := (hk m · hm)
  simpa using this

def ofEmbedding [GroupOps A] [IsGroup A] [GroupOps B] [IsCyclic B] (h: A ↪* B) : IsCyclic A where
  exists_generator := by
    have ⟨n, ⟨g⟩⟩ := existsEquivCyclic B
    replace h := h.trans g.toEmbedding
    replace g := Subgroup.equiv_of_embed h
    have ⟨m, ⟨g'⟩⟩ := Cyclic.subgroup_cyclic (Subgroup.of_hom h.toHom)
    replace g := g.trans g'
    exists g.symm (.unit _)
    intro a
    exists (g a).pow
    rw [←map_zpow, Cyclic.pow_spec, g.coe_symm]

def ofLogEmbedding [GroupOps A] [IsGroup A] [AddGroupOps B] [IsAddGroup.IsCyclic B] (h: A ↪ₘ+ B) : IsCyclic A := by
  apply ofEmbedding (B := MulOfAdd B)
  apply GroupEmbedding.of_log_exp h (ExpEquiv.MulOfAdd _).toEmbedding

end IsGroup.IsCyclic

namespace IsAddGroup.IsCyclic

def exists_minimal_generator (G: Type*) [AddGroupOps G] [IsCyclic G] :
  ∃u: G, ∀g: G, ∃n: ℤ, g = n • u ∧ ∀m: ℤ, g = m • u -> n.natAbs ≤ m.natAbs :=
  IsGroup.IsCyclic.exists_minimal_generator (MulOfAdd G)

def ofEmbedding [AddGroupOps A] [IsAddGroup A] [AddGroupOps B] [IsCyclic B] (h: A ↪+ B) : IsCyclic A := by
  suffices IsGroup.IsCyclic (MulOfAdd A) by
    show IsCyclic (AddOfMul (MulOfAdd A))
    infer_instance
  apply IsGroup.IsCyclic.ofLogEmbedding (B := B)
  apply LogEmbedding.trans_add _ h
  refine (LogEquiv.MulOfAdd A).toEmbedding

def ofLogEmbedding [AddGroupOps A] [IsAddGroup A] [GroupOps B] [IsGroup.IsCyclic B] (h: A ↪ₐ* B) : IsCyclic A := by
  apply ofEmbedding (B := AddOfMul B)
  apply AddGroupEmbedding.of_exp_log h (LogEquiv.AddOfMul _).toEmbedding

end IsAddGroup.IsCyclic

instance : IsGroup.IsCyclic (Cyclic n) where
  exists_generator := by
    exists .unit n
    intro g
    cases g with | _ i =>
    exists i

instance : IsAddGroup.IsCyclic (ZMod n) :=
  IsAddGroup.IsCyclic.ofLogEmbedding Cyclic.equiv_zmod_add.symm.toEmbedding

namespace Cyclic

-- def coprime_of_eqv_prod (n m: ℕ) (h: Cyclic (n * m) ≃* Cyclic n × Cyclic m) : Nat.gcd n m = 1 := by
--   have : IsGroup.IsCyclic (Cyclic n × Cyclic m) := IsGroup.IsCyclic.ofEmbedding h.symm.toEmbedding
--   have zmod_prod_cyclic := IsAddGroup.IsCyclic.ofLogEmbedding (A := ZMod n × ZMod m) (B := Cyclic n × Cyclic m) (by
--     apply ExpEquiv.toEmbedding
--     refine ExpEquiv.congrProd ?_ ?_
--     exact equiv_zmod_add.symm
--     exact equiv_zmod_add.symm)

--   match g:Nat.gcd n m with
--   | 1 => rfl
--   | 0 =>
--     -- obtain ⟨rfl, rfl⟩ := Nat.gcd_eq_zero_iff.mp g
--     -- simp at h
--     -- exfalso
--     -- replace ⟨⟨u, v⟩, h⟩ := zmod_prod_cyclic.exists_minimal_generator
--     -- have ⟨x, hx, xmin⟩ := h (1, 0)
--     -- have ⟨y, hy, ymin⟩ := h (0, 1)
--     -- have ⟨hx₀, hx₁⟩ := Prod.mk.inj hx
--     -- have ⟨hy₀, hy₁⟩ := Prod.mk.inj hy
--     -- clear g hx hy; simp at *
--     -- cases of_mul_eq_zero hx₁.symm
--     -- subst x; simp at hx₀; exact zero_ne_one _ hx₀.symm
--     -- subst v; simp at hy₁; exact zero_ne_one _ hy₁.symm
--     sorry
--   | k + 2 =>
--     exfalso
--     replace g : _ = k + 2 := g
--     have k_dvd_n : k + 2 ∣ n := by rw [←g]; apply Nat.gcd_dvd_left
--     have k_dvd_m : k + 2 ∣ m := by rw [←g]; apply Nat.gcd_dvd_right
--     obtain ⟨q₀, rfl⟩ := k_dvd_n
--     obtain ⟨q₁, rfl⟩ := k_dvd_m
--     replace g : q₀.gcd q₁ = 1 := by
--       rw [Nat.gcd_mul_left, ←mul_one  (k + 2), mul_assoc, one_mul] at g
--       refine mul_left_cancel₀ ?_ g
--       omega
--     replace ⟨⟨u, v⟩, h⟩ := zmod_prod_cyclic.exists_minimal_generator
--     have ⟨x, hx, xmin⟩ := h (1, 0)
--     have ⟨y, hy, ymin⟩ := h (0, 1)
--     simp only [ZMod.toInt_zero, ZMod.toInt_eq_zero] at hx hy
--     have ⟨hx₀, hx₁⟩ := Prod.mk.inj hx
--     have ⟨hy₀, hy₁⟩ := Prod.mk.inj hy
--     clear h
--     clear hx hy; simp at *
--     induction u with | ofInt u =>
--     induction v with | ofInt v =>
--     rw [smul_def, ←map_algebraMap ((ZMod.ofInt ((k + 2) * _))), ←map_mul, algebraMap_id] at hx₀ hx₁ hy₀ hy₁

--     sorry

end Cyclic
