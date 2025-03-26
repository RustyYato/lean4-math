import Math.Algebra.Impls.Fin
import Math.Algebra.Ring.Theory.Ideal.TwoSided.Quotient
import Math.Data.Quotient.Basic
import Math.Order.Fin
import Math.Order.OrderIso
import Math.Algebra.AddGroupWithOne.Hom
import Math.Algebra.Semiring.Char
import Math.Algebra.Ring.Basic

-- the multiplies of n, as an ideal over the integers
def Int.multiples (n: ℕ) : Ideal ℤ where
  carrier := Set.mk fun x => (n: ℤ) ∣ x
  mem_zero' := by exists 0
  mem_neg' := by
    intro x hx
    apply Int.dvd_neg.mpr
    assumption
  mem_add' := by
    intro x y hx hy
    apply Int.dvd_add <;> assumption
  mem_mul_left' := by
    intro r x hx
    apply Int.dvd_trans
    assumption
    apply Int.dvd_mul_left
  mem_mul_right' := by
    intro r x hx
    apply Int.dvd_trans
    assumption
    apply Int.dvd_mul_right

def ZMod (n: ℕ): Type := (Int.multiples n).toRing

instance : RingOps (ZMod n) := inferInstanceAs (RingOps (Int.multiples n).toRing)
instance : IsRing (ZMod n) := inferInstanceAs (IsRing (Int.multiples n).toRing)

def zmod_zero_eqv_int : ZMod 0 ≃+* ℤ :=
  flip RingEquiv.trans (Ideal.eqv_quot_empty (R := ℤ)).symm <| Ideal.toRing_eqv_toRing_of_eq <| by
    ext x
    apply Iff.intro
    intro h
    cases Int.zero_dvd.mp h
    rfl
    rintro rfl
    apply Int.dvd_refl

private def int_dvd_emod_sub (n x: Int) : n ∣ (x % n) - x := by
  conv => { rhs; rhs; rw [←Int.ediv_add_emod x n] }
  rw [sub_eq_add_neg, neg_add_rev, ←add_assoc, add_neg_cancel, zero_add]
  apply Int.dvd_neg.mpr
  apply Int.dvd_mul_right

def zmod_succ_eqv_fin (n: Nat) [h: NeZero n] : ZMod n ≃+* Fin n :=
  RingEquiv.symm <| {
    toFun x := x.val
    invFun x := by
      have n_ne_zero : n ≠ 0 := Ne.symm (NeZero.ne' n)
      apply x.lift (fun x: ℤ => Fin.mk (x % n).toNat (by
        refine (Int.toNat_lt ?_).mpr ?_
        refine Int.emod_nonneg x ?_
        omega
        refine Int.emod_lt_of_pos x ?_
        omega))
      intro a b eqv
      apply Fin.val_inj.mp
      apply Int.ofNat.inj
      show ((a % ↑n).toNat: ℤ) = ↑(b % ↑n).toNat
      rw [Int.toNat_of_nonneg, Int.toNat_of_nonneg]
      · have dvd: ↑n ∣ a - b := eqv
        obtain ⟨k, eq⟩ := dvd
        replace eq : a = n * k + b := by rw [←eq, sub_add_cancel]
        subst eq
        rw [Int.add_emod, Int.mul_emod_right, Int.zero_add,
          Int.emod_emod]
      · refine Int.emod_nonneg b ?_
        omega
      · refine Int.emod_nonneg a ?_
        omega
    leftInv := by
      intro x
      simp
      apply Fin.val_inj.mp
      let mkQuot : ℤ →+* ZMod n := (Int.multiples n).mkQuot
      rw [←resp_natCast mkQuot]
      show Int.toNat ((x.val: ℤ) % n) = x.val
      apply Int.ofNat.inj
      rw [Int.ofNat_eq_coe, Int.ofNat_eq_coe, Int.toNat_of_nonneg]
      rw [←Int.ofNat_emod, Nat.mod_eq_of_lt]
      exact x.isLt
      apply Int.emod_nonneg
      have := h.out
      omega
    rightInv := by
      intro x
      obtain ⟨x, rfl⟩ := (Int.multiples n).mkQuot_surj x
      dsimp
      let mkQuot : ℤ →+* ZMod n := (Int.multiples n).mkQuot
      rw [←resp_natCast mkQuot]
      apply Quotient.sound
      show (n: ℤ) ∣ ↑(x % ↑n).toNat - x
      rw [Int.toNat_of_nonneg]
      apply int_dvd_emod_sub
      refine Int.emod_nonneg x ?_
      have := h.out
      omega
    resp_zero' := rfl
    resp_one' := by
      match n, h with
      | 1, h =>
        apply Quotient.sound
        apply Int.one_dvd
      | n + 2, h => rfl
    resp_add' {x y} := by
      show (((x.val + y.val) % n): ZMod n) = (x.val: ZMod n) + (y.val: ZMod n)
      rw [←natCast_add]
      let mkQuot : ℤ →+* ZMod n := (Int.multiples n).mkQuot
      rw [←resp_natCast mkQuot, ←resp_natCast mkQuot]
      apply Quotient.sound
      show (n: ℤ) ∣ _
      rw [Int.ofNat_emod]
      apply int_dvd_emod_sub
    resp_mul' {x y} := by
      show (((x.val * y.val) % n): ZMod n) = (x.val: ZMod n) * (y.val: ZMod n)
      rw [←natCast_mul]
      let mkQuot : ℤ →+* ZMod n := (Int.multiples n).mkQuot
      rw [←resp_natCast mkQuot, ←resp_natCast mkQuot]
      apply Quotient.sound
      show (n: ℤ) ∣ _
      rw [Int.ofNat_emod]
      apply int_dvd_emod_sub
  }

instance : IsCommMagma (ZMod n) where
  mul_comm := by
    intro a b; cases n
    apply zmod_zero_eqv_int.inj
    show zmod_zero_eqv_int _ = zmod_zero_eqv_int _
    rw [resp_mul, resp_mul, mul_comm]
    apply (zmod_succ_eqv_fin _).inj
    show zmod_succ_eqv_fin _ _ = zmod_succ_eqv_fin _ _
    rw [resp_mul, resp_mul, mul_comm]

instance : DecidableEq (ZMod n) :=
  match n with
  | 0 => zmod_zero_eqv_int.toEmbedding.DecidableEq
  | _ + 1 => (zmod_succ_eqv_fin _).toEmbedding.DecidableEq

instance : LE (ZMod n) where
  le a b :=
    match n with
    | 0 => zmod_zero_eqv_int a ≤ zmod_zero_eqv_int b
    | _ + 1 => zmod_succ_eqv_fin _ a ≤ zmod_succ_eqv_fin _ b

instance : LT (ZMod n) where
  lt a b :=
    match n with
    | 0 => zmod_zero_eqv_int a < zmod_zero_eqv_int b
    | _ + 1 => zmod_succ_eqv_fin _ a < zmod_succ_eqv_fin _ b

def zmod_zero_oeqv_int : ZMod 0 ≃o Int where
  toEquiv := zmod_zero_eqv_int.toEquiv
  resp_rel := Iff.rfl

def zmod_succ_oeqv_fin (n: Nat) [h: NeZero n] : ZMod n ≃o Fin n where
  toEquiv := (zmod_succ_eqv_fin n).toEquiv
  resp_rel := match n, h with
    | _ + 1, _ => Iff.rfl

instance : Max (ZMod n) :=
  match n with
  | 0 => zmod_zero_oeqv_int.instMax
  | _ + 1  => (zmod_succ_oeqv_fin (_ + 1)).instMax
instance : Min (ZMod n) :=
  match n with
  | 0 => zmod_zero_oeqv_int.instMin
  | _ + 1  => (zmod_succ_oeqv_fin (_ + 1)).instMin

instance : IsLawfulLT (ZMod n) where
  lt_iff_le_and_not_le {a} :=
    match n with
    | 0 => lt_iff_le_and_not_le (a := zmod_zero_oeqv_int a)
    | _ + 1 => lt_iff_le_and_not_le (a := zmod_succ_oeqv_fin _ a)

instance : IsDecidableLinearOrder (ZMod n) :=
  match n with
  | 0 => zmod_zero_oeqv_int.instIsDecidableLinearOrder (fun _ _ => rfl) (fun _ _ => rfl)
  | _ + 1  => (zmod_succ_oeqv_fin (_ + 1)).instIsDecidableLinearOrder (fun _ _ => rfl) (fun _ _ => rfl)

namespace ZMod

def toInt (x: ZMod n): Int :=
  match n with
  | 0 => (zmod_zero_eqv_int x)
  | _ + 1 => (zmod_succ_eqv_fin _ x)

instance : Repr (ZMod n) where
  reprPrec x := reprPrec (toInt x)

instance : HasChar (ZMod n) n :=
  match n with
  | 0 => HasChar.of_ring_equiv zmod_zero_eqv_int
  | _ + 1 => HasChar.of_ring_equiv (zmod_succ_eqv_fin _)

@[simp]
def n_eq_zero : (n: ZMod n) = 0 := by
  cases n
  rfl
  apply (zmod_succ_eqv_fin _).inj
  show zmod_succ_eqv_fin _ _ = zmod_succ_eqv_fin _ 0
  rw [resp_natCast, resp_zero]
  simp [Nat.cast, NatCast.natCast]

@[simp]
def n_nsmul (a: ZMod n) : n • a = 0 := by
  simp [nsmul_eq_natCast_mul]

@[simp]
def n_zsmul (a: ZMod n) : (n: ℤ) • a = 0 := by
  simp [zsmul_eq_intCast_mul, intCast_ofNat]

def natCast_mod_n (a: ℕ) : ((a % n): ZMod n) = a := by
  conv => { rhs; rw [←Nat.div_add_mod a n] }
  rw [natCast_add, natCast_mul]
  simp [n_eq_zero]

def intCast_mod_n (a: ℤ) : ((a % (n: ℤ)): ZMod n) = a := by
  conv => { rhs; rw [←Int.ediv_add_emod a n] }
  rw [←intCast_add, ←intCast_mul]
  simp [intCast_ofNat, n_eq_zero]

@[simp]
def intCast_eq_intCast {n: ℕ} {a b: ℤ} :
  a % n = b % n ↔ (a: ZMod n) = (b: ZMod n) := by
  apply Iff.intro
  · intro g
    cases n with
    | zero =>
      rw [
        natCast_zero, Int.emod_zero, Int.emod_zero] at g
      congr
    | succ n =>
    apply (zmod_succ_eqv_fin (n+1)).inj
    show zmod_succ_eqv_fin _ _ = zmod_succ_eqv_fin _ _
    rw [resp_intCast, resp_intCast]
    show Fin.mk _ _ = Fin.mk _ _
    congr 2
  · intro eq
    rw [←intCast_mod_n, ←intCast_mod_n b] at eq
    cases n
    rw [natCast_zero, Int.emod_zero, Int.emod_zero] at *
    rw [←resp_intCast zmod_zero_eqv_int.symm, ←resp_intCast zmod_zero_eqv_int.symm] at eq
    apply zmod_zero_eqv_int.symm.inj
    assumption
    rename_i n
    rw [←resp_intCast (zmod_succ_eqv_fin (n+1)).symm, ←resp_intCast (zmod_succ_eqv_fin (n+1)).symm] at eq
    replace eq := Int.ofNat_inj.mpr <| Fin.mk.inj <| (zmod_succ_eqv_fin _).symm.inj eq
    rw [Int.toNat_of_nonneg, Int.toNat_of_nonneg,
      Int.ofNat_succ, Int.emod_emod, Int.emod_emod] at eq
    assumption
    refine Int.emod_nonneg _ ?_
    omega
    refine Int.emod_nonneg _ ?_
    omega

@[simp]
def natCast_eq_natCast {a b: ℕ} :
  a % n = b % n ↔ (a: ZMod n) = (b: ZMod n) := by
  rw [←intCast_ofNat, ←intCast_ofNat b, ←intCast_eq_intCast]
  rw [←Int.ofNat_emod, ←Int.ofNat_emod, Int.ofNat_inj]

def toInt_intCast (x: ZMod n) : x.toInt = x := by
  let mkQuot : ℤ →+* ZMod n := (Int.multiples n).mkQuot
  rw [←resp_intCast mkQuot]
  obtain ⟨x, rfl⟩ := (Int.multiples n).mkQuot_surj x
  apply Quotient.sound
  cases n
  rfl
  rename_i n
  show ((n+1: ℕ): ℤ) ∣ (x % (n+1: ℕ)).toNat - x
  rw [Int.toNat_of_nonneg]
  exact Int.dvd_emod_sub_self
  refine Int.emod_nonneg x ?_
  omega

def homOfDvd (n m: ℕ) (h: m ∣ n) : ZMod n →+* ZMod m where
  toFun n := toInt n
  resp_zero' := by
    dsimp
    cases n <;> unfold toInt <;> dsimp
    rw [resp_zero, intCast_zero]
    rw [resp_zero]
    rfl
  resp_one' := by
    cases n <;> unfold toInt <;> dsimp
    rw [resp_one, intCast_one]
    rw [resp_one]
    rename_i n
    cases n
    cases Nat.dvd_one.mp h
    decide
    rename_i n
    rfl
  resp_add' {x y} := by
    cases n
    unfold toInt
    dsimp only
    rw [resp_add, intCast_add]
    unfold toInt
    dsimp only
    rw [resp_add, intCast_ofNat, intCast_ofNat, intCast_ofNat,
      Fin.add_def, Fin.val_mk]
    rw [←natCast_mod_n, Nat.mod_mod_of_dvd, natCast_mod_n, natCast_add]
    assumption
  resp_mul' {x y} := by
    cases n
    unfold toInt
    dsimp only
    rw [resp_mul, intCast_mul]
    unfold toInt
    dsimp only
    rw [resp_mul, intCast_ofNat, intCast_ofNat, intCast_ofNat,
      Fin.mul_def, Fin.val_mk]
    rw [←natCast_mod_n, Nat.mod_mod_of_dvd, natCast_mod_n, natCast_mul]
    assumption

-- def embOfDvd (n m: ℕ) (h: m ∣ n) : ZMod m ↪+*₀ ZMod n where
--   toFun x :=
--     match m with
--     | 0 => toInt x
--     | m + 1 => (((m + 1) * toInt x / n): ℤ)
--   resp_zero' := by
--     dsimp
--     have : ¬NeZero 0 := by
--       intro ⟨_⟩
--       contradiction
--     cases m <;> unfold toInt <;> dsimp only
--     rw [resp_zero, intCast_zero]
--     rw [resp_zero]
--     simp [intCast_zero, mul_zero]
--   inj' := by
--     have : ¬NeZero 0 := by
--       intro ⟨_⟩
--       contradiction
--     intro x y eq
--     dsimp at eq
--     cases m
--     · cases Nat.zero_dvd.mp h
--       simpa [toInt_intCast] using eq
--     rename_i m
--     unfold toInt at eq <;> dsimp only at eq
--     rw [←intCast_eq_intCast] at eq
--     apply (zmod_succ_eqv_fin (m + 1)).inj
--     revert eq
--     generalize (zmod_succ_eqv_fin (m + 1)) x = x'
--     generalize (zmod_succ_eqv_fin (m + 1)) y = y'
--     clear x y; intro eq
--     sorry
--   resp_add' {x y} := by
--     cases m <;> dsimp
--     cases Nat.zero_dvd.mp h
--     simp [toInt_intCast]
--     rename_i m
--     sorry
--   resp_mul' {x y} := by
--     cases m <;> dsimp
--     cases Nat.zero_dvd.mp h
--     simp [toInt_intCast]
--     rename_i m
--     sorry

end ZMod
