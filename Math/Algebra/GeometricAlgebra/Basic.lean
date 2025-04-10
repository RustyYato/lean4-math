import Math.Algebra.Ring.Defs
import Math.Algebra.Hom.Defs

inductive BasisVector where
| zero
| pos
| neg
deriving Repr

-- a binary tree representing the Geometric Algebra G(z, p, n)
inductive GA (R: Type u) : List BasisVector -> Type u where
| scalar : R -> GA R []
| node (b: BasisVector) (rem keep: GA R bs) : GA R (b::bs)
deriving Repr

namespace GA

def zipWith (f: R -> S -> α) : GA R basis -> GA S basis -> GA α basis
| .scalar a, .scalar b => .scalar (f a b)
| .node _ a₀ a₁, .node _ b₀ b₁ => .node _ (a₀.zipWith f b₀) (a₁.zipWith f b₁)

def map (f: R -> α) : GA R basis -> GA α basis
| .scalar a => .scalar (f a)
| .node _ a₀ a₁ => .node _ (a₀.map f) (a₁.map f)

def ofScalar [Zero R] (r: R) : ∀{basis}, GA R basis
| [] => .scalar r
| _::_ => .node _ (.ofScalar r) (.ofScalar 0)

def map_ofScalar [Zero R] [Zero α] [FunLike F R α] [IsZeroHom F R α] (f: F) (r: R) :
  map f (ofScalar r) = ofScalar (basis := basis) (f r) := by
  induction basis generalizing r with
  | nil => rfl
  | cons _ _  ih =>
    unfold ofScalar map
    congr
    apply ih
    rw [ih, map_zero]

instance [Zero R] : Zero (GA R basis) := ⟨.ofScalar (OfNat.ofNat 0)⟩
instance [Zero R] [One R] : One (GA R basis) := ⟨.ofScalar (OfNat.ofNat 1)⟩
instance [Zero R] [NatCast R] : NatCast (GA R basis) := ⟨(.ofScalar (R := R) ·)⟩
instance [Zero R] [IntCast R] : IntCast (GA R basis) := ⟨(.ofScalar (R := R) ·)⟩
instance [Add R] : Add (GA R basis) := ⟨zipWith (· + ·)⟩
instance [Sub R] : Sub (GA R basis) := ⟨zipWith (· - ·)⟩
instance [Neg R] : Neg (GA R basis) := ⟨map (-·)⟩
instance [SMul S R] : SMul S (GA R basis) := ⟨fun r => map (r • ·)⟩

def basis_mul [Neg R] : GA R basis -> GA R basis
| .scalar v => .scalar v
| .node _ a₀ a₁ => .node _ a₀.basis_mul (-a₁.basis_mul)

-- (a₀ + a₁ e) (b₀ + b₁ e) =
-- (a₀ (b₀ + b₁ e) + a₁ e (b₀ + b₁ e)) =
-- a₀ b₀ + a₀ b₁ e + a₁ e b₀ + a₁ e b₁ e =
-- a₀ b₀ + a₀ b₁ e + a₁ $b₀ e + a₁ $b₁ e e =
-- a₀ b₀ + (a₀ b₁ + a₁ $b₀) e + a₁ $b₁ e e =
def mul [Mul R] [Add R] [Neg R] [Sub R] : GA R basis -> GA R basis -> GA R basis
| .scalar a, .scalar b => .scalar (a * b)
-- a₀ * b₀ + (a₀ * b₁ + a₁ $b₀) e  + a₁ $b₁ e * e =
-- a₀ * b₀ + (a₀ * b₁ + a₁ $b₀) e  - a₁ $b₁ =
-- (a₀ * b₀ - a₁ $b₁) + (a₀ * b₁ + a₁ $b₀) e  =
| .node .neg a₀ a₁, .node _ b₀ b₁ => .node _ (a₀.mul b₀ - a₁.mul b₁.basis_mul) (a₀.mul b₁ + a₁.mul b₀.basis_mul)
-- a₀ * b₀ + (a₀ * b₁ + a₁ $b₀) e  + a₁ $b₁ e * e =
-- a₀ * b₀ + (a₀ * b₁ + a₁ $b₀) e  + a₁ $b₁ =
-- (a₀ * b₀ + a₁ $b₁) + (a₀ * b₁ + a₁ $b₀) e  =
| .node .pos a₀ a₁, .node _ b₀ b₁ => .node _ (a₀.mul b₀ + a₁.mul b₁.basis_mul) (a₀.mul b₁ + a₁.mul b₀.basis_mul)
-- a₀ * b₀ + (a₀ * b₁ + a₁ $b₀) e  + a₁ $b₁ e * e =
-- a₀ * b₀ + (a₀ * b₁ + a₁ $b₀) e =
| .node .zero a₀ a₁, .node _ b₀ b₁ => .node _ (a₀.mul b₀) (a₀.mul b₁ + a₁.mul b₀.basis_mul)

instance [Mul R] [Add R] [Neg R] [Sub R] : Mul (GA R basis) := ⟨mul⟩

instance [Zero R] [One R] [Mul R] [Add R] [Neg R] [Sub R] : Pow (GA R basis) ℕ := ⟨flip npowRec⟩

@[simp] def add_scalar [Add R] (a b: R) : scalar a + scalar b = scalar (a + b) := rfl
@[simp] def add_node [Add R] (a b c d: GA R basis) : node v a b + node v c d = node v (a + c) (b + d) := rfl

@[simp] def neg_scalar [Neg R] (a: R) : -scalar a = scalar (-a) := rfl
@[simp] def neg_node [Neg R] (a b: GA R basis) : -node v a b = node v (-a) (-b) := rfl

@[simp] def basis_mul_scalar [Neg R] (a: R) : (scalar a).basis_mul = scalar a := rfl
@[simp] def basis_mul_node [Neg R] (a b: GA R basis) : (node v a b).basis_mul = node v a.basis_mul (-b.basis_mul) := rfl

@[local simp] def zero_scalar [Zero R] : 0 = scalar (0: R) := rfl
@[local simp] def zero_node [Zero R] : 0 = node v 0 (0: GA R basis) := rfl
@[local simp] def one_scalar [Zero R] [One R] : 1 = scalar (1: R) := rfl
@[local simp] def one_node [Zero R] [One R] : 1 = node v 1 (0: GA R basis) := rfl

section

variable [Mul R] [Add R] [Neg R] [Sub R]

@[simp] def mul_scalar (a b: R) : scalar a * scalar b = scalar (a * b) := rfl
@[simp] def mul_node_neg [Neg R] (a b c d: GA R basis) : (node .neg a b) * (node .neg c d) =
  node _ (a * c - b * d.basis_mul) (a * d + b * c.basis_mul) := rfl
@[simp] def mul_node_pos [Neg R] (a b c d: GA R basis) : (node .pos a b) * (node .pos c d) =
  node _ (a * c + b * d.basis_mul) (a * d + b * c.basis_mul) := rfl
@[simp] def mul_node_zero [Neg R] (a b c d: GA R basis) : (node .zero a b) * (node .zero c d) =
  node _ (a * c) (a * d + b * c.basis_mul) := rfl

end

instance [AddGroupOps R] [IsAddGroup R] : IsAddGroup (GA R basis) where
  add_assoc a b c := by
    induction a with
    | scalar a =>
      cases b; cases c
      show scalar _ = scalar _
      congr 1; apply add_assoc
    | node _ a₀ a₁ ih₀ ih₁ =>
      cases b; cases c
      show node _ _ _ = node _ _ _
      congr 1
      apply ih₀
      apply ih₁
  zero_add a := by
    induction a with
    | scalar =>
      show scalar _ = scalar _
      congr; apply zero_add
    | node =>
      show node _ _ _ = node _ _ _
      congr 1
  add_zero a := by
    induction a with
    | scalar =>
      show scalar _ = scalar _
      congr; apply add_zero
    | node =>
      show node _ _ _ = node _ _ _
      congr 1
  sub_eq_add_neg a b := by
    induction a with
    | scalar =>
      cases b
      show scalar _ = scalar _
      congr; apply sub_eq_add_neg
    | node _ _ _ ih₀ ih₁ =>
      cases b
      show node _ _ _ = node _ _ _
      congr 1
      apply ih₀
      apply ih₁
  neg_add_cancel a := by
    induction a with
    | scalar =>
      show scalar _ = scalar _
      congr; apply neg_add_cancel
    | node =>
      show node _ _ _ = node _ _ _
      congr 1
  zero_nsmul a := by
    induction a with
    | scalar =>
      show scalar _ = scalar _
      congr; apply zero_nsmul
    | node =>
      show node _ _ _ = node _ _ _
      congr 1
  succ_nsmul n a := by
    induction a with
    | scalar =>
      show scalar _ = scalar _
      congr; apply succ_nsmul
    | node =>
      show node _ _ _ = node _ _ _
      congr 1
  zsmul_ofNat n a := by
    induction a with
    | scalar =>
      show scalar _ = scalar _
      congr; apply zsmul_ofNat
    | node =>
      show node _ _ _ = node _ _ _
      congr 1
  zsmul_negSucc n a := by
    induction a with
    | scalar =>
      show scalar _ = scalar _
      congr; apply zsmul_negSucc
    | node =>
      show node _ _ _ = node _ _ _
      congr 1

instance [Add R] [IsAddCommMagma R] : IsAddCommMagma (GA R basis) where
  add_comm a b := by
    induction a with
    | scalar a =>
      cases b with | scalar b =>
      show scalar _ = scalar _
      congr 1
      apply add_comm
    | node v a₀ a₁ ih₀ ih₁ =>
      cases b with | node _ b₀ b₁ =>
      simp [ih₀, ih₁]

instance [AddGroupWithOneOps R] [IsAddGroupWithOne R] : IsAddGroupWithOne (GA R basis) where
  natCast_zero := by
    show ofScalar _ = ofScalar _
    rw [natCast_zero]
  natCast_succ n := by
    show ofScalar _ = zipWith _ (ofScalar _) (ofScalar _)
    induction basis generalizing n with
    | nil =>
      show scalar _ = scalar _
      rw [natCast_succ]
    | cons b basis ih =>
      show node _ _ _ = node _ _ _
      congr
      apply ih
      symm; apply add_zero
  intCast_ofNat := by
    intro n
    show ofScalar _ = ofScalar _
    rw [intCast_ofNat]
  intCast_negSucc := by
    intro n
    let neg : ZeroHom R R := {
      toFun x := -x
      map_zero := neg_zero
    }
    show .ofScalar _ = map neg (.ofScalar _)
    rw [map_ofScalar, intCast_negSucc]
    rfl

@[simp] def basis_mul_ofScalar [AddGroupOps R] [IsAddGroup R] (r: R) : basis_mul (basis := basis) (R := R) (ofScalar r) = ofScalar r := by
  induction basis generalizing r with
  | nil => rfl
  | cons b basis ih =>
    show node _ _ _  = node _ _ _
    congr
    rw [ih]
    show -(basis_mul (ofScalar 0)) = 0
    rw [ih 0]
    show -(0: GA _ _) = 0
    rw [neg_zero]

@[simp] def basis_mul_zero [AddGroupOps R] [IsAddGroup R] : basis_mul (basis := basis) (R := R) 0 = 0 :=
  basis_mul_ofScalar 0
@[simp] def basis_mul_one [AddGroupOps R] [One R] [IsAddGroup R] : basis_mul (basis := basis) (R := R) 1 = 1 :=
  basis_mul_ofScalar 1

instance [RingOps R] [IsRing R] : IsMulZeroClass (GA R basis) where
  zero_mul a := by
    induction basis with
    | nil =>
      cases a
      show scalar _ = scalar _
      rw [zero_mul]
    | cons b bs ih =>
      cases a with | node _ a₀ a₁ =>
      show mul (node _ _ _) _ = node _ _ _
      cases b <;> unfold mul <;> congr
      apply ih
      any_goals
        show 0 * a₁ + 0 * a₀.basis_mul = _
        rw [ih, ih, add_zero]; rfl
      any_goals
        show 0 * a₀ + 0 * a₁.basis_mul = _
        rw [ih, ih, add_zero]; rfl
      show 0 * a₀ - 0 * a₁.basis_mul = _
      rw [ih, ih, sub_zero]; rfl
  mul_zero a := by
    induction basis with
    | nil =>
      cases a
      show scalar _ = scalar _
      rw [mul_zero]
    | cons b bs ih =>
      cases a with | node _ a₀ a₁ =>
      show mul _ (node _ _ _) = node _ _ _
      cases b <;> unfold mul <;> congr
      apply ih
      any_goals
        show a₀ * 0 + a₁ * basis_mul 0 = _
        rw [basis_mul_zero, ih, ih, add_zero]; rfl
      show a₀ * 0 - a₁ * basis_mul 0 = _
      rw [basis_mul_zero, ih, ih, sub_zero]; rfl

instance [RingOps R] [IsRing R] : IsMulOneClass (GA R basis) where
  mul_one a := by
    induction a with
    | scalar a => simp
    | node v a₀ a₁ ih₀ ih₁ => cases v <;> simp [ih₀, ih₁]
  one_mul a := by
    induction a with
    | scalar a => simp
    | node v a₀ a₁ ih₀ ih₁ => cases v <;> simp [ih₀, ih₁]

@[simp] def basis_mul_add [AddGroupOps R] [IsAddGroup R] [IsAddCommMagma R] (a b: GA R basis) : (a + b).basis_mul = a.basis_mul + b.basis_mul := by
  induction a with
  | scalar a =>
    cases b
    simp
  | node v a₀ a₁ ih₀ ih₁ =>
    cases b
    simp [ih₀, ih₁]
    rw [neg_add_rev, add_comm]

instance [RingOps R] [IsRing R]  : IsLeftDistrib (GA R basis) where
  mul_add k a b := by
    induction basis with
    | nil =>
      cases k with | scalar k =>
      cases a with | scalar a =>
      cases b with | scalar b =>
      simp [mul_add]
    | cons v vs ih =>
      cases k with | node _ k₀ k₁ =>
      cases a with | node _ a₀ a₁ =>
      cases b with | node _ b₀ b₁ =>
      cases v <;> simp [ih]
      ac_nf
      ac_nf
      rw [sub_add]
      repeat rw [sub_eq_add_neg]
      ac_nf

instance [RingOps R] [IsRing R]  : IsRightDistrib (GA R basis) where
  add_mul a b k := by
    induction basis with
    | nil =>
      cases k with | scalar k =>
      cases a with | scalar a =>
      cases b with | scalar b =>
      simp [add_mul]
    | cons v vs ih =>
      cases k with | node _ k₀ k₁ =>
      cases a with | node _ a₀ a₁ =>
      cases b with | node _ b₀ b₁ =>
      cases v <;> simp [ih]
      ac_nf
      ac_nf
      rw [sub_add]
      repeat rw [sub_eq_add_neg]
      ac_nf

@[simp]
def basis_mul_neg_neg [Neg R] (a: GA R basis) : (-a).basis_mul = -a.basis_mul := by
  induction a with
  | scalar => simp
  | node v a₀ a₁ ih₀ ih₁ => simp [ih₀, ih₁]

@[simp]
def basis_mul_basis_mul [RingOps R] [IsRing R] (a: GA R basis) : a.basis_mul.basis_mul = a := by
  induction a with
  | scalar => simp
  | node v a₀ a₁ ih₀ ih₁ => simp [ih₀, ih₁]

@[simp]
def basis_mul_mul [RingOps R] [IsRing R] (a b: GA R basis) : (a * b).basis_mul = a.basis_mul * b.basis_mul := by
  induction basis with
  | nil =>
    cases a with | scalar a =>
    cases b with | scalar b =>
    simp
  | cons v vs ih =>
    cases a with | node  a₀ a₁ =>
    cases b with | node  b₀ b₁ =>
    cases v <;> simp [ih,neg_add_rev]
    rw [neg_mul_left, neg_mul_right, add_comm]
    rw [←neg_mul_left, neg_mul_right]
    simp only [basis_mul_neg_neg, basis_mul_basis_mul, true_and, neg_neg]
    rw [←neg_mul_left, ←neg_mul_right, add_comm]
    rw [←neg_mul_left, neg_mul_right]
    simp only [basis_mul_neg_neg, basis_mul_basis_mul, neg_neg]
    rw [←neg_mul_left, ←neg_mul_right, add_comm]
    apply And.intro _ rfl
    rw [sub_eq_add_neg]
    simp only [basis_mul_add, ih]
    simp [←sub_neg, ih]

instance [RingOps R] [IsRing R] : IsMonoid (GA R basis) where
  mul_assoc := by
    intro a b c
    induction basis with
    | nil =>
      cases a; cases b; cases c
      simp [mul_assoc]
    | cons v vs ih =>
      cases a with | node _ a₀ a₁ =>
      cases b with | node _ b₀ b₁ =>
      cases c with | node _ c₀ c₁ =>
      cases v <;> (simp [ih, mul_add, add_mul]; ac_nf)
      simp [sub_eq_add_neg, ←neg_mul_left, ←neg_mul_right,
        mul_add, add_mul, ih, neg_add_rev]
      ac_nf

instance [RingOps R] [IsRing R] : IsSemiring (GA R basis) := IsSemiring.inst
instance [RingOps R] [IsRing R] : IsRing (GA R basis) := IsRing.inst

end GA
