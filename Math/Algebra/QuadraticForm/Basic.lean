import Math.Algebra.LinearMap
import Math.Algebra.Impls.Pi

structure QuadraticMap (R M N: Type*)
  [SemiringOps R] [IsSemiring R] [IsCommMagma R]
  [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M]
  [AddMonoidOps N] [IsAddMonoid N] [IsAddCommMagma N]
  [SMul R M] [SMul R N]
  [IsModule R M] [IsModule R N] where
  toFun : M → N
  toFun_smul : ∀ (a : R) (x : M), toFun (a • x) = (a * a) • toFun x
  exists_companion' : ∃ B : BilinMap R M N, ∀ x y, toFun (x + y) = toFun x + toFun y + B x y

abbrev QuadraticForm (R M: Type*)
  [SemiringOps R] [IsSemiring R] [IsCommMagma R]
  [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M]
  [SMul R M] [IsModule R M]: Type _ := QuadraticMap R M R

namespace QuadraticMap

variable
  [SemiringOps R] [IsSemiring R] [IsCommMagma R]
  [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M]
  [AddMonoidOps N] [IsAddMonoid N] [IsAddCommMagma N]
  [SMul R M] [SMul R N]
  [IsModule R M] [IsModule R N]

instance : FunLike (QuadraticMap R M N) M N where
  coe f := f.toFun
  coe_inj := by
    intro a b _; cases a; congr

def smul_eq_smul_sq (Q: QuadraticMap R M N) (r: R) (x: M) :
  Q (r • x) = (r * r) • Q x := Q.toFun_smul _ _

def exists_companion (Q: QuadraticMap R M N) : ∃ B : BilinMap R M N, ∀ x y, Q (x + y) = Q x + Q y + B x y := Q.exists_companion'

def copy (q: QuadraticMap R M N) (g: M -> N) (h: ∀x, q x = g x) : QuadraticMap R M N where
  toFun := g
  toFun_smul := by
    intro a x
    simp [←h, smul_eq_smul_sq]
  exists_companion' := by
    simp [←h]
    exact q.exists_companion

@[simp]
def toFun_eq (q: QuadraticMap R M N) : q.toFun = q := rfl

@[ext]
def ext (a b: QuadraticMap R M N) : (∀x, a x = b x) -> a = b := DFunLike.ext _ _

end QuadraticMap

namespace QuadraticMap

variable
  [SemiringOps R] [IsSemiring R] [IsCommMagma R]
  [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M]
  [AddGroupOps N] [IsAddGroup N] [IsAddCommMagma N]
  [SMul R M] [IsModule R M] [SMul R N] [IsModule R N]

def polar (Q: QuadraticMap R M N) : BilinMap R M N := by
  refine BilinMap.mk (fun a b => Q (a + b) - Q a - Q b) ?_ ?_ ?_ ?_
  · intro a b k
    dsimp only
    have ⟨B, spec⟩ := Q.exists_companion
    iterate 4 rw [spec]
    simp only [map_add, LinearMap.apply_add, sub_eq_add_neg, neg_add_rev]
    rw [
      show Q a + Q b + (B a) b + Q k + ((B a) k + (B b) k) + (-(B a) b + (-Q b + -Q a)) + -Q k
         = ((Q a + -Q a) + Q b + (-Q b)) + ((B a) b + (-(B a) b)) + (Q k + -Q k) + ((B a) k + (B b) k) by ac_rfl,
      show Q a + Q k + (B a) k + -Q a + -Q k + (Q b + Q k + (B b) k + -Q b + -Q k)
         = (Q a + -Q a) + (Q k + -Q k) + (B a) k+ (B b) k  + (Q b + -Q b) + (Q k + -Q k) by ac_rfl
    ]
    simp [add_neg_cancel]
  · intro k a b
    dsimp only
    have ⟨B, spec⟩ := Q.exists_companion
    iterate 4 rw [spec]
    simp only [map_add, LinearMap.apply_add, sub_eq_add_neg, neg_add_rev]
    rw [
      show Q k + (Q a + Q b + (B a) b) + ((B k) a + (B k) b) + -Q k + (-(B a) b + (-Q b + -Q a))
         = (Q k + -Q k) + ((Q a + -Q a)+ (Q b + -Q b) + ((B a) b + (-(B a) b))) + ((B k) a + (B k) b) by ac_rfl,
      show Q k + Q a + (B k) a + -Q k + -Q a + (Q k + Q b + (B k) b + -Q k + -Q b)
         = (Q k + -Q k) + (Q a + -Q a) + (B k) a + ((Q k + -Q k) + (Q b + -Q b)) + (B k) b by ac_rfl
    ]
    simp [add_neg_cancel]
  · intro r a b
    dsimp only
    have ⟨B, spec⟩ := Q.exists_companion
    iterate 2 rw [spec]
    simp only [sub_eq_add_neg, smul_add, smul_neg]
    rw [
      show Q (r • a) + Q b + (B (r • a)) b + -Q (r • a) + -Q b
         = (Q (r • a) + -Q (r • a)) + (Q b + -Q b) + (B (r • a)) b by ac_rfl,
      show r • Q a + r • Q b + r • (B a) b + -(r • Q a) + -(r • Q b)
         = (r • Q a + -(r • Q a)) + (r • Q b + -(r • Q b)) + r • (B a) b by ac_rfl
    ]
    simp [add_neg_cancel, map_smul]
  · intro r b a
    dsimp only
    have ⟨B, spec⟩ := Q.exists_companion
    iterate 2 rw [spec]
    simp only [sub_eq_add_neg, smul_add, smul_neg]
    rw [
      show Q a + Q (r • b) + (B a) (r • b) + -Q a + -Q (r • b)
         = (Q (r • b) + -Q (r • b)) + (Q a + -Q a) + (B a) (r • b) by ac_rfl,
      show r • Q a + r • Q b + r • (B a) b + -(r • Q a) + -(r • Q b)
         = (r • Q a + -(r • Q a)) + (r • Q b + -(r • Q b)) + r • (B a) b by ac_rfl
    ]
    simp [add_neg_cancel, map_smul]

end QuadraticMap

namespace QuadraticFrom

variable
  [RingOps R] [IsRing R] [IsCommMagma R]
  [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M]
  [SMul R M] [IsModule R M]

def polar (Q: QuadraticForm R M) : BilinMap R M R :=
  QuadraticMap.polar Q

end QuadraticFrom

namespace QuadraticMap

section AddMonoid

variable
  [SemiringOps R] [IsSemiring R] [IsCommMagma R]
  [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M]
  [AddMonoidOps N] [IsAddMonoid N] [IsAddCommMagma N]
  [SMul R M] [SMul R N]
  [IsModule R M] [IsModule R N]

instance : Zero (QuadraticMap R M N) where
  zero := {
    toFun := 0
    toFun_smul _ _ := by simp
    exists_companion' := by
      exists 0
      simp
  }

instance : Add (QuadraticMap R M N) where
  add a b := {
    toFun := a.toFun + b.toFun
    toFun_smul := by
      intro a m
      simp
      rw [smul_eq_smul_sq, smul_eq_smul_sq, ←smul_add]
    exists_companion' := by
      have ⟨Ba, ha⟩ := a.exists_companion
      have ⟨Bb, hb⟩ := b.exists_companion
      exists Ba + Bb
      intro x y
      simp
      show a _ + b _ = a _ + b _ + (a _ + b _) + _
      rw [ha, hb]; ac_rfl
  }

instance : SMul R (QuadraticMap R M N) where
  smul r a := {
    toFun := r • a.toFun
    toFun_smul := by
      intro a m
      simp
      rw [smul_eq_smul_sq, smul_comm]
    exists_companion' := by
      have ⟨Ba, ha⟩ := a.exists_companion
      exists r • Ba
      intro x y
      simp
      rw [ha]; clear ha
      simp [smul_add]
  }

instance : SMul ℕ (QuadraticMap R M N) where
  smul n a  := {
    toFun := n • a.toFun
    toFun_smul := by
      intro a m
      simp
      rw [smul_eq_smul_sq, smul_comm]
    exists_companion' := by
      have ⟨Ba, ha⟩ := a.exists_companion
      exists n • Ba
      intro x y
      simp
      rw [ha]; clear ha
      simp [nsmul_add]
  }

instance : IsAddCommMagma (QuadraticMap R M N) where
  add_comm _ _ := by ext; apply add_comm

instance : IsAddMonoid (QuadraticMap R M N) where
  add_assoc _ _ _ := by ext; apply add_assoc
  zero_add _ := by ext; apply zero_add
  add_zero _ := by ext; apply add_zero
  zero_nsmul _ := by ext; apply zero_nsmul
  succ_nsmul _ _ := by ext; apply succ_nsmul

instance : IsDistribMulAction R (QuadraticMap R M N) where
  one_smul _ := by ext; apply one_smul
  mul_smul _ _ _ := by ext; apply mul_smul
  smul_zero _ := by ext; apply smul_zero
  smul_add _ _ _ := by ext; apply smul_add

end AddMonoid

section AddGroup

variable
  [SemiringOps R] [IsSemiring R] [IsCommMagma R]
  [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M]
  [AddGroupOps N] [IsAddGroup N] [IsAddCommMagma N]
  [SMul R M] [SMul R N]
  [IsModule R M] [IsModule R N]

instance : Neg (QuadraticMap R M N) where
  neg a := {
    toFun := -a.toFun
    toFun_smul _ _ := by simp [smul_eq_smul_sq, neg_smul']
    exists_companion' := by
      have ⟨B, h⟩ := a.exists_companion
      exists -B
      intro x y
      simp [h, neg_add_rev]; clear h
      ac_rfl
  }

instance : Sub (QuadraticMap R M N) where
  sub a b := (a + -b).copy (fun x => a x - b x) <| by
    intro x
    simp
    rw [sub_eq_add_neg]; rfl

instance : SMul ℤ (QuadraticMap R M N) where
  smul n a := (match n with
    | .ofNat n => n • a
    | .negSucc n => -((n + 1) • a)).copy (fun x => n • a x) <| by
      intro a
      cases n <;> simp
      rw [zsmul_ofNat]; rfl
      rw [zsmul_negSucc]; rfl

instance : IsAddGroup (QuadraticMap R M N) where
  sub_eq_add_neg _ _ := by ext; apply sub_eq_add_neg
  neg_add_cancel _ := by ext; apply neg_add_cancel
  zsmul_ofNat _ _ := by ext; apply zsmul_ofNat
  zsmul_negSucc _ _ := by ext; apply zsmul_negSucc

end AddGroup

end QuadraticMap
