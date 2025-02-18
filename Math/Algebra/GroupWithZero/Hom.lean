import Math.Algebra.Monoid.Units.Hom
import Math.Algebra.Group.Hom
import Math.Algebra.GroupWithZero.Basic

-- def resp_inv?
--   [FunLike F α β]
--   [GroupWithZeroOps α] [IsGroupWithZero α] [GroupWithZeroOps β] [IsGroupWithZero β]
--   [IsZeroHom F α β] [IsOneHom F α β] [IsMulHom F α β] (f: F) {x: α} (h: x ≠ 0) (g: f x ≠ 0) : f (x⁻¹?) = (f x)⁻¹? := by
--   apply (Units.val_inj (a := toUnit? _ (by
--     intro h
--     sorry)) (b := toUnit? _ (by
--     invert_tactic))).mpr
--   rw [inv?_eq_toUnit?_inv]
--   symm

-- def resp_zpow?
--   [FunLike F α β]
--   [GroupOps α] [GroupOps β]
--   [IsOneHom F α β] [IsMulHom F α β]
--   [IsGroup α] [IsGroup β]
--   (f: F) (n: ℤ) (x: α) : f (x ^ n) = (f x) ^ n :=
--   resp_zsmul (α := AddOfMul α) (β := AddOfMul β) f n x

-- def resp_div?
--   [FunLike F α β]
--   [GroupOps α] [GroupOps β]
--   [IsOneHom F α β] [IsMulHom F α β]
--   [IsGroup α] [IsGroup β]
--   (f: F) {x y: α} : f (x / y) = f x / f y :=
--   resp_sub (α := AddOfMul α) (β := AddOfMul β) f
