import Math.Algebra.Group.Theory.Basic
import Math.Algebra.Module.Defs

-- the automorphism group of a group α
instance Aut (α: Type*) [GroupOps α] [IsGroup α] : Group (α ≃* α) := by
  apply Group.ofAxiomsLeft .refl .trans .symm
  intro; rfl
  intro; apply GroupEquiv.trans_symm
  intros; rfl

-- the automorphism group of a group α
instance AddAut (α: Type*) [AddGroupOps α] [IsAddGroup α] : Group (α ≃+ α) := by
  apply Group.ofAxiomsLeft .refl .trans .symm
  intro; rfl
  intro; apply AddGroupEquiv.trans_symm
  intros; rfl

-- every distributive right action on an additive group defines
-- a homomorphism into the additive automorphism group
def Group.toAddAut (G M: Type*) [GroupOps G] [IsGroup G]
  [AddGroupOps M] [IsAddGroup M] [SMul Gᵐᵒᵖ M] [IsDistribMulAction Gᵐᵒᵖ M]:
  G →* AddAut M where
  toFun x := {
    toFun m := MulOpp.mk x • m
    invFun m := MulOpp.mk x⁻¹ • m
    leftInv := by
      intro m; simp [←mul_smul, MulOpp.mk]
    rightInv := by
      intro m; simp [←mul_smul, MulOpp.mk]
    map_zero := by simp
    map_add {m₀ m₁} := by simp [smul_add]
  }
  map_one := by simp; rfl
  map_mul := by
    intro x y
    apply AddGroupEquiv.ext
    intro m
    show (MulOpp.mk (x * y) • m) = MulOpp.mk y • (MulOpp.mk x • m)
    simp [←mul_smul]

section

variable [GroupOps G] [IsGroup G] [AddGroupOps M] [IsAddGroup M]
  (h: G →* AddAut M)

def ofAddAut (_: G →* AddAut M) := G

instance : FunLike (AddAut M) M M :=
  inferInstanceAs (FunLike (M ≃+ M) M M)

instance (h: G →* AddAut M) : SMul (ofAddAut h)ᵐᵒᵖ M where
  smul x m := h x.get m

instance : GroupOps (ofAddAut h) :=
  inferInstanceAs (GroupOps G)
instance : IsGroup (ofAddAut h) :=
  inferInstanceAs (IsGroup G)

-- every group homomorphism from G to an additive automorphism group
-- defines a distributive right action
-- NOTE: this must be a right action, since function composition
-- is right associative
instance (h: G →* AddAut M) : IsDistribMulAction (ofAddAut h)ᵐᵒᵖ M where
  one_smul := by
    intro a
    show h _ _ = _
    rw [MulOpp.get_one, map_one]; rfl
  mul_smul x y m := by
    show h _ _ = h _ (h _ _)
    cases x with | mk x =>
    cases y with | mk y =>
    simp [←MulOpp.mk_mul]
    rw [map_mul]; rfl
  smul_zero a := map_zero (F := M ≃+ M) _
  smul_add _ _ _ := map_add (F := M ≃+ M) _

end section
