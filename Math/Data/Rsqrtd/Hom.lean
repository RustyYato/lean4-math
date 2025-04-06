import Math.Data.Rsqrtd.Defs
import Math.Algebra.Hom.Defs

namespace Rsqrtd

def lift
  [SemiringOps R] [SemiringOps S]
  [IsSemiring R] [IsSemiring S]
  [IsCommMagma R] [IsCommMagma S] {a: R}
  (f: R →+* S) : Rsqrtd a →+* Rsqrtd (f a) where
  toFun x := ⟨f x.a, f x.b⟩
  map_zero := by ext <;> simp [map_zero]
  map_one := by ext <;> simp [map_one, map_zero]
  map_add {_ _} := by ext <;> simp [map_add]
  map_mul {_ _} := by ext <;> simp [map_add, map_mul]

def liftEmbedding
  [SemiringOps R] [SemiringOps S]
  [IsSemiring R] [IsSemiring S]
  [IsCommMagma R] [IsCommMagma S] {a: R}
  (f: R ↪+* S) : Rsqrtd a ↪+* Rsqrtd (f a) := {
    lift f.toRingHom with
    inj' := by
      intro  x y h
      have : f _ = f _ ∧ f _ = f _ := Rsqrtd.mk.inj h
      rw [f.inj.eq_iff, f.inj.eq_iff] at this
      ext; exact this.left; exact this.right
  }

private def cast
  [SemiringOps R] [IsSemiring R] [IsCommMagma R]
  {a b: R}
  : Rsqrtd a ≃ Rsqrtd b where
  toFun x := ⟨x.a, x.b⟩
  invFun x := ⟨x.a, x.b⟩
  leftInv _ := rfl
  rightInv _ := rfl

def liftEquiv
  [SemiringOps R] [SemiringOps S]
  [IsSemiring R] [IsSemiring S]
  [IsCommMagma R] [IsCommMagma S] {a: R}
  (f: R ≃+* S) : Rsqrtd a ≃+* Rsqrtd (f a) :=  {
    lift f.toRingHom with
    invFun := by
      have inv : Rsqrtd (f a) →+* Rsqrtd (f.symm (f a)) := lift (a := f a) f.symm.toRingHom
      exact fun x => cast (inv x)
    leftInv x := by
      ext
      apply f.coe_symm
      apply f.coe_symm
    rightInv x := by
      ext
      apply f.symm_coe
      apply f.symm_coe
  }

end Rsqrtd
