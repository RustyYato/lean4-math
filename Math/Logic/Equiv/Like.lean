import Math.Logic.Equiv.Defs

class IsSurjective (F: Sort*) (α β: outParam Sort*) [FunLike F α β] where
  coe_surj (f: F): Function.Surjective f

class EmbeddingLike (F: Sort*) (α β: outParam Sort*) where
  coe : F -> α ↪ β := by intro f; exact f.toEmbedding
  coe_inj : Function.Injective coe := by intro a b h; cases a; cases b; congr

instance[EmbeddingLike F α β] : CoeTC F (α ↪ β) := ⟨EmbeddingLike.coe⟩

class EquivLike (F: Sort*) (α β: outParam Sort*) where
  coe : F -> α ≃ β := by intro f; exact f.toEquiv
  coe_inj : Function.Injective coe := by intro a b h; cases a; cases b; congr

instance [EquivLike F α β] : CoeTC F (α ≃ β) := ⟨EquivLike.coe⟩

def coe_surj [FunLike F α β] [IsSurjective F α β] (f: F): Function.Surjective f := IsSurjective.coe_surj f

instance [EmbeddingLike F α β] : FunLike F α β where
  coe f := (f: α ↪ β)
  coe_inj := by
    apply Function.Injective.comp
    apply DFunLike.coe_inj
    apply EmbeddingLike.coe_inj

instance [EquivLike F α β] : FunLike F α β where
  coe f := (f: α ≃ β)
  coe_inj := by
    apply Function.Injective.comp
    apply DFunLike.coe_inj
    apply EquivLike.coe_inj

instance [EquivLike F α β] : EmbeddingLike F α β where
  coe f := Equiv.toEmbedding f
  coe_inj := by
    show Function.Injective (Equiv.toEmbedding ∘ EquivLike.coe)
    apply Function.Injective.comp
    · intro a b h
      ext
      show a.toEmbedding _ = b.toEmbedding _
      rw [h]
    apply EquivLike.coe_inj

instance [EquivLike F α β] : IsSurjective F α β where
  coe_surj f x := by
    let f' := (f: α ≃ β)
    exists f'.symm x
    symm; apply f'.symm_coe
