import Math.Logic.Equiv.Defs

class EmbeddingLike (F: Sort*) (α β: outParam Sort*) where
  coe : F -> α ↪ β
  coe_inj : Function.Injective coe

instance[EmbeddingLike F α β] : CoeTC F (α ↪ β) := ⟨EmbeddingLike.coe⟩

class EquivLike (F: Sort*) (α β: outParam Sort*) where
  coe : F -> α ≃ β
  coe_inj : Function.Injective coe

instance [EquivLike F α β] : CoeTC F (α ≃ β) := ⟨EquivLike.coe⟩

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
