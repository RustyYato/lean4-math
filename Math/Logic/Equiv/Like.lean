import Math.Logic.Equiv.Defs

class IsSurjective (F: Sort*) (α β: outParam Sort*) [FunLike F α β] where
  coe_surj (f: F): Function.Surjective f

class EmbeddingLike (F: Sort*) (α β: outParam Sort*) where
  coe : F -> α ↪ β := by intro f; exact f.toEmbedding
  coe_inj : Function.Injective coe := by intro a b h; cases a; cases b; congr

instance[EmbeddingLike F α β] : CoeTC F (α ↪ β) := ⟨EmbeddingLike.coe⟩

class SurjectionLike (F: Sort*) (α β: outParam Sort*) where
  coe : F -> α ↠ β := by intro f; exact f.toSurjection
  coe_inj : Function.Injective coe := by intro a b h; cases a; cases b; congr

instance [SurjectionLike F α β] : CoeTC F (α ↠ β) := ⟨SurjectionLike.coe⟩

class BijectionLike (F: Sort*) (α β: outParam Sort*) where
  coe : F -> α ⇔ β := by intro f; exact f.toBijection
  coe_inj : Function.Injective coe := by intro a b h; cases a; cases b; congr

instance [BijectionLike F α β] : CoeTC F (α ⇔ β) := ⟨BijectionLike.coe⟩

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

instance [SurjectionLike F α β] : FunLike F α β where
  coe f := (f: α ↠ β)
  coe_inj := by
    apply Function.Injective.comp
    apply DFunLike.coe_inj
    apply SurjectionLike.coe_inj

instance [BijectionLike F α β] : FunLike F α β where
  coe f := (f: α ⇔ β)
  coe_inj := by
    apply Function.Injective.comp
    apply DFunLike.coe_inj
    apply BijectionLike.coe_inj

instance [BijectionLike F α β] : EmbeddingLike F α β where
  coe f := Bijection.toEmbedding f
  coe_inj := by
    show Function.Injective (Bijection.toEmbedding ∘ BijectionLike.coe)
    apply Function.Injective.comp
    · intro a b h
      show Bijection.mk a.toEmbedding _ = Bijection.mk b.toEmbedding _
      congr
    apply BijectionLike.coe_inj

instance [BijectionLike F α β] : SurjectionLike F α β where
  coe f := Bijection.toSurjection f
  coe_inj := by
    show Function.Injective (Bijection.toSurjection ∘ BijectionLike.coe)
    apply Function.Injective.comp
    · intro a b h
      show Bijection.mk ⟨a.toSurjection, _⟩ _ = Bijection.mk ⟨b.toSurjection, _⟩ _
      congr
      rw [h]
    apply BijectionLike.coe_inj

instance [EquivLike F α β] : BijectionLike F α β where
  coe f := Equiv.toBijection f
  coe_inj := by
    show Function.Injective (Equiv.toBijection ∘ EquivLike.coe)
    apply Function.Injective.comp
    · intro a b h
      ext
      show a.toBijection _ = b.toBijection _
      rw [h]
    apply EquivLike.coe_inj

instance [EquivLike F α β] : EmbeddingLike F α β := inferInstance
instance [EquivLike F α β] : SurjectionLike F α β := inferInstance

instance [EquivLike F α β] : IsSurjective F α β where
  coe_surj f x := by
    let f' := (f: α ≃ β)
    exists f'.symm x
    symm; apply f'.symm_coe

syntax "hom_equiv_trans_symm_impl" ident : tactic
macro_rules
| `(tactic|hom_equiv_trans_symm_impl $e) => `(tactic|apply DFunLike.ext; first|apply ($e).coe_symm|(apply ($e).symm_coe))
