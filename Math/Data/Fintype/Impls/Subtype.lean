import Math.Data.Fintype.Defs
import Math.Logic.Equiv.Basic

instance instFintypeSubtype {P: α -> Prop} [dec: DecidablePred P] [fa: Fintype α] : Fintype { x: α // P x } where
  all := fa.all.filterMap_embed (fun x => if h:P x then .some ⟨_, h⟩ else .none) (by
    intro x y eq
    dsimp at eq
    dsimp
    split at eq <;> rename_i h
    rw [dif_pos h]
    split at eq  <;> rename_i g
    right; exact Subtype.mk.inj (Option.some.inj eq)
    contradiction
    rw [dif_neg h]; left; rfl)
  complete := by
    intro ⟨x, Px⟩
    apply Multiset.mem_filterMap.mpr
    exists x
    apply And.intro
    apply Fintype.complete
    rw [dif_pos Px]
    rfl

namespace Fintype

def subtypeOr {α: Type _} {P Q: α -> Prop} [DecidableEq α] [fp: Fintype (Subtype P)] [fq: Fintype (Subtype Q)] : Fintype { x: α // P x ∨ Q x } where
  all :=
    let as: Finset { x: α // P x ∨ Q x } := fp.all.map_emb ⟨fun x: Subtype P => Subtype.mk x.val (Or.inl x.property), by
      intro ⟨x, _⟩ ⟨y, _⟩ eq
      cases eq
      rfl⟩
    let bs: Finset { x: α // P x ∨ Q x } := fq.all.map_emb ⟨fun x: Subtype Q => Subtype.mk x.val (Or.inr x.property), by
      intro ⟨x, _⟩ ⟨y, _⟩ eq
      cases eq
      rfl⟩
    as ∪ bs
  complete := by
    intro ⟨x, h⟩
    apply Finset.mem_union.mpr
    cases h <;> rename_i h
    left; apply Finset.mem_map_emb.mpr; exists ⟨x, h⟩
    apply And.intro _ rfl
    apply Fintype.complete
    right; apply Finset.mem_map_emb.mpr; exists ⟨x, h⟩
    apply And.intro _ rfl
    apply Fintype.complete

def subtypeAnd {α: Type _} {P Q: α -> Prop} [DecidablePred Q] [fp: Fintype (Subtype P)] : Fintype { x: α // P x ∧ Q x } :=
  ofEquiv (Equiv.bind_subtype _ _).symm

end Fintype
