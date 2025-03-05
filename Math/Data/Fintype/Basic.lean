import Math.Data.Fintype.Defs
import Math.Data.Set.Basic
import Math.Logic.Equiv.Basic
import Math.Logic.IsEmpty

import Math.Data.Fintype.Impls.Pi
import Math.Data.Fintype.Impls.Subtype
import Math.Data.Fintype.Impls.Finset

namespace Finset

instance [Fintype α] [DecidableEq α] : SetComplement (Finset α) where
  scompl f := Finset.univ _ \ f

def mem_compl [Fintype α] [DecidableEq α] (f: Finset α) :
  ∀{x}, x ∈ fᶜ ↔ x ∉ f := by
  intro x
  show x ∈ Finset.univ _ \ f ↔ _
  simp [mem_sdiff, mem_univ]

@[simp]
def compl_compl [Fintype α] [DecidableEq α] (f: Finset α) : fᶜᶜ = f := by
  ext x
  simp [mem_compl]

end Finset

namespace Fintype

variable {α β: Type*}

def equivOfCardEq
  [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  (h: card α = card β) : Trunc (α ≃ β) :=
  (equivFin α).bind fun ha =>
  (equivFin β).map fun hb =>
  (ha.trans ((Equiv.fin h).trans hb.symm))

def IsEmpty [f: Fintype α] (h: card α = 0) : IsEmpty α where
  elim x := by
    induction f with
    | mk all nodup complete =>
    match all with
    | [] =>
      have := complete x
      contradiction

def embed_of_card_le {α β: Type*} [Fintype β] [Fintype α] [DecidableEq α] [DecidableEq β] (h: card α ≤ card β): Trunc (α ↪ β) :=
  (equivFin α).bind fun ha =>
  (equivFin β).map fun hb =>
  Equiv.congrEmbed ha.symm hb.symm (Fin.embedFin h)

def card_le_of_embed [Fintype β] [Fintype α] (h: α ↪ β) : card α ≤ card β := by
  classical
  induction equivFin α with | mk ha =>
  induction equivFin β with | mk hb =>
  exact Fin.le_of_emebd (Equiv.congrEmbed ha hb h)

def embed_iff_card_le [Fintype β] [Fintype α] : Nonempty (α ↪ β) ↔ card α ≤ card β := by
  apply Iff.intro
  intro ⟨h⟩
  exact card_le_of_embed h
  intro h
  classical
  have := embed_of_card_le (α := α) (β := β) h
  exact (embed_of_card_le h).nonempty

instance [fa: Fintype α] [fb: Fintype β] : Fintype (α ⊕ β) where
  all :=
    Finset.union_disjoint
    ((Finset.univ α).map_emb ⟨.inl, fun _ _ => Sum.inl.inj⟩)
    ((Finset.univ β).map_emb ⟨.inr, fun _ _ => Sum.inr.inj⟩) (by
    intro x ha hb
    simp [Finset.mem_map_emb] at ha hb
    obtain ⟨_, rfl⟩ := ha
    nomatch hb)
  complete x := by
    apply Finset.mem_union_disjoint.mpr
    simp [Finset.mem_map_emb]
    cases x <;> simp

instance [fa: Fintype α] [fb: Fintype β] : Fintype (α × β) where
  all :=
    (Finset.univ α).flatMap_embed (fun a =>
    (Finset.univ β).map_emb ⟨fun b => (a, b), by intro a b eq; cases eq; rfl⟩) <| by
    intro x y hx hy (a, b) ha hb
    simp [Finset.mem_map_emb] at ha hb
    rw [ha, hb]
  complete := by
    intro (a, b)
    simp [Finset.mem_flatMap_embed, Finset.mem_map_emb]

instance [fa: Fintype α] : Fintype (Option α) :=
  ofEquiv (Equiv.option_equiv_unit_sum α)

end Fintype

@[simp] def Finset.univ_of_unique [Subsingleton α] [Inhabited α]: Finset.univ α = {default} := rfl
