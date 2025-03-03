import Math.Data.Fintype.Defs
import Math.Data.Set.Basic
import Math.Logic.Equiv.Basic
import Math.Logic.IsEmpty

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

end Fintype
