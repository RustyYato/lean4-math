import Math.Data.Set.Lattice
import Math.Relation.RelIso

namespace Set

section

variable (r: α -> α -> Prop)

def Induced (s: Set α) :=
  fun x y: s => r x y

def Induced.embed (s: Set α) : s.Induced r ↪r r where
  toFun x := x.val
  inj := Subtype.val_inj
  resp_rel := Iff.rfl

def Induced.embedSub {s t: Set α} (h: s ⊆ t) : s.Induced r ↪r t.Induced r where
  toFun x := ⟨x.val, h _ x.property⟩
  inj := by
    intro ⟨x, _⟩ ⟨y, _⟩ eq
    dsimp at eq
    cases eq
    rfl
  resp_rel := Iff.rfl

def Induced.embedSInter {s: Set α} {t: Set (Set α)} (h: s ∈ t) : (⋂t).Induced r ↪r s.Induced r where
  toFun x := ⟨x.val, Set.mem_sInter.mp x.property _ h⟩
  inj := by
    intro ⟨x, _⟩ ⟨y, _⟩ eq
    dsimp at eq
    cases eq
    rfl
  resp_rel := Iff.rfl

-- a chain is a set which is trichotomous over it's elements
abbrev IsChain (s: Set α) :=
  Relation.IsTrichotomous (s.Induced r)

def IsSuperChain (s u: Set α) :=
  s ⊆ u ∧ u.IsChain r

def IsStrictSuperChain (s u: Set α) :=
  s ⊂ u ∧ u.IsChain r

def IsMaxChain (s: Set α) :=
  s.IsChain r ∧ ∀x, x.IsChain r -> s ⊆ x -> s = x

namespace IsChain

def empty : (∅: Set α).IsChain r where
  tri x := elim_empty x

def univ [Relation.IsTrichotomous r] : (Set.univ α).IsChain r :=
  (Induced.embed r (Set.univ α)).tri

end IsChain

end

variable {r: α -> α -> Prop}

namespace IsChain

def ofSubset (h: s ⊆ t) (c: IsChain r t) : IsChain r s :=
  (Induced.embedSub r h).tri

def insert (c: IsChain r s) (x: α) (h: ∀y ∈ s, r x y ∨ x = y ∨ r y x) : IsChain r (insert x s) where
  tri := by
    intro ⟨a, amem⟩ ⟨b, bmem⟩
    cases Set.mem_insert.mp amem <;>
    cases Set.mem_insert.mp bmem
    subst a; subst b
    right; left; rfl
    subst a
    rename_i mem
    rcases h b mem with hr | hr | hr
    left; assumption
    right; left; congr
    right; right; assumption
    subst b
    rename_i mem
    rcases h a mem with hr | hr | hr
    right; right; assumption
    right; left; symm; congr
    left; assumption
    rename_i amem bmem
    rcases c.tri ⟨_, amem⟩ ⟨_, bmem⟩ with hr | hr | hr
    left; assumption
    cases hr
    right; left; congr
    right; right; assumption

def sInter {t: Set (Set α)} (h: t.Nonempty) (c: ∀s ∈ t, IsChain r s) : IsChain r (⋂ t) :=
  have ⟨s, mem⟩ := h
  have := c s mem
  (Induced.embedSInter r mem).tri

def inter (cs: IsChain r s) (ct: IsChain r t) : IsChain r (s ∩ t) := by
  rw [←Set.sInter_pair]
  apply sInter
  exact nonempty_insert
  intro x mem
  rcases Set.mem_pair.mp mem with h | h <;> subst x
  assumption
  assumption

end IsChain

open Classical in
noncomputable
def succChain (r: α -> α -> Prop) (s: Set α) :=
  if h:∃t, IsStrictSuperChain r s t then
    Classical.choose h
  else
    s

def succChain.isStrictSuperChain {s: Set α} (h: ∃t, IsStrictSuperChain r s t) :
  IsStrictSuperChain r s (succChain r s) := by
  unfold succChain
  rw [dif_pos h]
  exact Classical.choose_spec h
def succChain.sub (s: Set α) :
  s ⊆ succChain r s := by
  unfold succChain
  split
  rename_i h
  have := Classical.choose_spec h
  exact this.left.right
  rfl
def succChain.isChain' {s: Set α} (h: ∃t, IsStrictSuperChain r s t) :
  IsChain r s := (isStrictSuperChain h).right.ofSubset (sub _)
def succChain.isChain {s: Set α} (h: ∃t, IsStrictSuperChain r s t) :
  IsChain r (succChain r s) := (isStrictSuperChain h).right

def succChain.ofIsMaxChain {s: Set α} (h: IsMaxChain r s) : succChain r s = s := by
  unfold succChain
  rw [dif_neg]
  intro ⟨t, ssup⟩
  exact ssup.left.left <| h.right t ssup.right ssup.left.right

def succChain.toIsMaxChain {s: Set α} (hs: IsChain r s) (h: succChain r s = s) : IsMaxChain r s := by
  unfold succChain at h
  split at h
  rename_i g
  have := Classical.choose_spec g
  rw [h] at this
  have := this.left.left
  contradiction
  clear h
  apply And.intro
  assumption
  intro x c sub
  rename_i g
  rw [not_exists] at g
  have := g x
  unfold IsStrictSuperChain at this
  rw [and_comm, not_and] at this
  replace this : ¬(_ ∧ _) := this c
  rw [and_comm, not_and] at this
  have := this sub
  apply Classical.not_not.mp
  assumption

def exists_succChain_of_not_max_chain (c: IsChain r s) (h: ¬IsMaxChain r s) : ∃t, IsStrictSuperChain r s t := by
  replace ⟨t, h⟩ := Classical.not_forall.mp (not_and.mp h c)
  replace ⟨ct, h⟩ := not_imp.mp h
  replace ⟨s_sub_t, h⟩ := not_imp.mp h
  exists t

def IsChain.succ (c: IsChain r s) : IsChain r (succChain r s) := by
  by_cases h:IsMaxChain r s
  rw [succChain.ofIsMaxChain h]
  assumption
  apply succChain.isChain
  exact exists_succChain_of_not_max_chain c h

inductive ChainClosure (r: α -> α -> Prop): Set α -> Prop where
| union : ∀ {s: Set (Set α)}, (∀ a ∈ s, ChainClosure r a) → ChainClosure r (⋃ s)
| succ : ∀ {s}, ChainClosure r s -> ChainClosure r (succChain r s)

def maxChain (r: α -> α -> Prop) := ⋃ Set.mk (ChainClosure r)

namespace ChainClosure

def empty : ChainClosure r ∅ := by
  rw [←Set.sUnion_empty]
  apply ChainClosure.union
  intros
  contradiction

def maxChain : ChainClosure r (maxChain r) := by
  apply ChainClosure.union
  intros; assumption

def total_aux (cs: ChainClosure r s)
    (h : ∀ ⦃x⦄, ChainClosure r x → x ⊆ t → x = t ∨ succChain r x ⊆ t)
    : s ⊆ t ∨ succChain r t ⊆ s := by
  induction cs with
  | succ =>
    rename_i s cs ih
    rcases ih with ih | ih
    rcases h cs ih with eq | succ_le
    subst t
    right; rfl
    left; assumption
    right
    apply Set.sub_trans ih
    apply succChain.sub
  | union =>
    rename_i s cs ih
    apply Classical.or_iff_not_imp_right.mpr
    intro g
    apply sSup_le _ s
    intro s' s'_in_s
    apply (ih s' s'_in_s).resolve_right
    intro h
    apply g
    apply Set.sub_trans h
    apply le_sSup s
    assumption

def eq_or_succ_sub_of_sub
  (cs: ChainClosure r s) (ct: ChainClosure r t) (h: s ⊆ t): s = t ∨ succChain r s ⊆ t := by
  induction ct generalizing s with
  | succ =>
    rename_i t ct ih
    rcases (total_aux cs (fun _ => ih)) with s_sub_t | succ_t_sub_s
    right
    obtain rfl | succ_s_sub_t := ih cs s_sub_t
    rfl
    apply Set.sub_trans succ_s_sub_t
    apply succChain.sub
    left
    apply Set.sub_antisymm <;> assumption
  | union =>
    rename_i t ct ih
    apply Or.imp_left (Set.sub_antisymm h)
    apply Classical.byContradiction
    have : ⋃t ⊆ s ↔ _ := sSup_le_iff (s := t) (a := s)
    rw [this, not_or, Classical.not_forall]
    intro ⟨⟨x, h₀⟩, h₁⟩
    rw [not_imp] at h₀
    obtain ⟨x_in_t, not_x_sub_s⟩ := h₀
    have cx := ct x x_in_t
    rcases total_aux cs (fun _ => ih x x_in_t) with s_sub_x | succ_x_sub_s
    · obtain rfl | s := ih x x_in_t cs s_sub_x
      contradiction
      rename_i s'
      apply h₁
      apply Set.sub_trans s
      apply Set.sub_sUnion
      assumption
    apply not_x_sub_s
    apply Set.sub_trans _ succ_x_sub_s
    apply succChain.sub

def total (cs: ChainClosure r s) (ct: ChainClosure r t) : s ⊆ t ∨ t ⊆ s := by
  cases total_aux cs (fun _ h => eq_or_succ_sub_of_sub h ct)
  left; assumption
  right
  rename_i h
  apply Set.sub_trans _ h
  apply succChain.sub

def IsChain (c: ChainClosure r s) : IsChain r s := by
  induction c with
  | succ c ih => exact ih.succ
  | union c ih =>
    apply Relation.IsTrichotomous.mk
    intro ⟨a, amem⟩ ⟨b, bmem⟩
    unfold Induced; dsimp
    rw [Set.mem_sUnion] at amem bmem
    obtain ⟨sa, sa_in_s, a_in_sa⟩ := amem
    obtain ⟨sb, sb_in_s, b_in_sb⟩ := bmem
    have sa_chain := ih sa sa_in_s
    have sb_chain := ih sb sb_in_s
    rcases total (c _ sa_in_s) (c _ sb_in_s) with sa_sub_sb | sb_sub_sa
    rcases sb_chain.tri ⟨_, sa_sub_sb _ a_in_sa⟩ ⟨_, b_in_sb⟩ with h | h | h
    left; assumption
    right; left; cases h; congr
    right; right; assumption
    rcases sa_chain.tri ⟨_, a_in_sa⟩ ⟨_, sb_sub_sa _ b_in_sb⟩ with h | h | h
    left; assumption
    right; left; cases h; congr
    right; right; assumption

end ChainClosure

def maxChain_spec : IsMaxChain r (maxChain r) := by
  apply succChain.toIsMaxChain
  apply ChainClosure.IsChain
  apply ChainClosure.maxChain
  apply flip Set.sub_antisymm
  apply succChain.sub
  apply Set.sub_sUnion
  apply ChainClosure.succ
  apply ChainClosure.maxChain

end Set
