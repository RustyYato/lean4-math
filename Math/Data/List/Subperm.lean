namespace List

inductive Subperm : List α -> List α -> Prop where
| nil : Subperm [] as
| cons : Subperm as bs -> Subperm (x::as) (x::bs)
| trans : Subperm as bs -> Subperm bs cs -> Subperm as cs
| swap: Subperm (x::y::as) (y::x::as)

scoped infix:25 " <~+ " => Subperm

def of_subperm_nil (h: as <~+ []) : as = [] := by
  generalize hbs:[] = bs
  rw [←hbs]
  rw [hbs] at h
  induction h with
  | cons => contradiction
  | swap => contradiction
  | nil => rfl
  | trans _ _ ih₀ ih₁ =>
    cases hbs
    cases ih₁ rfl
    exact ih₀ rfl

def subperm_of_perm {as bs: List α}: as ~ bs -> as <~+ bs := by
  intro h
  induction h with
  | nil => apply Subperm.nil
  | cons => apply Subperm.cons; assumption
  | swap => apply Subperm.swap
  | trans => apply Subperm.trans <;> assumption

def subperm_of_append_left {as bs: List α}: as <~+ (as ++ bs) := by
  induction as with
  | nil => apply Subperm.nil
  | cons => apply Subperm.cons; assumption

def subperm_of_sublist {as bs: List α} : as <+ bs -> as <~+ bs := by
  intro h
  induction h with
  | slnil => apply Subperm.nil
  | cons x _ ih =>
    rename_i as bs _
    apply Subperm.trans ih
    apply Subperm.trans
    show bs <~+ bs ++ [x]
    apply subperm_of_append_left
    apply subperm_of_perm
    apply Perm.symm
    apply perm_cons_append_cons
    rw [List.append_nil]
  | cons₂ =>
    apply Subperm.cons
    assumption

def extract_of_mem (h: x ∈ as) : ∃as', as' <+ as ∧ as ~ x::as' := by
  induction h with
  | head as =>
    exists as
    apply And.intro
    apply Sublist.cons
    apply Sublist.refl
    rfl
  | tail a _ ih =>
    obtain ⟨as', as'_sub, perm⟩ := ih
    exists a::as'
    apply And.intro
    apply Sublist.cons₂
    assumption
    apply flip Perm.trans
    apply Perm.swap
    apply Perm.cons
    assumption

def subperm_of_sublist_of_perm (h: as ~ bs) (g: as' <+ as) : ∃bs', bs' <+ bs ∧ as' ~ bs' := by
  induction g generalizing bs with
  | slnil =>
    cases h.nil_eq
    exists []
    apply And.intro
    apply Sublist.refl
    rfl
  | cons =>
    rename_i bs₀ bs₁ x sub ih
    have ⟨bs₂, bs₂_sub_bs, bs_perm_bs₂⟩  := extract_of_mem (h.mem_iff.mp (List.Mem.head _))
    have bs₁_perm_bs₂ := (h.trans bs_perm_bs₂).cons_inv
    have ⟨bs', bs'_sub_bs₂, bs₀_perm_bs'⟩ := ih bs₁_perm_bs₂
    exists bs'
    apply And.intro
    apply Sublist.trans
    assumption
    assumption
    assumption
  | cons₂ =>
    rename_i bs₀ bs₁ x bs₀_sub_bs₁ ih
    have ⟨bsl, bsr, eq⟩  := append_of_mem (h.mem_iff.mp (List.Mem.head _))
    subst eq
    have : [x] ++ bsl ++ bsr ~ bsl ++ x::bsr := by
      have : x::bsr = [x] ++ bsr := rfl
      rw [this]; clear this
      rw [←List.append_assoc]
      apply (perm_append_right_iff _).mpr
      apply perm_append_comm
    replace := h.trans this.symm
    replace : _ ~ ([] ++ bsl) ++ bsr := Perm.cons_inv this
    rw [List.nil_append] at this
    replace ⟨bs, bs_sub_bsl_bsr, bs₀_perm_bs⟩ := ih this
    have ⟨bsl₀, bsr₀, eq, bsl₀_sub_bsl, bsr₀_sub_bsr⟩ := sublist_append_iff.mp bs_sub_bsl_bsr
    subst bs; clear bs_sub_bsl_bsr
    exists bsl₀ ++ x::bsr₀
    apply And.intro
    apply sublist_append_iff.mpr
    refine ⟨bsl₀, x::bsr₀, rfl, ?_, ?_⟩
    assumption
    apply Sublist.cons₂
    assumption
    apply Perm.trans
    apply Perm.cons
    assumption
    refine perm_cons_append_cons x ?_
    rfl

private
def Subperm.spec' (h: as <~+ bs): ∃bs', bs' <+ bs ∧ as ~ bs' := by
  induction h with
  | nil =>
    exists []
    apply And.intro
    apply nil_sublist
    rfl
  | swap =>
    rename_i x y zs
    exists y::x::zs
    apply And.intro
    apply Sublist.refl
    apply Perm.swap
  | cons _ ih =>
    rename_i x _
    obtain ⟨bs', sublist, perm⟩ := ih
    exists (x::bs')
    apply And.intro
    apply Sublist.cons₂
    assumption
    apply List.Perm.cons
    assumption
  | trans _ _ ih₀ ih₁ =>
    rename_i as bs cs as_bs bs_cs; show ∃cs', _
    obtain ⟨bs', bs'_sub_bs, as_perm_bs'⟩ := ih₀
    obtain ⟨cs', cs'_sub_cs, bs_perm_cs'⟩ := ih₁
    have ⟨cs₀, cs₀_sub_cs', bs'_perm_cs₀⟩   := subperm_of_sublist_of_perm bs_perm_cs' bs'_sub_bs
    exists cs₀
    apply And.intro
    apply cs₀_sub_cs'.trans
    assumption
    apply as_perm_bs'.trans
    assumption

def Subperm.spec {as bs: List α} : as <~+ bs ↔ ∃bs', bs' <+ bs ∧ as ~ bs' := by
  apply Iff.intro
  apply Subperm.spec'
  intro ⟨cs, cs_sub_bs, as_perm_cs⟩
  exact (subperm_of_perm as_perm_cs).trans (subperm_of_sublist cs_sub_bs)

def Subperm.refl {as: List α} : as <~+ as := by
  induction as with
  | nil => exact Subperm.nil
  | cons a as ih => exact Subperm.cons ih

def Subperm.cons_inv {as bs: List α} : x::as <~+ x::bs -> as <~+ bs := by
  intro h
  obtain ⟨cs, cs_sub, perm_as⟩ := Subperm.spec.mp h; clear h
  cases sublist_cons_iff.mp cs_sub <;> (clear cs_sub; rename_i cs_sub)
  exact (subperm_of_sublist (sublist_cons_self _ _)).trans (subperm_of_perm perm_as)
    |>.trans (subperm_of_sublist cs_sub)
  obtain ⟨cs, eq, cs_sub_bs⟩ := cs_sub; subst eq
  exact subperm_of_perm (perm_as.cons_inv) |>.trans (subperm_of_sublist cs_sub_bs)

def Subperm.antisymm {as bs: List α} (h: as <~+ bs) (g: bs <~+ as) : as ~ bs := by
  induction h with
  | nil => rw [of_subperm_nil g]
  | swap => apply Perm.swap
  | cons h ih =>
    apply Perm.cons
    apply ih g.cons_inv
  | trans _ _ ih₀ ih₁ =>
    apply Perm.trans
    apply ih₀
    apply Subperm.trans
    assumption
    assumption
    apply ih₁
    apply Subperm.trans
    assumption
    assumption

end List
