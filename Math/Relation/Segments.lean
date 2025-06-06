import Math.Relation.RelIso
import Math.Data.Set.Basic

open Relation

variable {α β: Type*} {r: α -> α -> Prop} {s: β -> β -> Prop} {t: γ -> γ -> Prop}

def RelEmbedding.IsPrincipalTop (h: r ↪r s) (top: β): Prop := ∀b: β, s b top ↔ b ∈ Set.range h

structure InitialSegment (r: α -> α -> Prop) (s: β -> β -> Prop) extends r ↪r s where
  isInitial: ∀a b, s b (toRelEmbedding a) -> b ∈ Set.range toRelEmbedding

structure PrincipalSegment (r: α -> α -> Prop) (s: β -> β -> Prop) extends r ↪r s where
  exists_top: ∃top: β, toRelEmbedding.IsPrincipalTop top

infixl:25 " ≼i " => InitialSegment
infixl:25 " ≺i " => PrincipalSegment

abbrev init_seg_le (α β: Type*) [LE α] [LE β] := @InitialSegment α β (· ≤ ·) (· ≤ ·)
abbrev init_seg_lt (α β: Type*) [LT α] [LT β] := @InitialSegment α β (· < ·) (· < ·)

infixl:25 " ≤i " => init_seg_le
infixl:25 " <i " => init_seg_lt

instance : FunLike (InitialSegment r s) α β where
  coe f := f.toFun
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ eq
    congr
    exact DFunLike.coe_inj eq

instance : FunLike (PrincipalSegment r s) α β where
  coe f := f.toFun
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ eq
    congr
    exact DFunLike.coe_inj eq

namespace InitialSegment

@[simp] def toEmbedding_eq_coe (h: r ≼i s) : (h.toEmbedding: _ -> _) = h := rfl
@[simp] def toRelEmbedding_eq_coe (h: r ≼i s) : (h.toRelEmbedding: _ -> _) = h := rfl
@[simp] def toFun_eq_coe (h: r ≼i s) : (h.toFun: _ -> _) = h := rfl

def inj (h: r ≼i s) : Function.Injective h := h.toEmbedding.inj

@[coe]
def ofRelIso (h: r ≃r s) : r ≼i s where
  toRelEmbedding := h.toEmbedding
  isInitial a b sb := by
    replace sb : s b (h a) := sb
    show b ∈ Set.range h
    exists h.symm b
    simp

instance : Coe (r ≃r s) (r ≼i s) := ⟨ofRelIso⟩

def refl (r: α -> α -> Prop) : r ≼i r where
  toRelEmbedding := RelEmbedding.refl
  isInitial _ _ _ := Set.mem_range.mpr ⟨_, rfl⟩

@[ext]
def ext (a b: r ≼i s) : (∀x, a x = b x) -> a = b := DFunLike.ext a b

def trans (h: r ≼i s) (g: s ≼i t): r ≼i t where
  toRelEmbedding := RelEmbedding.trans h.toRelEmbedding g.toRelEmbedding
  isInitial := by
    intro a b t₀
    have ⟨b₀, b_eq⟩ := Set.mem_range.mp <| g.isInitial _ _ t₀
    subst b
    have s₀ := g.resp_rel.mpr t₀
    have ⟨a₀, a_eq⟩ := Set.mem_range.mp <| h.isInitial _ _ s₀
    subst b₀
    apply Set.mem_range.mpr
    exact ⟨_, rfl⟩

instance [IsConnected s] [IsIrrefl s] [IsWellFounded r] : Subsingleton (r ≼i s) where
  allEq := by
    intro a b
    ext x
    induction x using (wellFounded r).induction with
    | h x ih =>
    apply extensional_of_trichotomous_of_irrefl s
    intro y
    apply Iff.intro
    intro s₀
    have ⟨y₀, eq⟩ := Set.mem_range.mp <| a.isInitial x y s₀
    subst y
    show s (a y₀) (b x)
    rw [ih]
    apply b.resp_rel.mp
    apply a.resp_rel.mpr
    assumption
    apply a.resp_rel.mpr
    assumption

    intro s₀
    have ⟨y₀, eq⟩ := Set.mem_range.mp <| b.isInitial x y s₀
    subst y
    show s (b y₀) (a x)
    rw [←ih]
    apply a.resp_rel.mp
    apply b.resp_rel.mpr
    assumption
    apply b.resp_rel.mpr
    assumption

instance [IsWellOrder s] : Subsingleton (r ≼i s) :=
  ⟨fun a => by let _ := a.toRelHom.wf; exact Subsingleton.elim a⟩

def eq [IsWellOrder s] (f g : r ≼i s) (a) : f a = g a := by
  rw [Subsingleton.elim f g]

def antisymm_aux [IsWellOrder r] (f : r ≼i s) (g: s ≼i r) : Function.IsRightInverse f g :=
  eq (f.trans g) (.refl _)

def antisymm [IsWellOrder r] (f : r ≼i s) (g: s ≼i r) : r ≃r s where
  toFun := f
  invFun := g
  leftInv := f.antisymm_aux g
  rightInv :=
    have := g.toRelEmbedding.lift_wo
    g.antisymm_aux f
  resp_rel := f.resp_rel

def eqv_or_principal [IsWellOrder s] (h: r ≼i s) :
  Function.Surjective h ∨ ∃b, ∀x, s x b ↔ x ∈ Set.range h := by
  apply Classical.or_iff_not_imp_right.mpr
  intro g b
  induction b using (wellFounded s).induction with
  | h b ih =>
  apply Classical.not_forall_not.mp
  intro f
  refine g ⟨b, ?_⟩
  intro b'
  apply Iff.intro
  intro sb'b
  apply Set.mem_range.mpr
  exact ih b' sb'b
  intro mem
  have ⟨a, eq⟩ := Set.mem_range.mp mem
  subst b'
  rcases connected s (h a) b with ab | eq | ba
  assumption
  have := f _ eq.symm
  contradiction
  have ⟨a', eq⟩ := Set.mem_range.mp <| h.isInitial _ _ ba
  have := f _ eq
  contradiction

def congr (eqr: r₀ ≃r r₁) (eqs: s₀ ≃r s₁) (g: r₀ ≼i s₀): r₁ ≼i s₁ where
  toRelEmbedding := g.toRelEmbedding.congr eqr eqs
  isInitial := by
    intro a b  s'
    rw [RelEmbedding.congr_apply] at s'
    have : s₀ (eqs.symm b) (eqs.symm _) := eqs.symm.resp_rel.mp s'
    rw [eqs.coe_symm] at this
    have ⟨a', eq⟩ := Set.mem_range.mp <| g.isInitial _ _ this
    apply Set.mem_range.mpr
    exists eqr a'
    rw [RelEmbedding.congr_apply]
    rw [eqr.coe_symm, ←eq, eqs.symm_coe]

section collapse

private noncomputable
def collapse_helper [IsWellOrder s] (f: r ↪r s) : ∀ a, { b // ¬s (f a) b } := by
  refine f.toRelHom.wf.wf.fix fun a ih => ?_
  let S := Set.mk fun b => ∀a₀ h, s (ih a₀ h).1 b
  have : f a ∈ S := by
    intro a' h
    have := (ih a' h).property
    rcases connected s (ih a' h) (f a) with s' | eq | s'
    assumption
    rw [eq] at this
    have : ¬r a' a := (this <| f.resp_rel.mp ·)
    contradiction
    exfalso
    apply this
    apply IsTrans.trans _ s'
    apply f.resp_rel.mp
    assumption
  have g: S.Nonempty := ⟨_, this⟩
  refine ⟨S.min s g, ?_⟩
  apply Set.not_lt_min s g
  assumption

private
def collapse_helper_lt [IsWellOrder s] (f: r ↪r s) :
∀a a', r a' a -> s (collapse_helper f a') (collapse_helper f a) := by
  intro a
  show (collapse_helper f a).1 ∈ Set.mk fun b => ∀ (a') (_ : r a' a), s (collapse_helper f a').1 b
  unfold collapse_helper; rw [WellFounded.fix_eq]
  dsimp only; apply Set.min_mem

private
theorem collapse_helper_not_lt [IsWellOrder s] (f : r ↪r s) (a : α) {b}
    (h : ∀ a' (_ : r a' a), s (collapse_helper f a').1 b) : ¬s b (collapse_helper f a).1 := by
  unfold collapse_helper; rw [WellFounded.fix_eq]
  dsimp only
  exact Set.not_lt_min _ _ _ h

def collapse [IsWellOrder s] (f: Nonempty (r ↪r s)) : Nonempty (r ≼i s) := by
  obtain ⟨f⟩ := f
  have := f.lift_wo
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
  intro a
  exact (collapse_helper f a).val
  intro x y eq
  dsimp at eq
  apply eq_of_not_lt_or_gt r
  intro h
  have := collapse_helper_lt f _ _ h
  rw [eq] at this
  exact irrefl this
  intro h
  have := collapse_helper_lt f _ _ h
  rw [eq] at this
  exact irrefl this
  intro a b
  dsimp
  apply Iff.intro
  apply collapse_helper_lt
  intro h
  rcases connected r a b with ab | eq | ba
  assumption
  rw [eq] at h
  exact (irrefl h).elim
  exact (asymm h <| collapse_helper_lt _ _ _ ba).elim
  intro a b h
  replace h : s _ (collapse_helper _ _).val := h
  apply Set.mem_range.mpr
  show ∃_, _ = (collapse_helper _ _).val
  let S := Set.mk fun a => ¬s (collapse_helper f a).val b
  have : S.Nonempty := ⟨_, asymm h⟩
  have ⟨a', a'_inS, a'_min⟩ := S.exists_min_elem r this
  exists a'
  apply flip (eq_of_not_lt_or_gt s _ _)
  assumption
  apply collapse_helper_not_lt
  intro x rxa
  apply Classical.byContradiction
  intro g
  apply a'_min _ g rxa

end collapse

end InitialSegment

namespace PrincipalSegment

@[simp] def toEmbedding_eq_coe (h: r ≺i s) : (h.toEmbedding: _ -> _) = h := rfl
@[simp] def toRelEmbedding_eq_coe (h: r ≺i s) : (h.toRelEmbedding: _ -> _) = h := rfl
@[simp] def toFun_eq_coe (h: r ≺i s) : (h.toFun: _ -> _) = h := rfl

def inj (h: r ≺i s) : Function.Injective h := h.toEmbedding.inj

theorem init [IsTrans s] (f : r ≺i s) (a : α) (b : β) (h : s b (f a)) : b ∈ Set.range f := by
  obtain ⟨top, down⟩  := f.exists_top
  apply (down _).mp
  apply IsTrans.trans h
  apply (down _).mpr
  apply Set.mem_range'

instance toPrincipal [IsTrans s] : Coe (r ≺i s) (r ≼i s) where
  coe h := ⟨h.toRelEmbedding, h.init⟩

def lt_of_lt_of_le (h: r ≺i s) (g: s ≼i t): r ≺i t where
  toRelEmbedding := h.toRelEmbedding.trans g.toRelEmbedding
  exists_top := by
    obtain ⟨top, lt_top⟩ := h.exists_top
    refine ⟨g top, ?_⟩
    intro x
    apply Iff.intro
    intro tx
    have ⟨x, eq⟩ := Set.mem_range.mp <| g.isInitial _ _ tx
    subst eq
    replace tx := g.resp_rel.mpr tx
    have := (lt_top _).mp tx
    apply Set.range_comp
    assumption
    intro mem
    obtain ⟨x, eq⟩  := Set.mem_range.mp mem
    subst eq
    apply g.resp_rel.mp
    apply (lt_top _).mpr
    apply Set.mem_range'

def congr (eqr: r₀ ≃r r₁) (eqs: s₀ ≃r s₁) (g: r₀ ≺i s₀): r₁ ≺i s₁ where
  toRelEmbedding := g.toRelEmbedding.congr eqr eqs
  exists_top := by
    obtain ⟨top, lt_top⟩ := g.exists_top
    exists eqs top
    intro b
    apply Iff.intro
    intro h
    have : s₀ (eqs.symm b) (eqs.symm (eqs top)) := eqs.symm.resp_rel.mp h
    rw [eqs.coe_symm] at this
    have := (lt_top _).mp this
    have ⟨a', eq⟩ := Set.mem_range.mp this
    apply Set.mem_range.mpr
    exists eqr a'
    rw [RelEmbedding.congr_apply, eqr.coe_symm, ←eq, eqs.symm_coe]
    intro mem
    have ⟨a', eq⟩ := Set.mem_range.mp mem
    subst b
    apply eqs.resp_rel.mp
    apply (lt_top _).mpr
    apply Set.mem_range'

def trans [IsTrans t] (h: r ≺i s) (g: s ≺i t) : r ≺i t := lt_of_lt_of_le h g

def coe_initial_seg_inj [IsTrans s] : Function.Injective (fun x: r ≺i s => (x: r ≼i s)) := by
  intro x y eq
  cases x; cases y
  cases eq
  congr

instance [IsWellOrder s] : Subsingleton (r ≺i s) where
  allEq a b := by
    apply coe_initial_seg_inj
    apply Subsingleton.allEq

theorem irrefl {r : α → α → Prop} [IsWellOrder r] (f : r ≺i r) : False := by
  have ⟨top, lt_top⟩ := f.exists_top
  have h := (lt_top top).trans Set.mem_range
  have : f top = top := InitialSegment.eq (↑f) (InitialSegment.refl r) top
  have := h.mpr ⟨_, this.symm⟩
  exact (wellFounded r).irrefl this

instance (r : α → α → Prop) [IsWellOrder r] : IsEmpty (r ≺i r) :=
  ⟨fun f => f.irrefl⟩

def top_congr [IsWellOrder t] (e : r ≃r s) (f : r ≺i t)
  : ∀x, f.IsPrincipalTop x -> (f.congr e RelIso.refl).IsPrincipalTop x := by
  intro x xtop
  intro y
  apply (xtop y).trans
  rw [Set.mem_range, Set.mem_range]
  apply Iff.intro
  intro ⟨y, eq⟩
  subst eq
  exists e y
  show f y = f (e.symm (e y))
  rw [e.coe_symm]
  intro ⟨x, eq⟩
  subst eq
  exists e.symm x

def top_unique' [IsWellOrder t] (f: s ≺i t)
  : ∀x y, f.IsPrincipalTop x -> f.IsPrincipalTop y -> x = y := by
  intro x y xtop ytop
  unfold RelEmbedding.IsPrincipalTop at xtop ytop
  apply extensional_of_trichotomous_of_irrefl t
  intro z
  rw [xtop, ytop]

def top_unique [IsWellOrder t] (e : r ≃r s) (f : r ≺i t) (g : s ≺i t)
  : ∀x y, f.IsPrincipalTop x -> g.IsPrincipalTop y -> x = y := by
  intro x y xtop ytop
  let g' := f.congr e RelIso.refl
  have : g' = g := Subsingleton.allEq _ _
  subst g
  symm; apply top_unique' g'
  exact ytop
  apply top_congr
  assumption

def top_of_lt_of_lt_of_le [IsWellOrder t] (h : r ≺i s) (g : s ≼i t) : ∀x, h.IsPrincipalTop x -> (h.lt_of_lt_of_le g).IsPrincipalTop (g x) := by
  intro x top y
  rw [Set.mem_range]
  apply Iff.intro
  intro tyx
  show ∃_, y = g (h _)
  have ⟨y, eq⟩ := Set.mem_range.mp <| g.isInitial _ _ tyx
  subst eq
  replace tyx := g.resp_rel.mpr tyx
  have ⟨y, eq⟩ := Set.mem_range.mp <| (top y).mp tyx
  exists y
  rw [eq]; rfl
  intro ⟨y, eq⟩
  subst eq
  show (t (g (h _))) _
  apply g.resp_rel.mp
  apply (top _).mpr
  apply Set.mem_range'

def top_of_trans [IsWellOrder t] (h : r ≺i s) (g : s ≺i t) : ∀x, h.IsPrincipalTop x -> (h.trans g).IsPrincipalTop (g x) := by
  let h₀ := h.lt_of_lt_of_le (g: s ≼i t)
  let h₁ := h.trans g
  have : h₀ = h₁ := Subsingleton.allEq _ _
  show ∀x, h.IsPrincipalTop x -> h₀.IsPrincipalTop _
  rw [this]
  apply top_of_lt_of_lt_of_le

end PrincipalSegment

namespace RelIso

def toInitial (h: r ≃r s) : r ≼i s where
  toRelEmbedding := h.toRelEmbedding
  isInitial := by
    intros a b sb
    apply Set.mem_range.mpr
    refine ⟨h.symm b, ?_⟩
    show _ = h (h.symm _)
    rw [h.symm_coe]

def toInitial_inj : Function.Injective (toInitial (r := r) (s := s)) := by
  intro ⟨x, _⟩ ⟨y, _⟩ eq
  congr
  have : x.toFun = y.toFun := Embedding.mk.inj (RelEmbedding.mk.inj (InitialSegment.mk.inj eq))
  apply DFunLike.coe_inj
  exact this

instance [IsWellOrder s] : Subsingleton (r ≃r s) where
  allEq := by
    intro a b
    apply toInitial_inj
    apply Subsingleton.allEq

end RelIso

def Subtype.initalSegment {P: α -> Prop} (r: α -> α -> Prop) (h: ∀x y, P x -> r y x -> P y) : (fun a b: Subtype P => r a b) ≼i r where
  toRelEmbedding := Subtype.relEmbed _
  isInitial := by
    intro ⟨x, Px⟩ y ryx
    replace ryx : r y x := ryx
    apply Set.mem_range.mpr
    refine ⟨⟨y, ?_⟩, rfl⟩
    apply h
    assumption
    assumption
