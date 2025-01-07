import Math.TypeTheory.Lambda.OpSem

def LamTerm.IsWellTyped.weakenAll {term: LamTerm} :
  term.IsWellTyped ∅ ty ->
  (∀x ∈ ctx, ¬term.Introduces x) ->
  term.IsWellTyped ctx ty := by
  induction ctx using Map.ind with
  | nil =>
    intro wt h
    assumption
  | cons k v _ nomem ih =>
    intro h g
    have := IsWellTyped.weaken (ih h ?_) (x := ⟨k, v⟩) (g _ ?_)
    simp [insert, dif_neg nomem] at this
    assumption
    intro x mem
    apply g
    apply Map.mem_insert_no_dup.mpr
    left; assumption
    apply Map.mem_insert_no_dup.mpr
    right; rfl

def LamTerm.substAll (term: LamTerm) (substs: Map Name LamTerm) (closed: ∀n (h: n ∈ substs), substs[n].IsWellFormed ∅) : LamTerm := by
  induction substs using Map.rec' with
  | nil => exact term
  | cons k v substs notmem ih =>
    apply (ih ?_).subst v k
    intro n h
    have := closed n (Map.mem_insert_no_dup.mpr <| .inl h)
    rw [Map.insert_nodup_get_elem, dif_neg] at this
    assumption
    intro g
    exact notmem (g ▸ h)
    left; assumption
  | swap k₀ v₀ k₁ v₁ as h₀ h₁ ne ih =>
    apply Function.hfunext
    sorry
    intro g₀ g₁ eq
    apply heq_of_eq
    dsimp
    generalize ih _=ih'
    induction ih' with
    | Panic => sorry
    | Lambda => sorry
    | App => sorry
    | Var =>
      rw [subst]
      split
      rw [LamTerm.subst_closed, subst, if_neg, subst, if_pos]
      assumption
      intro h
      subst h
      contradiction
      have := g₀ k₁ (Map.mem_insert_no_dup.mpr <| .inl <| Map.mem_insert_no_dup.mpr <| .inr rfl)
      rw [Map.insert_nodup_get_elem, dif_neg ne.symm, Map.insert_nodup_get_elem, dif_pos rfl] at this
      assumption
      right; rfl
      left; apply Map.mem_insert_no_dup.mpr
      right; rfl
      sorry
      rw [subst]
      split
      rw [subst_closed]



      repeat sorry
      -- unfold subst
      -- rfl
def LamTerm.substAll_closed (term: LamTerm) :

  term.IsWellFormed ∅ ->
  (∀s ∈ substs, ¬term.Introduces s.fst) ->
  term.substAll substs = term := by
  intro wf nointro
  induction substs generalizing term with
  | nil => rfl
  | cons s _ ih =>
    unfold substAll
    rw [LamTerm.subst_closed]
    apply ih
    assumption
    intro s mem
    apply nointro
    apply List.Mem.tail
    assumption
    assumption
    apply nointro
    apply List.Mem.head

def LamTerm.substAll.Panic (body: LamTerm) (ty: LamType) :
  (LamTerm.Panic body ty).substAll substs =
  LamTerm.Panic (body.substAll substs) ty := by
  induction substs generalizing body with
  | nil => rfl
  | cons s _ ih => apply ih

def LamTerm.substAll.App (func arg: LamTerm) :
  (LamTerm.App func arg).substAll substs =
  LamTerm.App (func.substAll substs) (arg.substAll substs) := by
  induction substs generalizing func arg with
  | nil => rfl
  | cons s _ ih => apply ih

def LamTerm.substAll.Lambda (n: Name) (ty: LamType) (body: LamTerm) :
  (LamTerm.Lambda n ty body).substAll substs =
  LamTerm.Lambda n ty (body.substAll substs) := by
  induction substs generalizing body with
  | nil => rfl
  | cons s _ ih => apply ih

def LamTerm.substAll.Var (n: Name) (v: LamTerm) (h: ⟨n, v⟩ ∈ substs)
  (is_closed: ∀s ∈ substs, s.snd.IsWellFormed ∅)
  (nocomm: substs.Pairwise (fun x y => ¬x.snd.Introduces y.fst))
  (nodup: substs.Pairwise (fun x y => x.fst ≠ y.fst)):
  (LamTerm.Var n).substAll substs = v := by
  induction h with
  | head =>
    unfold substAll subst
    rw [if_pos rfl, substAll_closed]
    apply is_closed ⟨_, _⟩
    apply List.Mem.head
    intro s mem
    apply nocomm.head
    assumption
  | tail s _ ih =>
    unfold substAll subst
    rw [if_neg, ih]
    intro s mem
    apply is_closed
    apply List.Mem.tail
    assumption
    exact nocomm.tail
    exact nodup.tail
    intro h
    subst h
    apply nodup.head
    assumption
    rfl

-- def LamTerm.substAll.Var' (n: Name) (h: ∀v, ⟨n, v⟩ ∉ substs):
--   (LamTerm.Var n).substAll substs = (.Var n) := by
--   induction substs with
--   | nil => rfl
--   | cons s _ ih =>
--     apply ih

structure LamTerm.substAllContext (term: LamTerm) (ctx: Context) (ty: LamType) (substs: List (Name × LamTerm)) where
  -- given a well typed term
  wt: term.IsWellTyped ctx ty
  -- and a context that can be exactly filled by the given substitutions
  eqv: ∀n, n ∈ ctx ↔ ∃t, ⟨n, t⟩ ∈ substs
  -- where every substitution is well typed in the empty context
  -- according to it's label in the term's context
  subst_wt: ∀s (h: s ∈ substs), s.snd.IsWellTyped ∅ <| ctx[s.fst]'((eqv s.fst).mpr ⟨_, h⟩)
  -- and there are no common introduction bindings between the term
  -- and the substitutions (which can always be achieved through
  -- `relabel`)
  term_nocomm: ∀s ∈ substs, term.NoCommonIntroductions s.snd
  -- and there are no common introduction bindings between any
  -- two distinct substitutions (which can always be achieved through
  -- `relabel`)
  nocomm: substs.Pairwise (fun x y => x.snd.NoCommonIntroductions y.snd)
  -- if all elements of the context have a different name from
  -- any binding introduced in the substitution. (which can
  -- also be handled by `relabel`)
  nointro: ∀s ∈ substs, ∀n ∈ ctx, ¬s.snd.Introduces n
  -- and there are no duplicate substitutions
  nodup: substs.Pairwise (fun x y => x.fst ≠ y.fst)

def LamTerm.IsWellTyped.substAll {term: LamTerm} {substs: Map Name LamTerm} :
  LamTerm.substAllContext term ctx ty substs ->
  (term.substAll substs).IsWellTyped ∅ ty := by
  intro substctx
  induction substs generalizing ctx term with
  | nil =>
    induction ctx using Map.ind with
    | nil => exact substctx.wt
    | cons k v =>
      have ⟨_, _⟩ := (substctx.eqv k).mp (Map.mem_insert_no_dup.mpr <| .inr rfl)
      contradiction
  | cons s substs ih =>
    have mem_ctx := (substctx.eqv s.fst).mpr ⟨_, List.Mem.head _⟩
    have ⟨v, ctx, h, eq⟩ := Map.eq_insert_of_mem _ _ mem_ctx; subst eq
    have := IsWellTyped.subst ?_ substctx.wt (name := s.fst) (subst := s.snd) ?_ (substctx.term_nocomm _ (List.Mem.head _))
    rw [Map.erase_insert_no_dup_cancel] at this
    apply ih
    apply substAllContext.mk
    · exact this
    · intro s' mem
      have := substctx.subst_wt _ (List.Mem.tail _ mem)
      rw [Map.insert_nodup_get_elem, dif_neg] at this
      assumption
      exact (substctx.nodup.head s' mem).symm
      left
      have := (substctx.eqv _).mpr ⟨_, List.Mem.tail _ mem⟩
      cases Map.mem_insert_no_dup.mp this
      assumption
      have := (substctx.nodup.head s' mem).symm
      contradiction
    · intro s mem
      intro n it i
      cases LamTerm.Introduces.subst _ it
      apply substctx.term_nocomm
      apply List.Mem.tail
      exact mem
      assumption
      assumption
      apply substctx.nocomm.head
      exact mem
      assumption
      assumption
    · exact substctx.nocomm.tail
    · intro s mem n memctx
      apply substctx.nointro
      apply List.Mem.tail
      assumption
      apply Map.mem_insert_no_dup.mpr
      left; assumption
    · exact substctx.nodup.tail
    · intro n
      replace ctx_eqv := substctx.eqv n
      apply Iff.intro
      intro h
      have ⟨v, mem⟩ := ctx_eqv.mp (Map.mem_insert_no_dup.mpr <| .inl h)
      cases mem
      contradiction
      rename_i mem
      refine ⟨_, mem⟩
      intro ⟨v, h⟩
      have mem := ctx_eqv.mpr ⟨v, List.Mem.tail _ h⟩
      cases Map.mem_insert_no_dup.mp mem
      assumption
      subst n
      have := substctx.nodup.head ⟨s.fst, v⟩ h
      contradiction
    assumption
    rw [Map.insert_nodup_get_elem, dif_pos rfl, Map.erase_insert_no_dup_cancel]
    have  := substctx.subst_wt s (List.Mem.head _)
    rw [Map.insert_nodup_get_elem, dif_pos rfl] at this
    apply weakenAll
    assumption
    intro x mem
    apply substctx.nointro
    apply List.Mem.head
    apply Map.mem_insert_no_dup.mpr
    left; assumption
    right; rfl
    right; rfl

def LamTerm.HeredHalts.substAll {term: LamTerm} {substs: List (Name × LamTerm)}  :
  ∀h: LamTerm.substAllContext term ctx ty substs,
  (term.substAll substs).HeredHalts (IsWellTyped.substAll h) := by
  intro substctx
  induction term with
  | Panic =>
    sorry
  | App =>
    sorry
  | Lambda =>
    sorry
  | Var name =>
    -- let v := substs
    have := substctx.nodup
    conv => { lhs; rw [LamTerm.substAll.Var] }
    sorry
