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

def LamTerm.substAll (term: LamTerm) : List (Name × LamTerm) -> LamTerm
| [] => term
| ⟨name, subst⟩::substs => (term.subst subst name).substAll substs

def LamTerm.IsWellTyped.substAll {term: LamTerm} {substs: List (Name × LamTerm)} :
  -- given a well typed term
  term.IsWellTyped ctx ty ->
  -- and a context that can be exactly filled by the given substitutions
  (eqv: ∀n, n ∈ ctx ↔ ∃t, ⟨n, t⟩ ∈ substs) ->
  -- where every substitution is well typed in the empty context
  -- according to it's label in the term's context
  (∀s (h: s ∈ substs), s.snd.IsWellTyped ∅ <| ctx[s.fst]'((eqv s.fst).mpr ⟨_, h⟩)) ->
  -- and there are no common introduction bindings between the term
  -- and the substitutions (which can always be achieved through
  -- `relabel`)
  (∀s ∈ substs, term.NoCommonIntroductions s.snd) ->
  -- and there are no common introduction bindings between any
  -- two distinct substitutions (which can always be achieved through
  -- `relabel`)
  substs.Pairwise (fun x y => x.snd.NoCommonIntroductions y.snd) ->
  -- if all elements of the context have a different name from
  -- any binding introduced in the substitution. (which can
  -- also be handled by `relabel`)
  (∀s ∈ substs, ∀n ∈ ctx, ¬s.snd.Introduces n) ->
  -- and there are no duplicate substitutions
  substs.Pairwise (fun x y => x.fst ≠ y.fst) ->
  -- then the term with all substitutions applied is well typed in the empty context
  (term.substAll substs).IsWellTyped ∅ ty := by
  intro wt ctx_eqv subst_wt nocomm nocomm' nointro nodup
  induction substs generalizing ctx term with
  | nil =>
    induction ctx using Map.ind with
    | nil => assumption
    | cons k v =>
      have ⟨_, _⟩ := (ctx_eqv k).mp (Map.mem_insert_no_dup.mpr <| .inr rfl)
      contradiction
  | cons s substs ih =>
    cases nodup
    rename_i nodup nodup'
    cases nocomm'
    rename_i nocomm' nocomm'₀
    have mem_ctx := (ctx_eqv s.fst).mpr ⟨_, List.Mem.head _⟩
    have ⟨v, ctx, h, eq⟩ := Map.eq_insert_of_mem _ _ mem_ctx; subst eq
    have := IsWellTyped.subst ?_ wt (name := s.fst) (subst := s.snd) ?_ (nocomm _ (List.Mem.head _))
    rw [Map.erase_insert_no_dup_cancel] at this
    apply ih this
    · intro s' mem
      have := subst_wt _ (List.Mem.tail _ mem)
      rw [Map.insert_nodup_get_elem, dif_neg] at this
      assumption
      exact (nodup' s' mem).symm
      left
      have := (ctx_eqv _).mpr ⟨_, List.Mem.tail _ mem⟩
      cases Map.mem_insert_no_dup.mp this
      assumption
      have := (nodup' s' mem).symm
      contradiction
    · intro s mem
      have := nocomm
      intro n it i
      cases LamTerm.Introduces.subst _ it
      apply nocomm
      apply List.Mem.tail
      exact mem
      assumption
      assumption
      apply nocomm'₀
      exact mem
      assumption
      assumption
    · exact nocomm'
    · intro s mem n memctx
      apply nointro
      apply List.Mem.tail
      assumption
      apply Map.mem_insert_no_dup.mpr
      left; assumption
    · exact nodup
    · intro n
      replace ctx_eqv := ctx_eqv n
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
      have := nodup' ⟨s.fst, v⟩ h
      contradiction
    assumption
    rw [Map.insert_nodup_get_elem, dif_pos rfl, Map.erase_insert_no_dup_cancel]
    have  := subst_wt s (List.Mem.head _)
    rw [Map.insert_nodup_get_elem, dif_pos rfl] at this
    apply weakenAll
    assumption
    intro x mem
    apply nointro
    apply List.Mem.head
    apply Map.mem_insert_no_dup.mpr
    left; assumption
    right; rfl
    right; rfl
