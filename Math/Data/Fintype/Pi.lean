import Math.Data.Fintype.Basic


def Pi.all (β: Fin n -> Type _) (f: ∀x, List (β x)) : List (∀x, β x) :=
  match n with
  | 0 => [nofun]
  | n + 1 => by
    apply (Pi.all (β ∘ Fin.succ) (fun x => f x.succ)).flatMap
    intro g
    apply (f 0).map
    intro b
    intro x
    match x with
    | ⟨x, xLt⟩ =>
    match x with
    | 0 => exact b
    | x + 1 =>
      apply g ⟨_, _⟩
      apply Nat.lt_of_succ_lt_succ
      assumption

def Pi.finArgFintype (β: Fin n -> Type _) [f: ∀x, Fintype (β x)] : Fintype (∀x, β x) where
  all := Pi.all _ (fun x => (f x).all)
  nodup := by
    induction n with
    | zero =>
      apply List.Pairwise.cons
      intros; contradiction
      apply List.Pairwise.nil
    | succ n ih =>
      apply List.nodup_flatMap
      apply ih (β ∘ Fin.succ) (f := fun x => f x.succ)
      intro g
      apply List.nodup_map
      · intro x y eq
        dsimp at eq
        exact congrFun eq 0
      apply Fintype.nodup
      intro x y xmem ymem z zmemx zmemy
      dsimp at zmemx zmemy
      replace ⟨x₀, _, xeq⟩ := List.mem_map.mp zmemx
      replace ⟨y₀, _, yeq⟩ := List.mem_map.mp zmemy
      funext n
      have := congrFun xeq n.succ
      dsimp at this
      rw [this]
      have := congrFun yeq n.succ
      dsimp at this
      rw [this]
  complete := by
    intro g
    induction n with
    | zero =>
      have : g = nofun := funext (fun x => x.elim0)
      rw [this]
      apply List.Mem.head
    | succ n ih =>
      apply List.mem_flatMap.mpr
      refine ⟨fun x => g x.succ, ?_⟩
      apply And.intro
      dsimp
      apply ih (β ∘ Fin.succ) (f := fun x => f x.succ)
      apply List.mem_map.mpr
      exists g 0
      apply And.intro
      apply Fintype.complete
      funext x
      dsimp
      cases x with | mk x xLt =>
      cases x
      rfl
      rfl

instance {β: α -> Type _} [DecidableEq α] [fa: Fintype α] [∀x, Fintype (β x)] : Fintype (∀x, β x) := by
  let eqvFin : α ≃ Fin (Fintype.card α) := fa.equivFin
  have := Pi.finArgFintype (fun x => β (eqvFin.invFun x))
  apply Fintype.ofEquiv (a := (∀x: (Fin (Fintype.card α)), β (eqvFin.invFun x)))
  clear this
  apply Pi.congrEquiv _ _
  symm; assumption
  intro
  rfl
instance [DecidableEq α] [Fintype α] [Fintype β] : Fintype (α -> β) := inferInstance
