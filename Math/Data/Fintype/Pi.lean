import Math.Data.Fintype.Defs

def Pi.all (β: Fin n -> Type _) (f: ∀x, List (β x)) : List (∀x, β x) :=
  match n with
  | 0 => [nofun]
  | n + 1 => by
    apply (f 0).flatMap
    intro b
    apply (Pi.all (β ∘ Fin.succ) (fun x => f x.succ)).map
    intro g
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
      apply Fintype.nodup
      intro b
      apply List.nodup_map
      · intro x y eq
        dsimp at eq
        replace eq := congrFun eq
        funext z
        exact eq z.succ
      apply ih (β ∘ Fin.succ) (f := fun x => f x.succ)
      intro x y xmem ymem z zmemx zmemy
      dsimp at zmemx zmemy
      replace ⟨x₀, _, xeq⟩ := List.mem_map.mp zmemx
      replace ⟨y₀, _, yeq⟩ := List.mem_map.mp zmemy
      clear zmemx zmemy
      exact (congrFun xeq 0).trans (congrFun yeq 0).symm
  complete := by
    intro g
    induction n with
    | zero =>
      have : g = nofun := funext (fun x => x.elim0)
      rw [this]
      apply List.Mem.head
    | succ n ih =>
      apply List.mem_flatMap.mpr
      refine ⟨g 0, ?_⟩
      apply And.intro
      apply Fintype.complete
      apply List.mem_map.mpr
      refine ⟨fun x => g x.succ, ?_⟩
      apply And.intro
      apply ih (β ∘ Fin.succ) (f := fun x => f x.succ)
      funext x
      dsimp
      cases x with | mk x xLt =>
      cases x
      rfl
      rfl

instance Pi.FintypeInst {β: α -> Type _} [DecidableEq α] [fa: Fintype α] [∀x, Fintype (β x)] : Fintype (∀x, β x) := by
  let eqvFin : α ≃ Fin (Fintype.card α) := fa.equivFin
  have := Pi.finArgFintype (fun x => β (eqvFin.invFun x))
  apply Fintype.ofEquiv' (a := (∀x: (Fin (Fintype.card α)), β (eqvFin.invFun x)))
  clear this
  apply Pi.congrEquiv _ _
  symm; assumption
  intro
  rfl
instance Function.FintypeInst [DecidableEq α] [Fintype α] [Fintype β] : Fintype (α -> β) := inferInstance

def Pi.fin_card_eq {β: Fin n -> Type _} [bs: ∀x, Fintype (β x)] :
  (Pi.finArgFintype β).card = (List.product <| (List.finRange n).map (fun x => (bs x).all.length)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv => { lhs; unfold Fintype.card Fintype.all Pi.finArgFintype; dsimp }
    unfold all
    rw [List.length_flatMap]
    rw [List.finRange_succ, List.map_cons, List.product]
    dsimp
    have := ih (β := β ∘ Fin.succ) (bs := fun x => bs x.succ)
    conv at this => { lhs; unfold Fintype.card Fintype.all finArgFintype; dsimp }
    conv => {
      lhs; rhs; arg 1; intro x; erw [List.length_map, this]
    }
    rw [List.map_map, List.sum_const', List.length_map, Nat.mul_comm]
    intro x mem
    have ⟨b₀, _, eq⟩  := List.mem_map.mp mem
    exact eq.symm

def Pi.card_eq {β: α -> Type _} [DecidableEq α] [fa: Fintype α] [bs: ∀x, Fintype (β x)] :
  Fintype.card (∀x, β x) = (List.product <| fa.all.map (fun x => (bs x).all.length)) := by
  rw [Fintype.ofEquiv'_card_eq, Pi.fin_card_eq]
  congr
  cases fa with | mk fa nodup compl =>
  show List.map (fun x => _) (List.finRange fa.length) = List.map (fun x => _) fa
  apply List.ext_getElem
  rw [List.length_map, List.length_map, List.length_finRange]
  intro n h₁ h₂
  rw [List.getElem_map, List.getElem_map]
  unfold Fintype.all
  rw [List.getElem_finRange]
  congr

def Function.card_eq [DecidableEq α] [Fintype α] [Fintype β] :
  Fintype.card (α -> β) = Fintype.card β ^ Fintype.card α := by
  rw [Pi.card_eq, List.product_const']
  congr
  rw [List.length_map]
  rfl
  intro x mem
  have ⟨_,_,_⟩  := List.mem_map.mp mem
  subst x; rfl
