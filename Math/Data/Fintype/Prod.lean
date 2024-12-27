import Math.Data.Fintype.Defs

instance {β: α -> Type _} [as: Fintype α] [bs: ∀x, Fintype (β x)] : Fintype ((x: α) × β x) where
  all := as.all.flatMap fun x => (bs x).all.map fun b => ⟨x, b⟩
  complete := by
    intro ⟨a, b⟩
    apply List.mem_flatMap.mpr
    refine ⟨a, as.complete _, ?_⟩
    apply List.mem_map.mpr
    exact ⟨b, (bs _).complete _, rfl⟩
  nodup := by
    apply List.nodup_flatMap
    apply Fintype.nodup
    intro
    apply List.nodup_map
    intro x y eq
    cases eq
    rfl
    apply Fintype.nodup
    intro x y _ _ ⟨a, b⟩ memx memy
    have ⟨Bx, _, eq⟩  := List.mem_map.mp memx
    have ⟨By, _, eq⟩  := List.mem_map.mp memy
    cases eq; cases eq
    rfl

instance [Fintype α] [Fintype β] : Fintype (α × β) :=
  Fintype.ofEquiv Prod.equivSigma

instance {β: α -> Type _} [IsEmpty α] : Fintype ((x: α) × β x) where
  all := []
  nodup := List.Pairwise.nil
  complete := by
    intro ⟨a, _⟩
    have := elim_empty a
    contradiction

instance {β: α -> Type _} [h: ∀x, IsEmpty (β x)] : Fintype ((x: α) × β x) where
  all := []
  nodup := List.Pairwise.nil
  complete := by
    intro ⟨a, b⟩
    have := (h a).elim b
    contradiction

def Sigma.card_eq {β: α -> Type _} (as: Fintype α) (bs: ∀x, Fintype (β x)) :
  Fintype.card ((x: α) × β x) = List.sum (as.all.map fun a => (bs a).card) := by
  cases as with | mk as asnodup ascomplete =>
  unfold Fintype.card Fintype.all instFintypeSigma
  dsimp
  clear asnodup ascomplete
  erw [List.length_flatMap]
  congr
  funext x
  dsimp
  rw [List.length_map]
  rfl

def Prod.card_eq (as: Fintype α) (bs: Fintype β) :
  Fintype.card (α × β) = as.card * bs.card := by
  rw [Fintype.eqCardOfEquiv Prod.equivSigma, Sigma.card_eq as (fun _ => bs)]
  cases as with | mk as asnodup ascomplete =>
  cases bs with | mk bs bsnodup bscomplete =>
  dsimp
  unfold Fintype.card Fintype.all
  dsimp
  clear asnodup ascomplete bsnodup bscomplete
  rw [List.sum_const' (as.map _) bs.length, List.length_map, Nat.mul_comm]
  intro x mem
  have ⟨_, _,_⟩  := List.mem_map.mp mem
  symm; assumption
