import Math.Data.Fintype.Defs

instance [f: Fintype α] : Fintype (Option α) where
  all := .none::f.all.map .some
  nodup := by
    apply List.Pairwise.cons
    intro x mem h
    cases h
    have ⟨_,_,_⟩  := List.mem_map.mp mem
    contradiction
    apply List.nodup_map
    apply Option.some.inj
    apply Fintype.nodup
  complete a := by
    cases a
    apply List.Mem.head
    apply List.Mem.tail
    apply List.mem_map.mpr
    refine ⟨_, ?_, rfl⟩
    apply Fintype.complete

open Fintype in
def Option.card_eq' {f: Fintype α} {fo: Fintype (Option α)} :  card (Option α) = (card α).succ := by
  rw [Fintype.card_eq fo instFintypeOption]
  show Nat.succ _ = _
  congr 1
  rw [List.length_map]
  rfl

open Fintype in
def Option.card_eq [f: Fintype α] [fo: Fintype (Option α)] :  card (Option α) = (card α).succ :=
  card_eq'

def Option.equivFinSucc : Fin (Nat.succ n) ≃ Option (Fin n) where
  toFun x := if h:x = 0 then .none else .some (x.pred h)
  invFun
  | .some x => x.succ
  | .none => 0
  leftInv := by
    intro x
    dsimp
    if h:x = 0 then rw [dif_pos h]; exact h.symm else
    rw [dif_neg h]
    dsimp
    rw [Fin.succ_pred]
  rightInv := by
    intro x
    cases x
    rfl
    dsimp
    rw [dif_neg]
    rw [Fin.pred_succ]
    intro h
    have := Fin.succ_ne_zero _ h
    contradiction
