import Math.Data.Fintype.Array

instance (as: { x: List α // x.Nodup }) : Fintype as.val where
  all := as.val.attach
  nodup := (List.nodup_attach _).mp as.property
  complete := by
    intro ⟨x, mem⟩
    apply List.mem_attach

instance (priority := 100) [DecidableEq α] (as: List α) : Fintype as where
  all := as.attach.dedup
  nodup := List.nodup_dedup _
  complete := by
    intro ⟨x, mem⟩
    apply List.mem_dedup.mp
    apply List.mem_attach

def List.Elem.nodup_card_eq {as: { x: List α // x.Nodup }} (f: Fintype as) : f.card = as.val.length := by
  rw [Fintype.card_eq _ (instFintypeElemValListNodup _)]
  show List.length (List.attach _) = _
  rw [List.length_attach]

-- def List.Elem.card_le [DecidableEq α] {as: List α} (f: Fintype as) : f.card ≤ as.length := by
--   rw [Fintype.card_eq _ (instFintypeElemOfDecidableEq _)]
--   show List.length (List.dedup _) ≤ _
--   sorry
