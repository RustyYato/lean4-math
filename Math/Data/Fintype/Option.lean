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
