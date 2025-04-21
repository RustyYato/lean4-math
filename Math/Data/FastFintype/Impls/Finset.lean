import Math.Data.FastFintype.Defs
import Math.Data.Finset.Basic

instance (s: Finset α) : Fintype s :=
  match s with
  | .mk s nodup =>
  s.recOnSubsingleton (motive := fun s: Multiset α => s.Nodup -> Fintype { x: α // x ∈ s }) (fun s nodup =>
  (Fintype.mk ∘ Trunc.mk) {
    card := s.length
    all := {
      toFun i := ⟨s[i], List.mem_of_getElem rfl⟩
      inj' := by
        intro x y h
        apply Fin.val_inj.mp
        apply List.nodup_getElem_inj
        assumption
        dsimp at h
        exact Subtype.mk.inj h
    }
    complete := by
      intro ⟨x, hx⟩
      simp
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      exists ⟨i, hi⟩
  }) nodup
