import Math.Data.Fintype.Impls.List

namespace Fintype

instance instSubtype [f: Fintype α] {P: α -> Prop} [DecidablePred P] : Fintype (Subtype P) := by
  refine f.toRepr.recOnSubsingleton fun f => ?_
  refine Fintype.ofArray ?_ ?_ ?_
  · exact (Array.ofFn f.decode).filterMap (fun x => if h:P x then .some ⟨x, h⟩ else .none)
  · rw [Array.toList_filterMap, Array.toList_ofFn]
    apply List.nodup_filterMap
    apply (List.nodup_ofFn _).mp
    apply f.decode.inj
    intro x y hx h
    split at h <;> split at h
    any_goals contradiction
    exact Subtype.mk.inj (Option.some.inj h)
    split at hx <;> contradiction
  · intro ⟨x, hx⟩
    rw [Array.mem_filterMap]
    exists x
    apply And.intro
    rw [Array.mem_ofFn]
    have ⟨i, h⟩ := f.decode.surj x
    exists i; symm; assumption
    rw [dif_pos]

end Fintype
