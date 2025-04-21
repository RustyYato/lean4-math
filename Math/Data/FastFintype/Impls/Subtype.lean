import Math.Data.FastFintype.Defs
import Math.Data.List.Defs

def Array.getElem_inj (a: Array α) (h: a.toList.Nodup) :
  ∀i j: Fin a.size, a[i] = a[j] -> i = j := by
  intro i j eq
  apply Fin.val_inj.mp
  apply List.nodup_getElem_inj _ (as := a.toList) (i := i) (j := j)
  assumption
  assumption

instance [fα: Fintype α] {P: α -> Prop} [DecidablePred P] : Fintype (Subtype P) :=
  fα.map fun fα =>
  let all := (Array.ofFn fα.all).filter (fun x => P x)
  {
    card := all.size
    all := {
      toFun i := {
        val := all[i]
        property := by
          have : all[i] ∈ all := by exact Array.mem_of_getElem rfl
          rw [Array.mem_filter] at this
          simp at this
          exact this.right
      }
      inj' := by
        intro i j eq
        simp at eq
        have hi : all[i] ∈ all := by exact Array.mem_of_getElem rfl
        have hj : all[j] ∈ all := by exact Array.mem_of_getElem rfl
        rw [Array.mem_filter] at hi hj
        simp at hi hj
        obtain ⟨⟨i₀, eqi⟩, pi⟩ := hi
        obtain ⟨⟨j₀, eqj⟩, pj⟩ := hj
        rw [←eqi, ←eqj, fα.all.inj.eq_iff] at eq
        subst j₀
        apply Array.getElem_inj
        · unfold all
          simp; apply List.nodup_filter
          apply (List.nodup_ofFn _).mp
          exact fα.all.inj
        exact eqi.symm.trans eqj
    }
    complete x := by
      have ⟨i, hi⟩ := fα.complete x.val
      have : x.val ∈ all := by
        rw [Array.mem_filter]
        simp
        apply And.intro _ x.property
        exists i
        symm; assumption
      simp
      have ⟨j, hj, eq⟩ := Array.getElem_of_mem this
      exists ⟨j, hj⟩
      ext; symm; assumption
  }
