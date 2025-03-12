import Math.Data.Fintype.Impls.Quot

namespace Pi

variable [DecidableEq α]

private def allOn (as: List α) (β: α -> Type _) (bs: ∀x, List (β x)) : List (∀x ∈ as, β x) :=
  match as with
  | [] => [nofun]
  | a::as => by
    apply (bs a).flatMap
    intro b
    apply (allOn as β bs).map
    intro f
    intro x h
    if g:a = x then
      exact Eq.ndrec b g
    else
      apply f
      cases h
      contradiction
      assumption

private def allOn_nodup
  (as: List α) (β: α -> Type _) (bs: ∀x, List (β x))
  (as_nodup: as.Nodup)
  (bs_nodup: ∀x, (bs x).Nodup):
  (allOn as β bs).Nodup := by
  induction as_nodup with
  | nil => apply List.Nodup.singleton
  | cons not_mem_head as_nodup ih =>
    rename_i a as
    replace not_mem_head : a ∉ as := by
      intro h
      apply not_mem_head
      assumption
      rfl
    apply List.nodup_flatMap
    apply bs_nodup
    intro b
    apply List.nodup_map
    intro x y eq
    dsimp at eq
    ext a₀ h
    have := congrFun (congrFun eq a₀) (List.Mem.tail _ h)
    rw [dif_neg, dif_neg] at this
    assumption
    intro eq
    clear this
    rw [eq] at not_mem_head
    contradiction
    intro eq
    clear this
    rw [eq] at not_mem_head
    contradiction
    assumption
    intro x y hx hy z gx gy
    simp only [List.mem_map] at gx gy
    obtain ⟨f₀, f₀_mem, f₀_eq_z⟩ := gx
    obtain ⟨f₁, f₁_mem, f₁_eq_z⟩ := gy
    have feq := f₀_eq_z.trans f₁_eq_z.symm
    clear f₀_mem f₁_mem f₀_eq_z f₁_eq_z
    have := congrFun (congrFun feq a) (List.Mem.head _)
    rw [dif_pos rfl, dif_pos rfl] at this
    assumption

private def allOn_complete
  (as: List α) (β: α -> Type _) (bs: ∀x, List (β x))
  (bs_complete: ∀x, ∀b, b ∈ bs x):
  ∀f, f ∈ allOn as β bs := by
  intro f
  induction as with
  | nil =>
    apply List.mem_singleton.mpr
    ext; contradiction
  | cons a as ih =>
    apply List.mem_flatMap.mpr
    refine ⟨?_, ?_, ?_⟩
    apply f
    apply List.Mem.head
    apply bs_complete
    apply List.mem_map.mpr
    refine ⟨?_, ?_, ?_⟩
    exact (fun x h => f x (List.Mem.tail _ h))
    apply ih
    ext a₀ h
    split
    subst a
    rfl
    rfl

end Pi

instance Fintype.instPi {α: Type*} {β: α -> Type*} [DecidableEq α] [ha: Fintype α] [hb: ∀x, Fintype (β x)] : Fintype (∀x, β x) := by
  apply ha.recOnSubsingleton
  intro as as_nodup as_complete
  refine Quotient.fin_ilift ?_ ?_ (fun a: α => Fintype.equiv_trunc_subtype (hb a))
  · intro hb
    refine Fintype.ofList ?_ ?_ ?_
    apply (Pi.allOn as β (fun x => hb x)).map
    intro f x
    apply f
    apply as_complete
    apply List.nodup_map
    intro x y eq
    ext
    apply congrFun eq
    apply Pi.allOn_nodup
    assumption
    intro x
    apply (hb x).property.left
    intro f
    apply List.mem_map.mpr
    refine ⟨?_, ?_⟩
    intro x _
    exact f x
    apply And.intro _ rfl
    apply Pi.allOn_complete
    intro x
    apply (hb x).property.right
  · intro a b eq
    dsimp
    apply Subsingleton.allEq

instance {α β: Type*} [DecidableEq α] [Fintype α] [Fintype β] : Fintype (α -> β) :=
  inferInstance
