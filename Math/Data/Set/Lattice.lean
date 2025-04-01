import Math.Order.Lattice.Complete
import Math.Data.Set.Order.Basic

def Set.Induced (r: α -> α -> Prop) (s: Set α) :=
  fun x y: s => r x y

instance : Max (Set α) where
  max a b := a ∪ b
instance : Min (Set α) where
  min a b := a ∩ b

instance : IsLattice (Set α) where
  le_sup_left := Set.sub_union_left
  le_sup_right := Set.sub_union_right
  sup_le := by
    intro a b k ak bk
    intro x mem
    cases Set.mem_union.mp mem
    apply ak
    assumption
    apply bk
    assumption
  inf_le_left := Set.inter_sub_left
  inf_le_right := Set.inter_sub_right
  le_inf := by
    intro a b k ka kb x mem
    apply Set.mem_inter.mpr
    apply And.intro
    apply ka; assumption
    apply kb; assumption

instance : IsCompleteLattice (Set α) where
  bot_le := Set.empty_sub
  le_top := Set.sub_univ
  le_sSup := by
    intro s x
    apply Set.sub_sUnion
  sSup_le := by
    intro k s h x mem
    have ⟨s', s'_in_s, x_in_s'⟩ := Set.mem_sUnion.mp mem
    apply h s' s'_in_s
    assumption
  sInf_le := by
    intro s x mem y hy
    exact Set.mem_sInter.mp hy x mem
  le_sInf := by
    intro k s h x hx
    apply Set.mem_sInter.mpr
    intro s' hs'
    apply h
    assumption
    assumption
