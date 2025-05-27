import Math.Data.Nat.Factorial
import Math.Data.Fintype.Defs
import Math.Data.Nat.Basic

namespace Fintype

private def mod_m (i: Fin (npr (m + 1) (n + 1))) : Fin (m + 1) := Fin.ofNat' (m + 1) i

private def div_m (i: Fin (npr (m + 1) (n + 1))) : Fin (npr m n) where
  val := i.val / (m + 1)
  isLt := by
      have hi := i.isLt
      simp [npr] at *
      rwa [Nat.div_lt_iff_lt_mul, Nat.mul_comm, ←Nat.mul_div_assoc, ←fact_succ]
      apply fact_dvd_of_le
      apply Nat.sub_le
      apply Nat.zero_lt_succ

private def val_mod_m (i: Fin (npr (m + 1) (n + 1))) : (mod_m i).val = i.val % (m + 1) := rfl
private def val_div_m (i: Fin (npr (m + 1) (n + 1))) : (div_m i).val = i.val / (m + 1) := rfl

private def decode (h: n ≤ m) (i: Fin (npr m n)) : Fin n ↪ Fin m :=
  match n with
  | 0 => Embedding.empty
  | _ + 1 =>
  match m with
  | _ + 1 =>
    have f := decode (Nat.le_of_succ_le_succ h) (div_m i)
    Equiv.congrEmbed (Equiv.fin_equiv_option _).symm (Equiv.fin_erase (mod_m i)).symm f.congrOption

private def decode_inj (h: n ≤ m) : Function.Injective (decode h) := by
  intro x y g
  induction m generalizing n with
  | zero =>
    clear g
    obtain ⟨x, xLt⟩ := x
    obtain ⟨y, yLt⟩ := y
    congr
    simp [npr] at xLt yLt
    rw [xLt, yLt]
  | succ m ih =>
    congr 1; congr 1
    cases n with
    | zero =>
      have xLt := x.isLt
      have yLt := y.isLt
      simp [npr, Nat.div_self (n := (m + 1) * m !) (by
        rw [←fact_succ]
        apply fact_pos)] at xLt yLt
      rw [←Fin.val_inj, xLt, yLt]
    | succ n =>
      let x₀ := mod_m x
      let x₁ := div_m x
      let y₀ := mod_m y
      let y₁ := div_m y
      rw [←Fin.val_inj]
      rw [←Nat.div_add_mod x (m + 1), ←Nat.div_add_mod y (m + 1)]
      simp [←val_mod_m, ←val_div_m]
      suffices mod_m x = mod_m y by
        congr 1; congr 2
        apply ih (Nat.le_of_succ_le_succ h)
        · unfold decode at g
          simp only [Equiv.symm_symm, this] at g
          replace g := (Equiv.congrEmbed _ _).inj g
          exact Embedding.congrOption.inj g
        · rw [this]
      have := Embedding.congr g (Fin.last _)
      simpa [Fintype.decode, Equiv.symm_apply_fin_erase_none] using this

private def encode (f: Fin n ↪ Fin m) : Fin (npr m n) :=
  have := Fin.le_of_embed f
  match n with
  | 0 =>
    Fin.mk 0 (by simp [npr]; apply fact_pos)
  | n + 1 =>
  match m with
  | m + 1 =>
    let i₀ := f (Fin.last _)
    let f' := Embedding.of_option_embed_option (Equiv.congrEmbed (Equiv.fin_equiv_option _) (Equiv.fin_erase i₀) f)
    have i₁ := encode f'
    {
      val := i₁.val * (m + 1) + i₀
      isLt := by
        rw [npr_succ_succ, Nat.mul_comm]
        apply Nat.lt_of_succ_le
        rw [←Nat.add_succ]
        rw (occs := [2]) [←Nat.sub_add_cancel (n := npr m n) (m := 1)]
        rw [Nat.mul_succ]
        apply Nat.add_le_add
        apply Nat.mul_le_mul_left
        apply Nat.le_pred_of_lt
        simp
        simp; rw [←Nat.lt_succ]
        simp
        rw [Nat.succ_le]
        apply npr_pos
    }

private def encode_inj : Function.Injective (encode (n := n) (m := m)) := by
  intro f g h
  induction n generalizing m with
  | zero => apply Subsingleton.allEq
  | succ n ih =>
    cases m with
    | zero => exact (f 0).elim0
    | succ m =>
      unfold encode at h
      simp at h
      rw [Nat.mul_comm _ (m + 1), Nat.mul_comm _ (m + 1)] at h
      have ⟨h₀, h₁⟩ := Nat.of_mul_add_lt (Fin.isLt _) (Fin.isLt _) h
      clear h
      rw [Fin.val_inj] at h₀
      replace h₀ := ih h₀
      replace h₀ := Embedding.of_option_embed_option_inj _ _ (by simp) (by simp) h₀
      replace h₀ := Embedding.congr h₀
      simp at h₀
      rw [Fin.val_inj] at h₁
      replace h₀ (i: Fin n) := h₀ i
      simp [h₁, (Equiv.fin_erase _).inj.eq_iff] at h₀
      ext i
      cases i using Fin.lastCases
      rw [h₁ ]
      rw [h₀]

private def encode_decode (h: n ≤ m) (i: Fin (npr m n)) : encode (decode h i) = i := by
  induction n generalizing m with
  | zero =>
    have : Subsingleton (Fin (npr m 0)) := by
      rw [npr_zero_right]
      infer_instance
    apply Subsingleton.allEq
  | succ n ih =>
  cases m with
  | zero => contradiction
  | succ m =>
    ext; rw [←Nat.div_add_mod i.val (m + 1)]
    unfold decode encode
    simp
    rw [Nat.mul_comm]
    congr 2
    simp [←Embedding.trans_assoc, (Equiv.fin_equiv_option n).symm_trans]
    rw [Embedding.trans_assoc, Equiv.toEmbedding_trans]
    rw [Equiv.symm_apply_fin_erase_none, Equiv.symm_trans]
    simp
    rw [ih]
    rfl

private def decode_encode (f: Fin n ↪ Fin m)  : decode (Fin.le_of_embed f) (encode f) = f := by
  apply encode_inj
  rw [encode_decode]

instance [DecidableEq α] [fα: Fintype α] [fβ: Fintype β] : Fintype (α ↪ β) :=
  if h:card α ≤ card β then
    {
    card_thunk := Thunk.mk fun _ => npr (card β) (card α)
    toRepr :=
        fα.toRepr.bind fun rα: Repr (card α) _ =>
        fβ.toRepr.map (β := Repr (npr _ _) _) fun rβ: Repr (card β) _ =>
        {
          encode := Thunk.mk fun _ => .none
          decode x :=
            let f := Fintype.decode h x
            rα.toEquiv.symm.toEmbedding.trans (f.trans rβ.toEmbed)
          bij := by
            apply And.intro
            · intro x y g
              dsimp at g
              replace g := Embedding.congr g
              simp [rβ.toEmbed.inj.eq_iff] at g
              replace g (i: Fin (card α)) : Fintype.decode h x i = Fintype.decode h y i := by
                have := g (rα.toEquiv i)
                simpa using this
              apply decode_inj h
              apply Embedding.ext
              assumption
            · intro f
              dsimp
              let f' := rα.toEquiv.toEmbedding.trans f
              have (i: Fin (card α)) : ∃j, f' i = rβ.decode j := rβ.bij.Surjective _
              replace this := axiomOfChoice' this
              obtain ⟨g, hg⟩ := this
              let g' : Fin (card α) ↪ Fin (card β) := {
                toFun := g
                inj' := by
                  intro x y h
                  have : rβ.decode (g x) = rβ.decode (g y) := by rw [h]
                  rw [←hg, ←hg] at this
                  exact f'.inj this
              }
              exists (encode g')
              rw [decode_encode]
              ext i
              simp [g', Repr.toEmbed, ←hg, f']
        }
    }
  else
    have : IsEmpty (α ↪ β) := { elim f := h (Fintype.card_le_of_embed f) }
    inferInstanceAs (Fintype (α ↪ β))

end Fintype
