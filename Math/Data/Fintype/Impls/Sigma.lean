import Math.Data.Fintype.Choice

namespace Fintype

variable {α: ι -> Type*} [fι: Fintype ι] [fα: ∀i, Fintype (α i)]

private def fin_sum (f: Fin n -> ℕ) : ℕ :=
  Fin.foldr n (fun x acc => acc + f x) 0

private def fin_sum_succ (f: Fin (n + 1) -> ℕ) : fin_sum f = f 0 + fin_sum (f ∘ Fin.succ) := by
  rw [fin_sum, Fin.foldr_succ, Nat.add_comm]
  rfl

private def find_fin_sum (f: Fin n -> ℕ) (x: ℕ) : Option (Σx: Fin n, Fin (f x)) :=
  match n with
  | 0 => .none
  | _ + 1 =>
    if h:x < f 0 then
      .some ⟨0, _, h⟩
    else
      match find_fin_sum (f ∘ Fin.succ) (x - f 0) with
      | .none => .none
      | .some x => .some ⟨x.fst.succ, x.snd⟩

private def Nat.sub_lt_iff_lt_add {a b k: ℕ} (h: k ≤ a) : a - k < b ↔ a < b + k := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    cases a with
    | zero => contradiction
    | succ a =>
    rw [←Nat.add_assoc, Nat.succ_sub_succ, Nat.succ_lt_succ_iff]
    apply ih
    apply Nat.le_of_succ_le_succ
    assumption

private def find_fin_sum_spec (f: Fin n -> ℕ) (x: ℕ) (hx: x < fin_sum f) : ∃x₀ x₁, find_fin_sum f x = .some ⟨x₀, x₁⟩ ∧ x = fin_sum (n := x₀.val) (fun x => f (x.castLE (by omega))) + x₁.val := by
  induction n generalizing x with
  | zero => contradiction
  | succ n ih =>
    refine if h:x < f 0 then ?_ else ?_
    · exists 0
      exists ⟨x, h⟩
      apply And.intro
      unfold find_fin_sum
      simp [h]
      dsimp
      rw (occs := [1]) [Nat.add_comm, ←Nat.add_zero x]
      congr
    · unfold find_fin_sum
      simp [h]
      rw [Nat.not_lt] at h
      have ⟨x₀, x₁, g⟩ := ih (f ∘ Fin.succ)  (x - f 0) (by
        rwa [Nat.sub_lt_iff_lt_add, Nat.add_comm, ←fin_sum_succ]
        assumption)
      exists x₀.succ
      exists x₁
      simp at g
      rw [g.left]
      simp
      rw [fin_sum_succ, Nat.add_assoc]
      simp [←g.right]
      omega

private def find_fin_sum_isSome (f: Fin n -> ℕ) (x: ℕ) (hx: x < fin_sum f) : (find_fin_sum f x).isSome := by
  have ⟨_, _, g, _⟩ := find_fin_sum_spec f x hx
  rw [g]
  rfl

private def find_fin_sum_spec_lt (f: Fin n -> ℕ) (i₁: Fin n) (i₂: Fin (f i₁)) :
  (fin_sum fun x: Fin i₁.val => f (Fin.castLE (by omega) x)) + i₂.val < fin_sum f := by
  induction n with
  | zero => exact i₁.elim0
  | succ n ih =>
    cases i₁ using Fin.cases with
    | zero =>
      rw [fin_sum]
      simp
      apply Nat.lt_of_lt_of_le
      apply Fin.isLt
      rw [fin_sum_succ]
      omega
    | succ i₁ =>
      rw [fin_sum_succ, fin_sum_succ]
      simp [Nat.add_assoc]
      apply ih (f := f ∘ Fin.succ)

private def find_fin_sum_spec_inj (f: Fin n -> ℕ) (i₁ j₁: Fin n) (i₂: Fin (f i₁)) (j₂: Fin (f j₁)) :
  (fin_sum fun x: Fin i₁.val => f (Fin.castLE (by omega) x)) + i₂.val = (fin_sum fun x: Fin j₁.val => f (Fin.castLE (by omega) x)) + j₂.val ->
  i₁ = j₁ ∧ HEq i₂ j₂ := by
  induction n with
  | zero => exact i₁.elim0
  | succ n ih =>
    cases i₁ using Fin.cases with
    | zero =>
      cases j₁ using Fin.cases with
      | zero => simp [Fin.val_inj]
      | succ j₁ =>
        rw [fin_sum, fin_sum_succ]
        intro h
        have : i₂.val < f 0 := by apply Fin.isLt
        simp at h
        rw [h, ←Nat.not_le, Nat.add_assoc] at this
        have := this (Nat.le_add_right _ _)
        contradiction
        -- simp
        -- omega
    | succ i₁ =>
    cases j₁ using Fin.cases with
    | zero =>
      rw [fin_sum_succ]; rw (occs := [2]) [fin_sum]
      simp
      intro h
      have : j₂.val < f 0 := by apply Fin.isLt
      rw [←h, ←Nat.not_le, Nat.add_assoc] at this
      have := this (Nat.le_add_right _ _)
      contradiction
    | succ j₁ =>
      rw [fin_sum_succ, fin_sum_succ]
      simp [Nat.add_assoc]
      apply ih (f := f ∘ Fin.succ)

private def card_sigma' (rι: Repr cardι ι) := fin_sum fun x: Fin cardι => card (α (rι.decode x))

private def sigma_index_of (rι: Repr cardι ι) (x: Fin (card_sigma' rι (α := α))) : Σx: Fin cardι, Fin (card (α (rι.decode x))) :=
  (find_fin_sum _ x).get <| find_fin_sum_isSome _ _ (Fin.isLt _)

private def of_decode_heq
  {α β: Type u} {cardα cardβ} {rα: Repr cardα α} {rβ: Repr cardβ β}
  {x: Fin cardα} {y: Fin cardβ}
  (hty: α = β)
  (h: HEq (rα.decode x) (rβ.decode y))
  (hr: HEq rα rβ) :
  x.val = y.val := by
  cases hty;
  cases rα.card_eq rβ
  cases hr
  simp at h
  rw [rα.bij.Injective.eq_iff] at h
  congr

private def fin_heq_of_val_eq (h: n = m) {x: Fin n} {y: Fin m} (g: x.val = y.val) : HEq x y := by
  cases h
  simp; rwa [←Fin.val_inj]

instance {α: ι -> Type*} [fι: Fintype ι] [fα: ∀i, Fintype (α i)] : Fintype (Σi, α i) :=
  fι.toRepr.recOnSubsingleton fun rι : Repr (card ι) ι => {
    card_thunk := Thunk.mk fun _ => fin_sum (n := card ι) (fun i => card (α (rι.decode i)))
    toRepr :=
      Quotient.fin_ilift
        (n := card ι)
        (f := fun rα : ∀i: Fin (card ι), Repr (card (α (rι.decode i))) (α (rι.decode i)) =>
          Trunc.mk (α := Repr (fin_sum (fun i => card (α (rι.decode i)))) _) <| {
            decode x :=
              have x := (find_fin_sum (fun x: Fin (card ι) => card (α (rι.decode x))) x).get (find_fin_sum_isSome _ _ x.isLt)
              {
                fst := rι.decode x.fst
                snd := (rα _).decode x.snd
              }
            bij := by
              apply And.intro
              · intro ⟨x, xLt⟩ ⟨y, yLt⟩ h
                dsimp at h
                let x₀ := (find_fin_sum (fun x => card (α (rι.decode x))) x).get (find_fin_sum_isSome _ _ xLt)
                let y₀ := (find_fin_sum (fun x => card (α (rι.decode x))) y).get (find_fin_sum_isSome _ _ yLt)
                replace h : Sigma.mk (rι.decode x₀.1) ((rα _).decode x₀.2) = Sigma.mk (rι.decode y₀.1) ((rα _).decode y₀.2) := h
                suffices x₀ = y₀ by
                  clear h
                  have ⟨x₁, x₂, hx, gx⟩ := find_fin_sum_spec (fun x => card (α (rι.decode x))) x xLt
                  have ⟨y₁, y₂, hy, gy⟩ := find_fin_sum_spec (fun x => card (α (rι.decode x))) y yLt
                  simp
                  congr; rw [gx, gy]
                  have hx₀ : x₀ = ⟨x₁, x₂⟩ := by
                    apply Option.some.inj
                    rw [←hx]
                    simp [x₀]
                  have hy₀ : y₀ = ⟨y₁, y₂⟩ := by
                    apply Option.some.inj
                    rw [←hy]
                    simp [y₀]
                  rw [hx₀, hy₀] at this
                  cases this
                  rfl
                simp at h
                rw [rι.bij.Injective.eq_iff] at h
                obtain ⟨h₀, h₁⟩ := h
                have := of_decode_heq (by congr) h₁ (by congr)
                ext
                congr
                apply fin_heq_of_val_eq
                congr
                assumption
              · simp; intro ⟨i, ai⟩
                obtain ⟨i₀, rfl⟩ := rι.bij.Surjective i
                obtain ⟨i₁, rfl⟩ := (rα i₀).bij.Surjective ai
                let x₀ := fin_sum (n := i₀.val) (fun x => (fun x => card (α (rι.decode x))) (x.castLE (by omega))) + i₁.val
                have x₀Lt: x₀ < fin_sum fun x => card (α (rι.decode x)) := by
                  apply find_fin_sum_spec_lt (fun x => card (α (rι.decode x)))
                have ⟨x₁, x₂, hx, gx⟩ := find_fin_sum_spec (fun x => card (α (rι.decode x))) x₀ x₀Lt
                exists ⟨x₀, x₀Lt⟩
                dsimp
                let X := (find_fin_sum (fun x: Fin _ => card (α (rι.decode x))) x₀).get (find_fin_sum_isSome _ _ x₀Lt)
                show _ = Sigma.mk (rι.decode X.fst) ((rα _).decode X.snd)
                suffices Sigma.mk i₀ i₁ = X by rw [←this]
                simp [x₀] at gx
                have : X = ⟨x₁, x₂⟩ := by
                  simp [X]
                  apply Option.some.inj
                  simpa
                rw [this]; clear X this
                have ⟨_, _⟩ := find_fin_sum_spec_inj (fun x: Fin _ => card (α (rι.decode x))) i₀ x₁ i₁ x₂ gx
                congr

            encode := .none
          })
        (by intros; apply Subsingleton.allEq)
        (fun i => (fα (rι.decode i)).toRepr)
  }

end Fintype
