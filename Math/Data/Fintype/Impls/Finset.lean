import Math.Data.Finset.Basic
import Math.Data.Fintype.Defs
import Math.Data.Set.Defs

instance (f: Finset α) : Fintype f :=
  {
    card_thunk := f.val.length
    toRepr := f.recOnSubsingleton (motive := fun f => Trunc (Fintype.Repr f.val.length _)) fun l h =>
      Trunc.mk (α := Fintype.Repr l.length _) {
        encode := .none
        decode x := {
          val := l[x]'x.isLt
          property := List.getElem_mem x.isLt
        }
        bij := by
          apply And.intro
          · intro x y g
            dsimp at g
            rw [←Fin.val_inj]
            exact l.nodup_getElem_inj h (Subtype.mk.inj g)
          · intro ⟨x, hx⟩
            have ⟨i, h, _⟩ := List.getElem_of_mem hx
            exists ⟨i, h⟩
            congr; symm; assumption
      }
  }

def List.swap (l: List α) (i j: ℕ) (hi: i < l.length) (hj: j < l.length) :=
  (l.set i (l[j])).set j l[i]

@[simp]
def List.length_swap (l: List α) (i j: ℕ) (hi: i < l.length) (hj: j < l.length) : (l.swap i j hi hj).length = l.length := by
  simp [swap]

@[simp]
def List.swap_self (l: List α) (i: ℕ) (hi: i < l.length) : l.swap i i hi hi = l := by
  unfold swap
  apply List.ext_getElem
  simp
  intro x hx hy
  simp

def List.perm_swap (l: List α) (i j: ℕ) (hi: i < l.length) (hj: j < l.length) : l.Perm (l.swap i j hi hj) := by
  have := Array.swap_perm (xs := l.toArray) (i := i) (j := j) hi hj
  have := Array.perm_iff_toList_perm.mp this
  simp at this
  exact this.symm

@[simp]
def List.swap_succ (a: α) (as: List α) (i j: ℕ) (hi: i + 1 < as.length + 1) (hj: j + 1 < as.length + 1) :
  (a::as).swap (i + 1) (j + 1) hi hj = a::as.swap i j (by omega) (by omega) := by
  simp [swap]

def List.ofFn_eqv_swap_zero {f: Fin (n + 1) -> α} (y: Fin (n + 1)) {hx hy} : ofFn (f ∘ ⇑(Equiv.swap 0 y)) = (ofFn f).swap ↑0 ↑y hx hy := by
  cases y using Fin.cases with
  | zero => simp
  | succ y =>
    simp
    rw [Equiv.swap_spec]
    simp [swap]
    conv => {
      lhs; arg 1; intro i
      rw [Equiv.swap_comm,
        show Equiv.swap y.succ 0 i.succ = if y = i then 0 else i.succ by
          rw [Equiv.swap, Equiv.apply_set]
          split
          rw [if_pos ]
          symm; rwa [Fin.succ_inj] at *
          rw [if_neg, if_neg]
          rfl
          rintro rfl
          contradiction
          intro h
          rw [←Fin.val_inj] at h
          contradiction]
    }
    induction n with
    | zero => rfl
    | succ n ih =>
      cases y using Fin.cases with
      | zero =>
        simp
        conv => {
          lhs; arg 1; intro i
          rw [if_neg (by apply (Fin.succ_ne_zero _).symm)]
        }
      | succ y =>
        simp
        apply And.intro
        rw [if_neg (Fin.succ_ne_zero _)]
        let f' (j: Fin (n + 1)) : α :=
          if j = 0 then f 0 else f j.succ
        have (i: Fin n) : f (if y = i then 0 else i.succ.succ) = f' (if y = i then 0 else i.succ) := by
          split
          simp [f']
          simp [f']
          rw [if_neg (Fin.succ_ne_zero _)]
        simp [this]
        rw [ih]
        simp [f']
        conv => {
          lhs; arg 1; arg 1; intro i; rw [if_neg (Fin.succ_ne_zero _)]
        }
        simp
        simp

def List.ofFn_eqv_swap (f: Fin n -> α) : List.ofFn (f ∘ Equiv.swap x y) = (List.ofFn f).swap x.val y.val (by simp) (by simp) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases x using Fin.cases with
    | zero => apply List.ofFn_eqv_swap_zero
    | succ x =>
      cases y using Fin.cases with
      | zero =>
        rw [Equiv.swap_comm]
        rw [List.ofFn_eqv_swap_zero]
        simp [swap]
        simp
        simp
      | succ y =>
        simp
        rw [Equiv.swap, Equiv.apply_set]
        simp [if_neg (Fin.succ_ne_zero _).symm]
        rw [←ih]
        simp
        congr; ext i
        congr; simp [Equiv.swap, Equiv.apply_set]
        split
        rfl
        split
        rfl
        rfl

def List.ofFn_perm_of_eqv_swap (f: Fin n -> α) : (List.ofFn f).Perm (List.ofFn (f ∘ Equiv.swap x y)) := by
  rw [List.ofFn_eqv_swap]
  apply List.perm_swap

def List.ofFn_perm_of_eqv (f: Fin n -> α) (g: Fin m -> α) (eqv: Fin n ≃ Fin m) (h: ∀i, f i = g (eqv i))  : (List.ofFn f).Perm (List.ofFn g) := by
  rw [show f = (g ∘ eqv) from funext h]
  clear h  f
  cases Fin.eq_of_equiv eqv
  induction n with
  | zero => rw [Subsingleton.allEq (g ∘ eqv) g]
  | succ n ih =>
    apply (ofFn_perm_of_eqv_swap (g ∘ eqv) (x := 0) (y := eqv.symm 0)).trans
    simp [Equiv.swap_spec]
    let eqv₀ : Fin (n + 1) ≃ Fin (n + 1) := (Equiv.swap 0 (eqv.symm 0)).trans eqv
    have h₀ : eqv₀ 0 = 0 := by simp [eqv₀, Equiv.swap_spec]
    have h₁ : eqv₀.symm 0 = 0 := by
      symm; apply Equiv.eq_symm_of_coe_eq
      assumption
    let eqv' : Fin n ≃ Fin n := {
      toFun x := Fin.pred (eqv₀ x.succ) <| by
        intro h; rw [←h₀, eqv₀.inj.eq_iff] at h
        exact Fin.succ_ne_zero _ h
      invFun x := Fin.pred (eqv₀.symm x.succ) <| by
        intro h; rw [←h₁, eqv₀.symm.inj.eq_iff] at h
        exact Fin.succ_ne_zero _ h
      leftInv x := by simp
      rightInv x := by simp
    }
    have : eqv₀ ∘ Fin.succ = Fin.succ ∘ eqv' := by ext i; simp [eqv']
    show (ofFn (g ∘ (eqv₀ ∘ Fin.succ))).Perm (ofFn (g ∘ Fin.succ))
    rw [this]
    show (ofFn ((g ∘ Fin.succ) ∘ eqv')).Perm (ofFn (g ∘ Fin.succ))
    apply (ih (g ∘ Fin.succ) eqv')

def Finset.univ (α: Type*) [f: Fintype α] : Finset α :=
  f.toRepr.lift (fun s => ⟨Multiset.mk (List.ofFn s.decode), by
    apply (List.nodup_ofFn _).mp
    apply s.bij.Injective⟩) <| by
    intro a b
    simp
    congr 1
    classical
    apply Quotient.sound
    refine List.ofFn_perm_of_eqv _ _ ?_ ?_
    apply a.toEquiv.trans
    apply b.toEquiv.symm
    intro i
    simp
    rw [←Fintype.Repr.apply_toEquiv, ←Fintype.Repr.apply_toEquiv]
    simp

def Finset.mem_univ (α: Type*) [f: Fintype α] : ∀x, x ∈ univ α := by
  induction f using Fintype.ind with | _ r =>
  intro x
  apply List.mem_ofFn.mpr
  have ⟨i, h⟩ := r.bij.Surjective x
  exists i; symm; assumption

instance [Fintype α] [DecidableEq α] : SetComplement (Finset α) where
  scompl s := Finset.univ α \ s

def Finset.mem_compl [Fintype α] [DecidableEq α] {s: Finset α} : ∀{x}, x ∈ sᶜ ↔ x ∉ s := by
  intro x
  show x ∈ Finset.univ α \ s ↔ _
  simp [Finset.mem_sdiff, Finset.mem_univ]

def Finset.compl_compl [Fintype α] [DecidableEq α] (s: Finset α) : sᶜᶜ = s := by
  ext; simp [mem_compl]
