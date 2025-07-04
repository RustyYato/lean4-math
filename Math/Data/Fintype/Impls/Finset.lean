import Math.Data.Finset.Basic
import Math.Data.Fintype.Defs
import Math.Data.Set.Defs

instance (f: Finset α) : Fintype f :=
  {
    card_thunk := f.val.length
    toRepr := f.recOnSubsingleton (motive := fun f => Trunc (Fintype.Repr f.val.length _)) fun l h =>
      Trunc.mk (α := Fintype.Repr l.length _) {
        encode := Thunk.mk fun _ => .none
        decode := {
          toFun x := {
            val := l[x]'x.isLt
            property := List.getElem_mem x.isLt
          }
          inj' := by
            intro x y g
            dsimp at g
            rw [←Fin.val_inj]
            exact l.nodup_getElem_inj h (Subtype.mk.inj g)
          surj' := by
            intro ⟨x, hx⟩
            have ⟨i, h, _⟩ := List.getElem_of_mem hx
            exists ⟨i, h⟩
            congr; symm; assumption
        }
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
    apply s.decode.inj⟩) <| by
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
  have ⟨i, h⟩ := r.decode.surj x
  exists i; symm; assumption

instance [Fintype α] [DecidableEq α] : SetComplement (Finset α) where
  scompl s := Finset.univ α \ s

def Finset.mem_compl [Fintype α] [DecidableEq α] {s: Finset α} : ∀{x}, x ∈ sᶜ ↔ x ∉ s := by
  intro x
  show x ∈ Finset.univ α \ s ↔ _
  simp [Finset.mem_sdiff, Finset.mem_univ]

def Finset.compl_compl [Fintype α] [DecidableEq α] (s: Finset α) : sᶜᶜ = s := by
  ext; simp [mem_compl]

private def mk_multiset (f: Fintype.Repr c α) (x: Nat) (h: c' ≤ c) : Multiset α :=
  Multiset.mk (Fin.foldl c' (fun acc i =>
    if x.testBit i.val then
      acc.push (f.decode (i.castLE h))
    else
      acc
    ) #[]).toList

private def mk_multiset_zero (f: Fintype.Repr c α) (x: Nat) : mk_multiset f x (Nat.zero_le _) = ∅ := rfl
private def mk_multiset_succ (f: Fintype.Repr c α) (x: Nat) (h: c' + 1 ≤ c) :
  mk_multiset f x h = (
    let prev := mk_multiset (c' := c') f x (by
      apply Nat.le_trans _ h
      apply Nat.le_succ)
    if x.testBit c' then
      (f.decode ⟨c', Nat.lt_of_succ_le h⟩)::ₘprev
    else
      prev
  ) := by
  dsimp
  induction c' with
  | zero =>
    unfold mk_multiset
    dsimp
    rw [Fin.foldl_succ, Fin.foldl_zero, Fin.foldl_zero]
    dsimp
    split
    rfl
    rfl
  | succ c' ih =>
    rw [mk_multiset, Fin.foldl_succ_last]
    dsimp
    split
    · rw [Array.push_toList, ←Multiset.mk_append, Multiset.append_comm, Multiset.mk_append,
        List.singleton_append, ←Multiset.mk_cons]
      rfl
    · rfl
private def mk_multiset_succ' (f: Fintype.Repr c α) (x: Nat) (h: c' + 1 ≤ c) :
  mk_multiset f x h = (
    (if x.testBit c' then
      {f.decode ⟨c', Nat.lt_of_succ_le h⟩}
    else
      (∅: Multiset α)) ++ mk_multiset (c' := c') f x (by
      apply Nat.le_trans _ h
      apply Nat.le_succ)
  ) := by
  rw [mk_multiset_succ]
  dsimp
  split
  rfl
  rfl

private def mem_mk_multiset {f: Fintype.Repr c α} {x: Nat} {h: c' ≤ c} : ∀{a: α}, a ∈ mk_multiset f x h ↔ ∃i: Fin c', a = f.decode (i.castLE h) ∧ x.testBit i.val := by
  intro a
  induction c' with
  | zero =>
    rw [mk_multiset_zero]
    simp [show a ∉ (∅: Multiset α) from nofun]
    nofun
  | succ c' ih =>
    rw [mk_multiset_succ]
    split
    · simp; apply Iff.intro
      · intro g
        rcases g with g | g
        exists Fin.last _
        have ⟨i, hi⟩ := ih.mp g
        exists i.castSucc
      · intro ⟨i, _, _⟩
        cases i using Fin.lastCases
        left; assumption
        right; apply ih.mpr
        rename_i i _ _
        exists i
    · simp
      apply Iff.intro
      · intro g
        have ⟨i, hi⟩ := ih.mp g
        exists i.castSucc
      · intro ⟨i, _, _⟩
        cases i using Fin.lastCases
        contradiction
        apply ih.mpr
        rename_i i _ _
        exists i

private def mk_multiset_nodup (f: Fintype.Repr c α) (x: Nat) (h: c' ≤ c) : (mk_multiset f x h).Nodup := by
  induction c' with
  | zero => apply List.Pairwise.nil
  | succ c ih =>
    rw [mk_multiset_succ]
    dsimp
    split
    apply Multiset.nodup_cons
    · rw [mem_mk_multiset]
      intro ⟨⟨j, jlt⟩, hj, _⟩
      have := f.decode.inj hj
      dsimp at this
      cases this
      exact Nat.lt_irrefl _ jlt
    · apply ih
    · apply ih

private def mk_finset (f: Fintype.Repr c α) (x: Fin (2 ^ c')) (h: c' ≤ c) : Finset α where
  val := (mk_multiset f x h)
  property := by apply mk_multiset_nodup

private def mk_finset_zero (f: Fintype.Repr c α) (h: c' ≤ c) : mk_finset f 0 h = ∅ := by
  unfold mk_finset; congr
  induction c' with
  | zero => rw [mk_multiset_zero]
  | succ c' ih =>
    rw [mk_multiset_succ, if_neg]
    apply ih
    apply Bool.eq_false_iff.mp
    apply Nat.zero_testBit

private def nat_pow_lt_pow_iff_right (i j: Nat) : i < j -> 2 ^ i < 2 ^ j := by
  intro h
  induction i generalizing j with
  | zero =>
    simp
    omega
  | succ i ih =>
    cases j
    contradiction
    rw [Nat.pow_succ, Nat.pow_succ]
    rw [Nat.mul_two, Nat.mul_two]
    apply Nat.add_lt_add
    all_goals
      apply ih
      omega

private def Fin.twoPow (i: Fin n) : Fin (2 ^ n) where
  val := 2 ^ i.val
  isLt := by
    apply nat_pow_lt_pow_iff_right
    exact i.isLt

private def mk_multiset_or (f: Fintype.Repr c α) (i: Fin (2 ^ c')) (j: Fin c') (h: c' ≤ c) (g: ¬i.val.testBit j.val) :
  mk_multiset f (i ||| j.twoPow) h = f.decode (j.castLE h)::ₘmk_multiset f i h := by
  -- show a ∈ mk_multiset _ _ _ ↔ a ∈ _::ₘmk_multiset _ _ _
  obtain ⟨i, iLt⟩ := i
  dsimp [Fin.twoPow] at *
  clear iLt
  induction c' generalizing i with
  | zero => exact j.elim0
  | succ c' ih =>
    rw [mk_multiset_succ]
    cases j using Fin.lastCases with
    | last =>
      simp
      congr 1
      apply Multiset.ext_nodup
      apply mk_multiset_nodup
      apply mk_multiset_nodup
      intro a
      rw [mem_mk_multiset, mem_mk_multiset]
      simp; conv => {
        lhs; arg 1; intro k; rhs
        rw [Nat.testBit_two_pow, decide_eq_true_iff, or_iff_left (by
          intro g
          have := k.isLt
          rw [←g] at this
          exact Nat.lt_irrefl _ this)]
      }
      dsimp at g
      apply Iff.intro
      · intro ⟨k, _, _⟩
        exists k.castSucc
      · intro ⟨k, _, _⟩
        cases k using Fin.lastCases
        contradiction
        rename_i k _ _
        exists k
    | cast j =>
      simp [Nat.testBit_two_pow]
      rw [mk_multiset_succ']
      symm
      split <;> (symm; rename_i htest)
      · rw [if_pos (.inl htest)]
        rw [Multiset.singleton_append, Multiset.cons_comm]
        congr
        apply ih
        assumption
      · rw [if_neg]
        apply ih
        assumption
        intro g
        cases g
        contradiction
        have := j.isLt
        rename_i h
        rw [h] at this
        exact Nat.lt_irrefl _ this

instance Fintype.instFinset [f: Fintype α] : Fintype (Finset α) where
  card_thunk := Thunk.mk fun _ => 2 ^ Fintype.card α
  toRepr :=
    let c := Fintype.card α
    f.toRepr.map (β := Fintype.Repr (2 ^ c) _) fun f => {
      decode := {
        toFun x := mk_finset f x (Nat.le_refl _)
        inj' := by
          intro x y h
          dsimp at h
          have : ∀{a: α}, a ∈ mk_finset f x (Nat.le_refl _) ↔ a ∈ mk_finset f y (Nat.le_refl _) := by rw [h]
          replace this : ∀{a: α}, a ∈ mk_multiset _ _ (Nat.le_refl _) ↔ a ∈ mk_multiset _ _ (Nat.le_refl _) := this
          simp [mem_mk_multiset] at this
          have : ∀i, x.val.testBit i = y.val.testBit i := by
            intro i
            by_cases hi:i < c
            · let a := f.decode ⟨i, hi⟩
              by_cases h:x.val.testBit i = true
              have ⟨j, hj, testbit⟩ := (@this a).mp ⟨⟨i, hi⟩, rfl, h⟩
              cases f.decode.inj hj
              rw [h, testbit]
              have := (Iff.not_iff_not (@this a)).mp (by
                intro ⟨j, hj, tb⟩
                cases f.decode.inj hj
                contradiction)
              simp at this
              rw [this ⟨i, hi⟩ rfl]
              apply Bool.eq_false_iff.mpr
              assumption
            · rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt, Nat.div_eq_of_lt]
              apply Nat.lt_of_lt_of_le y.isLt
              refine Nat.pow_le_pow_right ?_ ?_ <;> omega
              apply Nat.lt_of_lt_of_le x.isLt
              refine Nat.pow_le_pow_right ?_ ?_ <;> omega
          ext; apply Nat.eq_of_testBit_eq
          assumption
        surj' := by
          intro x
          dsimp
          obtain ⟨x, xNodup⟩ := x
          induction x with
          | nil =>
            exists 0
            rw [mk_finset_zero]
            rfl
          | cons x xs ih =>
            replace ih := ih xNodup.tail
            obtain ⟨is, his⟩ := ih
            have ⟨i, hi⟩ := f.decode.surj x
            exists is ||| i.twoPow
            unfold mk_finset
            congr; simp
            by_cases hi':is.val.testBit i.val
            · exfalso
              cases Subtype.mk.inj his
              clear his
              have := xNodup.head
              rw [mem_mk_multiset, not_exists] at this
              exact this i ⟨hi, hi'⟩
            · rw [mk_multiset_or]
              congr
              exact Subtype.mk.inj his
              assumption
      }
      encode := Thunk.mk fun _ => .none
    }
