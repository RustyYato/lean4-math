import Math.Data.Rat.Order

def CauchySeq.Eventually (P: Nat -> Prop) : Prop := ∃k, ∀n, k ≤ n -> P n
def CauchySeq.Eventually₂ (P: Nat -> Nat -> Prop) : Prop := ∃k, ∀n m, k ≤ n -> k ≤ m -> P n m

def CauchySeq.Eventually.to₂ : Eventually a -> Eventually₂ fun i _ => a i := by
  intro ⟨i,hi⟩
  exists i
  intro n _ hn _
  apply hi; assumption

def CauchySeq.Eventually.merge : Eventually a -> Eventually b -> Eventually fun i => a i ∧ b i := by
  intro ⟨i,hi⟩ ⟨j,hj⟩
  exists max i j
  intro n hn
  apply And.intro
  apply hi
  apply le_trans _ hn
  apply le_max_left
  apply hj
  apply le_trans _ hn
  apply le_max_right

def CauchySeq.Eventually₂.merge : Eventually₂ a -> Eventually₂ b -> Eventually₂ fun i j => a i j ∧ b i j := by
  intro ⟨i,hi⟩ ⟨j,hj⟩
  exists max i j
  intro m n hm hn
  apply And.intro
  apply hi
  apply le_trans _ hm
  apply le_max_left
  apply le_trans _ hn
  apply le_max_left
  apply hj
  apply le_trans _ hm
  apply le_max_right
  apply le_trans _ hn
  apply le_max_right

def is_cauchy_equiv (a b: Nat -> ℚ) : Prop :=
  ∀ε: ℚ, 0 < ε -> CauchySeq.Eventually₂ fun n m => ‖a n - b m‖ < ε

structure CauchySeq where
  seq: Nat -> ℚ
  is_cacuhy: is_cauchy_equiv seq seq

instance : CoeFun CauchySeq (fun _ => Nat -> ℚ) := ⟨CauchySeq.seq⟩

def CauchySeq.Equiv (a b: CauchySeq) := is_cauchy_equiv a.seq b.seq

def Rat.half_pos {ε: ℚ} : 0 < ε -> 0 < ε /? 2 := (Rat.div_pos · (by decide))

@[refl]
def CauchySeq.Equiv.refl (a: CauchySeq) : Equiv a a := a.is_cacuhy
@[symm]
def CauchySeq.Equiv.symm {a b: CauchySeq} : Equiv a b -> Equiv b a := by
  intro h ε ε_pos
  replace ⟨δ, h⟩ := h ε ε_pos
  exists δ
  intro n m _ _
  rw [Rat.abs_sub_comm]
  apply h <;> assumption
def CauchySeq.Equiv.trans {a b c: CauchySeq} : Equiv a b -> Equiv b c -> Equiv a c := by
  intro ab bc ε ε_pos
  replace ab := ab _ (Rat.half_pos ε_pos)
  replace bc := bc _ (Rat.half_pos (Rat.half_pos ε_pos))
  replace bspec := b.is_cacuhy _ (Rat.half_pos (Rat.half_pos ε_pos))
  have ⟨δ, h⟩ := ab.merge (bc.merge bspec)
  exists δ
  intro n m δ_le_n δ_le_m
  replace ⟨ab, bc, bspec⟩ := h n m δ_le_n δ_le_m
  have := Rat.add_lt_add ab (Rat.add_lt_add bc bspec)
  rw [←Rat.mul_two, Rat.mul_div_cancel, ←Rat.mul_two, Rat.mul_div_cancel,
    Rat.abs_sub_comm (b n) (b m)] at this
  apply lt_of_le_of_lt _ this
  apply flip le_trans
  apply Rat.add_le_add
  rfl
  apply Rat.abs_add_le_add_abs
  apply flip le_trans
  apply Rat.abs_add_le_add_abs
  iterate 4 rw [Rat.sub_eq_add_neg]
  have : a n + -b m + (b n + -c m + (b m + -b n)) =
    a n + -c m + (-b m + b m) + (b n + -b n) := by ac_rfl
  rw [this]; clear this
  rw [Rat.neg_self_add, Rat.add_neg_self, Rat.add_zero, Rat.add_zero]

instance CauchySeq.setoid : Setoid CauchySeq := ⟨Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩

def Real := Quotient CauchySeq.setoid
notation "ℝ" => Real
def Real.mk : CauchySeq -> ℝ := Quotient.mk _

local notation "⟦" v "⟧" => Real.mk v

def CauchySeq.ofRat (q: ℚ) : CauchySeq where
  seq _ := q
  is_cacuhy ε ε_pos := by
    refine ⟨0, ?_⟩
    intro n m _ _
    simp
    rw [Rat.sub_self]
    assumption


def Real.ofRat (q: ℚ) : ℝ := ⟦.ofRat q⟧

@[refl]
def CauchySeq.refl (a: CauchySeq) : a ≈ a := CauchySeq.Equiv.refl a
@[symm]
def CauchySeq.symm {a b: CauchySeq} : a ≈ b -> b ≈ a := CauchySeq.Equiv.symm

instance : Coe ℚ ℝ := ⟨.ofRat⟩
instance : OfNat ℝ n := ⟨(OfNat.ofNat n: ℚ)⟩

def CauchySeq.add.spec (a b c d: CauchySeq) :
  a ≈ c -> b ≈ d ->
  is_cauchy_equiv (fun n => a n + b n) (fun n => c n + d n) := by
  intro ac bd ε ε_pos
  have ⟨δ, h⟩ := (ac _ (Rat.half_pos ε_pos)).merge (bd _ (Rat.half_pos ε_pos))
  refine ⟨δ, ?_⟩
  intro n m δ_le_n δ_le_m
  show ‖a n + b n - (c m + d m)‖ < ε
  rw [Rat.sub_eq_add_neg, Rat.neg_add]
  have : ‖a n + b n + (-c m + -d m)‖ =
    ‖a n + -c m + (b n + -d m)‖ := by ac_rfl
  rw [this]; clear this
  replace ⟨ab, cd⟩  := h n m δ_le_n δ_le_m
  have := Rat.add_lt_add ab cd
  rw [←Rat.mul_two, Rat.mul_div_cancel] at this
  apply lt_of_le_of_lt _ this
  rw [←Rat.sub_eq_add_neg, ←Rat.sub_eq_add_neg]
  apply Rat.abs_add_le_add_abs

def CauchySeq.add (a b: CauchySeq) : CauchySeq where
  seq n := a n + b n
  is_cacuhy := by apply CauchySeq.add.spec <;> rfl

instance : Add CauchySeq := ⟨.add⟩

def Real.add : ℝ -> ℝ -> ℝ := by
  apply Quotient.lift₂ (⟦· + ·⟧)
  intros
  apply Quotient.sound
  apply CauchySeq.add.spec <;> assumption

instance : Add ℝ := ⟨.add⟩

@[simp]
def Real.mk_add (a b: CauchySeq) : ⟦a⟧ + ⟦b⟧ = ⟦a + b⟧ := rfl

def CauchySeq.neg.spec (a b: CauchySeq) :
  a ≈ b ->
  is_cauchy_equiv (fun n => -a n) (fun n => -b n) := by
  intro ab ε ε_pos
  have ⟨δ, h⟩ := ab _ ε_pos
  refine ⟨δ, ?_⟩
  intro n m δ_le_n δ_le_m
  simp
  rw [Rat.neg_sub_neg, Rat.abs_sub_comm]
  apply h <;> assumption

def CauchySeq.neg (a: CauchySeq) : CauchySeq where
  seq n := -a n
  is_cacuhy := by apply CauchySeq.neg.spec <;> rfl

instance : Neg CauchySeq := ⟨.neg⟩

def Real.neg : ℝ -> ℝ := by
  apply Quotient.lift (⟦-·⟧)
  intros
  apply Quotient.sound
  apply CauchySeq.neg.spec <;> assumption

instance : Neg ℝ := ⟨.neg⟩
