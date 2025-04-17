import Math.Data.List.Algebra
import Math.Algebra.Ring.Theory.Ideal.TwoSided.Lattice
import Math.Algebra.Dvd

namespace Ideal

variable [RingOps α] [IsRing α]

def principal (a: α) : Ideal α where
  carrier := Set.mk fun x => ∃l: List (α × α), x = (l.map fun (r, s) => (r * a * s)).sum
  mem_zero := by exists []
  mem_neg := by
    simp only [Set.mk_mem, forall_exists_index, forall_eq_apply_imp_iff]
    intro l
    exists l.map (fun (r, s) => (-r, s))
    induction l  with
    | nil => apply neg_zero
    | cons x l ih =>
      obtain ⟨r, s⟩ := x
      simp only [List.map_cons, List.sum_cons, List.map_map]
      rw [neg_add_rev, add_comm, neg_mul, neg_mul, ih,
        List.map_map]
  mem_add := by
    simp only [Set.mk_mem, forall_exists_index]
    rintro _ _ x rfl y rfl
    exists x ++ y
    rw [List.map_append, List.sum_append]
  mem_mul_left := by
    simp only [Set.mk_mem, forall_exists_index, forall_eq_apply_imp_iff]
    rintro r₀ l
    exists l.map (fun (r, s) => (r₀ * r, s))
    induction l  with
    | nil => apply mul_zero
    | cons x l ih =>
      obtain ⟨r, s⟩ := x
      simp only [List.map_cons, List.sum_cons, List.map_map]
      rw [mul_add, mul_assoc r₀, mul_assoc r₀, ih,
        List.map_map]
  mem_mul_right := by
    simp only [Set.mk_mem, forall_exists_index, forall_eq_apply_imp_iff]
    rintro r₀ l
    exists l.map (fun (r, s) => (r, s * r₀))
    induction l  with
    | nil => apply zero_mul
    | cons x l ih =>
      obtain ⟨r, s⟩ := x
      simp only [List.map_cons, List.sum_cons, List.map_map]
      rw [add_mul, ←mul_assoc _ _ r₀, ih, List.map_map]

-- a principal ideal is one which is generated by a single element
def IsPrincipal (i: Ideal α) : Prop := ∃a: α, i = principal a

def principal_is_principal (a: α) : (principal a).IsPrincipal := ⟨a, rfl⟩
-- the principal ideal of `a` is the ideal generated by `a`
def principal_eq_generate (a: α) : principal a = generate {a} := by
  ext x
  apply Iff.intro
  · rintro ⟨l, rfl⟩
    dsimp
    apply mem_list_sum
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨r, s, rfl⟩ := hx
    apply mem_mul_right
    apply mem_mul_left
    apply Generate.of
    rfl
  · intro h
    apply of_mem_generate {a}
    rintro x rfl
    exists [(1, 1)]
    simp
    assumption
-- the principal ideal is the smallest ideal which contains a
def principal_spec (a: α) : principal a = ⨅ (Set.mk fun i => a ∈ i) := by
  rw [principal_eq_generate, generate_spec]
  congr
  ext i
  rw [Set.singleton_sub]
  rfl

def bot_is_principal : IsPrincipal (α := α) ⊥ := by
  exists 0
  rw [principal_eq_generate]
  ext x
  apply Iff.intro
  apply bot_le (α := Ideal α)
  intro h
  apply of_mem_generate _ _ _ _ h
  rintro _ rfl
  apply mem_zero

def top_is_principal : IsPrincipal (α := α) ⊤ := by
  exists 1
  rw [principal_eq_generate]
  ext x
  apply flip Iff.intro
  apply le_top (α := Ideal α)
  intro
  rw [←mul_one x]
  apply mem_mul_left
  apply Generate.of
  rfl

section Dvd

variable [Dvd α] [IsCommMagma α] [IsLawfulDvd α]

def of_dvd (a: α) : Ideal α where
  carrier := Set.mk fun x => a ∣ x
  mem_zero := dvd_zero _
  mem_add := by
    intro x y hx hy
    apply dvd_add
    assumption
    assumption
  mem_neg := by
    intro x hx
    apply dvd_neg.mp
    assumption
  mem_mul_left := by
    intro r x hx
    apply dvd_trans hx
    exact dvd_mul_right x r
  mem_mul_right := by
    intro r x hx
    apply dvd_trans hx
    exact dvd_mul_left x r

def of_dvd_eq_principal (a: α) : of_dvd a = principal a := by
  rw [principal_eq_generate]
  apply flip le_antisymm
  rintro x h
  apply of_mem_generate _ _ _ _ h
  rintro x rfl
  apply dvd_refl
  rintro _ h
  obtain h : a ∣ _ := h
  rw [dvd_iff] at h
  obtain ⟨k, rfl⟩ := h
  show _ ∈ generate {a}
  apply mem_mul_right
  apply Generate.of
  rfl

def of_dvd_principal (a: α) : IsPrincipal (of_dvd a) := by
  exists a
  apply of_dvd_eq_principal

end Dvd

end Ideal
