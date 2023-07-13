/- # Formally real semirings -/

import Mathlib.NumberTheory.Cyclotomic.Basic

open BigOperators

/- ## Sums of squares

To define formally real semirings, we first define what it means to be a sum of squares in a semiring. -/

def sum_of_squares {R : Type _} [Semiring R] : List R → R
  | [] => 0
  | (a :: L) => (a ^ 2) + (sum_of_squares L)

def is_sum_of_squares {R : Type _} [Semiring R] (x : R) : Prop := ∃ L : List R, sum_of_squares L = x

/- A few sanity checks -/

#check [1, 2, 3]
#check [1, -2, 3]

#eval sum_of_squares [1, 2, 3]
#eval sum_of_squares [1, -2, 3]

#eval sum_of_squares ([] : List ℕ)

/- Note that we can prove that `sum_of_squares [1, 2, 3] = 14` just by using `rfl` -/

example : sum_of_squares [1, 2, 3] = 14 := rfl

/- If a list is built by concatenation, we can compute its sum of squares from the sums of squares of each constructor. -/

#eval 0::[1,2,3]
#eval [1,2,3]++[1,2,3]

#eval sum_of_squares (0::[1,2,3])
#eval sum_of_squares ([1,2,3]++[1,2,3])

/- We now give a proof of these results, as well as of other useful facts about sums of squares. -/

@[simp]
def sum_of_squares_head_tail {R : Type _} [Semiring R] (x : R) (L : List R) : sum_of_squares (x :: L) = (sum_of_squares [x]) + (sum_of_squares L) := by
  simp [sum_of_squares]
  done

@[simp]
def sum_of_squares_concat {R : Type _} [Semiring R] (L1 L2 : List R) : sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2 := by
  induction' L1 with x L ih
  · simp [sum_of_squares]
  · rw [List.cons_append, sum_of_squares_head_tail x L, add_assoc, ← ih]
    simp [sum_of_squares]
  done

def sum_of_squares_of_list {R : Type _} [Semiring R] (L : List R) : sum_of_squares L = (L.map (.^2)).sum := by
  induction' L with a L ih
  · simp [sum_of_squares]
  · rw[sum_of_squares_head_tail, ih]
    simp [sum_of_squares]
  done

def sum_of_squares_of_list_div {F : Type _} [Semifield F] (L : List F) (c : F) (h : c ≠ 0) : sum_of_squares (L.map (./c)) = sum_of_squares L / (c^2) := by
  rw [sum_of_squares_of_list]
  simp [sum_of_squares]
  have comp : ((fun x => x ^ 2) ∘ (fun x => x / c)) = (fun x => x ^ 2 * (c ^ 2)⁻¹ ) := by
    ext x
    field_simp
  rw [comp, sum_of_squares_of_list, div_eq_mul_inv, List.sum_map_mul_right]
  done

def sum_of_squares_erase {R : Type _} [Semiring R] [BEq R] (L : List R) (a : R) (h : a ∈ L): sum_of_squares L = a ^ 2 + sum_of_squares (List.erase L a) := by
  sorry -- use List.sum_map_erase

-- **TASK 1:** Complete the proof above

/- ## Definition of formally real semirings -/

@[mk_iff]
class IsFormallyReal (R : Type _) [Semiring R] : Prop where
  is_formally_real : ∀ L : List R, sum_of_squares L = 0 → (∀ x ∈ L, x = 0)

lemma IsFormallyReal_iff_Fin (R : Type _) [Semiring R] : IsFormallyReal R ↔
    ∀ (n : ℕ), ∀ (f : Fin n → R), (∑ i, (f i) ^ 2 = 0) → (∀ i, f i = 0) := by
  refine' ⟨fun h n f hf i => _, fun h => ⟨fun L => List.ofFnRec (fun n f H a ha => _) L⟩⟩
  · refine' h.is_formally_real (List.ofFn f) _ (f i) (by simp [List.mem_ofFn])
    simp [sum_of_squares, sum_of_squares_of_list, List.sum_ofFn, hf]
  · rw [sum_of_squares_of_list, List.map_ofFn, List.sum_ofFn] at H
    obtain ⟨j, rfl⟩ := (List.mem_ofFn _ _).1 ha
    exact h n f H j

lemma IsFormallyReal_iff_Multiset (R : Type _) [Semiring R] : IsFormallyReal R ↔
    ∀ (M : Multiset R), (M.map (.^2)).sum = 0 → (∀ x ∈ M, x = 0) := by
  refine' ⟨fun h M hM x hx => _, fun h => ⟨fun L hL x hx => _⟩⟩
  · refine' h.is_formally_real M.toList _ x (Multiset.mem_toList.2 hx)
    convert hM
    rw [sum_of_squares_of_list]
    conv_rhs => rw [← Multiset.coe_toList M]
    rw [Multiset.coe_map, Multiset.coe_sum]
  · refine' h L _ _ (by simp [hx])
    convert hL
    simp [sum_of_squares_of_list]

/- As an example, we show that ordered semirings are formally real. -/

@[simp]
lemma sum_sq_nonneg {A : Type _} [LinearOrderedRing A] (L : List A) : 0  ≤ sum_of_squares L := by
  induction' L with head tail ih
  . rfl
  . apply add_nonneg
    . exact sq_nonneg head
    . exact ih

instance {A : Type _} [LinearOrderedRing A] : IsFormallyReal A where
  is_formally_real := fun (L : List A) (sum_sq_zero: sum_of_squares L = 0) ↦ by
    intro a a_in_L
    by_contra c
    have a_sq_pos : 0 < a ^ 2 := by exact Iff.mpr (sq_pos_iff a) c
    have h : a ^ 2 + sum_of_squares (L.erase a) = sum_of_squares L := by exact Eq.symm (sum_of_squares_erase L a a_in_L)
    rw [sum_sq_zero] at h
    have sum_sq_nonneg : 0 ≤ sum_of_squares (L.erase a) := by simp
    have sum_sq_pos: 0 < a ^ 2 + sum_of_squares (L.erase a) := by exact add_pos_of_pos_of_nonneg a_sq_pos sum_sq_nonneg
    have : a ^ 2 + sum_of_squares (L.erase a) ≠ 0 := by exact ne_of_gt sum_sq_pos
    contradiction

/- ## Properties of formally real semirings

We first want to show that, if `R` is a *non-trivial* formally real *ring*, then `-1` is not a sum of squares in `R`. We deduce this from the more general fact that, if `R` is a formally real nontrivial *semiring*, then there does *not* exist a sum of squares `S` in `R` such that `1 + S = 0`.-/

def one_add_sum_of_squares_neq_zero {R : Type _} [Semiring R] [ntR : Nontrivial R] : IsFormallyReal R → ¬ (∃ L : List R, 1 + sum_of_squares L = 0) := by
  intro h ⟨L, hL⟩
  have h1 := h.is_formally_real (1 :: L)
  simp [sum_of_squares] at h1
  exact h1 hL
  done

 /- Next, we show that a non-trivial formally real semiring is of characteristic 0. -/

 -- **TASK 2:** Prove the claim above

 /- ## Formally real semifields

 We prove that, in a semifield, the converse to `one_add_sum_of_squares_neq_zero` holds, namely: if there is no sum of squares `S` such that `1 + S = 0`, then the semifield `F` is formally real. -/

 def sum_of_sq_eq_zero_iff_all_zero {F : Type _} [Semifield F] : ¬(∃ L : List F, 1 + sum_of_squares L = 0) → IsFormallyReal F := by
  classical
  intro h
  push_neg at h
  constructor
  intro L hL
  by_contra hL1
  push_neg at hL1
  rcases hL1 with ⟨x, hx1, hx2⟩
  -- We are going to construct a list L such that 1 + sum_of_squares L = 0, thus contradicting h
  let L' := L.map (./x)
  have hL' : sum_of_squares L' = sum_of_squares L / (x^2) := by
    rw [← sum_of_squares_of_list_div L x hx2]
  have hx3 : (x / x) ∈ L' := List.mem_map_of_mem (·/x) hx1
  rw [div_self hx2] at hx3
  let L'' := List.erase L' 1
  have hL'1 : sum_of_squares L' = 0 := by
    rw [hL',hL]
    simp
  have hL'2 : sum_of_squares L' = 1 + sum_of_squares L'' := by
    simp [sum_of_squares_erase _ (1 : F) hx3]
  rw [hL'1] at hL'2
  exact h L'' hL'2.symm
  done

 /- In particular, **a field `F` is formally real if and only if `-1` is not a sum of squares in `F`**. -/

 def formally_real_semifield_equiv {F : Type _} [Semifield F] : (IsFormallyReal F) ↔ ¬ (∃ L : List F, 1 + sum_of_squares L = 0) := by
   classical
   constructor
   · exact one_add_sum_of_squares_neq_zero
   · exact sum_of_sq_eq_zero_iff_all_zero
   done

 /- ## Positive cones -/

 -- We define positive cones and show how maximal positive cones induce orderings.

def squares (A : Type _) [Semiring A] : Set A := {a | ∃ (b : A), a = b ^ 2}

def cone_of_squares (A : Type _) [Semiring A] := AddSubmonoid.closure (squares A)

lemma is_sum_of_squares_iff_mem_cone_of_squares {A : Type _} [Semiring A] (a : A) :
    is_sum_of_squares a ↔ a ∈ cone_of_squares A := by
  refine' ⟨fun ⟨L, hL⟩ => _, fun h => _⟩
  · rw [← hL, sum_of_squares_of_list]
    refine' AddSubmonoid.list_sum_mem _ (fun a ha => AddSubmonoid.subset_closure _)
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 ha
    exact ⟨b, rfl⟩
  · refine' AddSubmonoid.closure_induction h (fun a ⟨b, hb⟩ => ⟨[b], _⟩) (⟨[], by simp [sum_of_squares]⟩)
      (fun a b ⟨L₁, h₁⟩ ⟨L₂, h₂⟩ => ⟨L₁ ++ L₂, _⟩)
    · rw [hb]
      simp [sum_of_squares]
    · rw [← h₁, ← h₂]
      simp

theorem cone_of_squares.mem_mul {A : Type _} [Semiring A] {x y : A}
    (hx : x ∈ cone_of_squares A) (hy : y ∈ cone_of_squares A) :
    x * y ∈ cone_of_squares A := sorry

 /- ## Artin-Schreier theory -/

 /- We show that formally real fields admit an ordering, not unique in general.

 In particular, **a field `F` is formally real if and only if it admits an ordering.** -/

def PositiveCones (A : Type _) [Ring A] :=
  { P : Subsemiring A | squares A ⊆ P ∧ -1 ∉ P }

theorem PositiveCones.nonEmpty (A : Type _) [Ring A] [IsFormallyReal A] :
    Nonempty (PositiveCones A) :=
  sorry

theorem cone_add_element {F : Type _} [Field F] (P : Subsemiring F) (hP : P ∈ PositiveCones F)
    (a : F) (h1 : a ∉ P) (h2 : -a ∉ P) : Subsemiring.closure (P ∪ {a}) ∈ PositiveCones F := by
  unfold PositiveCones
  constructor
  · suffices h1 : P ≤  Subsemiring.closure (P ∪ {a}) by
      · refine' le_trans _ h1
        exact hP.1
    suffices (P : Set F) ⊆ P ∪ {a} by
      · refine' subset_trans this _
        exact Subsemiring.subset_closure
    exact Set.subset_union_left ↑P {a}
  · by_contra h3
    have h4 : ∃ (x y : F), (x ∈ P) ∧ (y ∈ P) ∧ (-1 = x + a * y) := sorry
    rcases h4 with ⟨x, y, hx, hy, hxy⟩
    by_cases y = 0
    rw [h] at hxy
    simp at hxy
    rw [← hxy] at hx
    exact hP.2 hx
    have ha : -a = (y⁻¹)^2 * y * (1 + x) := by
      field_simp [h]
      rw [neg_eq_iff_eq_neg.1 hxy]
      ring
    have ha2 : -a ∈ P := by
      have hy2 : (y⁻¹)^2 ∈ P := by
        apply hP.1
        use y⁻¹
      have hx2 : 1 ∈ P := by
        rw [← one_pow 2]
        apply hP.1
        use 1
      have hx3 : 1 + x ∈ P := by
        apply Subsemiring.add_mem
        exact hx2
        exact hx
      have aux : (y⁻¹)^2 * y * (1 + x) ∈ P := by
        apply Subsemiring.mul_mem
        have aux2 : (y⁻¹)^2 * y ∈ P := by
          apply Subsemiring.mul_mem
          exact hy2
          exact hy
        exact aux2
        exact hx3
      rw [← ha] at aux
      exact aux
    exact h2 ha2
  done
