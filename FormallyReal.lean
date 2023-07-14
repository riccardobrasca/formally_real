/- # Formally real semirings -/

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Tactic.Polyrith

open BigOperators

/- ## Sums of squares

To define formally real semirings, we first define what it means to be a sum of squares in a semiring. -/

def sum_of_squares {R : Type _} [Semiring R] : List R → R
  | [] => 0
  | (a :: L) => (a ^ 2) + (sum_of_squares L)

example : sum_of_squares [1, -2, 3] = 14 := rfl

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


def sum_of_squares_erase {R : Type _} [Semiring R] [DecidableEq R] (L : List R) (a : R) (h : a ∈ L): sum_of_squares L = a ^ 2 + sum_of_squares (List.erase L a) := by
  rw [sum_of_squares_of_list, sum_of_squares_of_list, ← Multiset.coe_sum,
    ← Multiset.coe_sum, ← Multiset.coe_map, ← Multiset.coe_map,  ← Multiset.sum_cons,
    ← Multiset.map_cons (.^2), ← Multiset.cons_erase (show a ∈ (L : Multiset R) from h)]
  simp

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

 theorem FormallyRealIsOfChar0 {R : Type _} [Semiring R] [hFR : IsFormallyReal R] : CharP R 0 := by
  constructor
  intro x
  constructor
  · intro h1
    simp
    sorry
  · intro h1
    simp at h1
    sorry

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

 theorem formally_real_semifield_equiv {F : Type _} [Semifield F] :
    (IsFormallyReal F) ↔ ¬ (∃ L : List F, 1 + sum_of_squares L = 0) := by
   classical
   constructor
   · exact one_add_sum_of_squares_neq_zero
   · exact sum_of_sq_eq_zero_iff_all_zero
   done

 theorem formally_real_field_equiv {F : Type _} [Field F] :
    (IsFormallyReal F) ↔ ¬ is_sum_of_squares (-1 : F) := by
  unfold is_sum_of_squares
  rw [formally_real_semifield_equiv]
  constructor
  · intro h h1
    obtain ⟨L, hL⟩ := h1
    have hh : 1 + sum_of_squares L = 0 := by rw [hL]; ring
    apply h
    use L
    exact hh
  · intro h h1
    obtain ⟨L, hL⟩ := h1
    apply h
    use L
    rw [add_eq_zero_iff_neg_eq] at hL
    exact hL.symm


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

theorem cone_of_squares.mem_mul {A : Type _} [CommSemiring A] {x y : A}
    (hx : x ∈ cone_of_squares A) (hy : y ∈ cone_of_squares A) :
    x * y ∈ cone_of_squares A := by

  refine' AddSubmonoid.closure_induction₂ hx hy _ _ _ _ _
  · intro x h1 y h2
    obtain ⟨x1, hx1⟩ := h1
    obtain ⟨x2, hx2⟩ := h2
    rw [hx1, hx2, ← mul_pow]
    apply AddSubmonoid.subset_closure
    use x1 * x2
  · intro x
    rw [mul_eq_zero_of_left]
    apply AddSubmonoid.subset_closure
    use 0
    rw [zero_pow (by norm_num)]
    rfl
  · intro x
    rw [mul_eq_zero_of_right]
    apply AddSubmonoid.subset_closure
    use 0
    rw [zero_pow (by norm_num)]
    rfl
  · intro x y z h1 h2
    rw [right_distrib]
    apply AddSubmonoid.add_mem _ h1 h2
  · intro x y z h1 h2
    rw [left_distrib]
    apply AddSubmonoid.add_mem _ h1 h2

theorem cone_of_squares_eq_Subsemiring (A : Type _) [CommSemiring A] :
    (Subsemiring.closure (squares A) : Set A) = (cone_of_squares A : Set A) := by
  apply le_antisymm
  · intro x hx
    refine' Subsemiring.closure_induction hx _ _ _ _ _
    · intro y hy
      apply AddSubmonoid.subset_closure hy
    · exact AddSubmonoid.zero_mem _
    · apply AddSubmonoid.subset_closure
      use 1
      simp
    · intro x y hx hy
      exact AddSubmonoid.add_mem _ hx hy
    · intro x y hx hy
      exact cone_of_squares.mem_mul hx hy
  · intro x hx
    refine' AddSubmonoid.closure_induction hx _ _ _
    · intro y hy
      apply Subsemiring.subset_closure hy
    · exact Subsemiring.zero_mem _
    · intro x y hx hy
      exact Subsemiring.add_mem _ hx hy

 /- ## Artin-Schreier theory -/

 /- We show that formally real fields admit an ordering, not unique in general.

 In particular, **a field `F` is formally real if and only if it admits an ordering.** -/

def PositiveCones (A : Type _) [Ring A] :=
  { P : Subsemiring A | squares A ⊆ P ∧ -1 ∉ P }

theorem PositiveCones.nonEmpty (A : Type _) [Field A] [hA : IsFormallyReal A] :
    Nonempty (PositiveCones A) := by
  constructor
  use Subsemiring.closure (squares A)
  constructor
  · apply Subsemiring.subset_closure
  · change ¬(_ ∈ (_ : Set A))
    rw [cone_of_squares_eq_Subsemiring]
    intro h
    simp at h
    rw [← is_sum_of_squares_iff_mem_cone_of_squares] at h
    apply formally_real_field_equiv.1 hA
    exact h

lemma span_cone_union_singleton {F : Type _} [Field F] (P : Subsemiring F)
    (hP : P ∈ PositiveCones F) (a : F) : (Subsemiring.closure (P ∪ {a}) : Set F) =
    { z : F | ∃ (x y : F), (x ∈ P) ∧ (y ∈ P) ∧ (z = x + a * y) } := by
  apply le_antisymm
  · intro z hz
    refine' Subsemiring.closure_induction hz _ _ _ _ _
    · intro z hz
      cases' hz with hz1 hz2
      · refine' ⟨z, 0, ⟨hz1, Subsemiring.zero_mem _, by simp⟩⟩
      · use 0
        use 1
        constructor
        exact Subsemiring.zero_mem _
        constructor
        exact Subsemiring.one_mem _
        simp at hz2
        rw [hz2]
        simp
    · use 0
      use 0
      constructor
      exact Subsemiring.zero_mem _
      constructor
      exact Subsemiring.zero_mem _
      simp
    · use 1
      use 0
      constructor
      exact Subsemiring.one_mem _
      constructor
      exact Subsemiring.zero_mem _
      simp
    · intro x y hx hy
      rcases hx with ⟨x1, y1, hx1, hy1, hx1y1⟩
      rcases hy with ⟨x2, y2, hx2, hy2, hx2y2⟩
      use x1 + x2
      use y1 + y2
      constructor
      · exact Subsemiring.add_mem _ hx1 hx2
      · constructor
        · exact Subsemiring.add_mem _ hy1 hy2
        · rw [hx2y2]
          rw [hx1y1]
          ring
    intro x y hx hy
    rcases hx with ⟨x1, y1, hx1, hy1, hx1y1⟩
    rcases hy with ⟨x2, y2, hx2, hy2, hx2y2⟩
    use x1 * x2 + a^2 * y1 * y2
    use x1 * y2 + x2 * y1
    constructor
    · apply Subsemiring.add_mem _
      apply Subsemiring.mul_mem _
      exact hx1
      exact hx2
      apply Subsemiring.mul_mem _
      apply Subsemiring.mul_mem _
      apply hP.1
      use a
      exact hy1
      exact hy2
    · constructor
      · apply Subsemiring.add_mem _
        apply Subsemiring.mul_mem _
        exact hx1
        exact hy2
        apply Subsemiring.mul_mem _
        exact hx2
        exact hy1
      · rw [hx1y1, hx2y2]
        ring
  · rintro z ⟨x, y, hx, hy, hz⟩
    rw [hz]
    apply Subsemiring.add_mem
    apply Subsemiring.subset_closure
    apply Set.mem_union_left
    exact hx
    apply Subsemiring.mul_mem
    apply Subsemiring.subset_closure
    apply Set.mem_union_right
    simp
    apply Subsemiring.subset_closure
    apply Set.mem_union_left
    exact hy
  done

theorem cone_add_element {F : Type _} [Field F] (P : Subsemiring F) (hP : P ∈ PositiveCones F)
    (a : F) (h1 : a ∉ P) (h2 : -a ∉ P) : (P < Subsemiring.closure (P ∪ {a})) ∧ (Subsemiring.closure (P ∪ {a}) ∈ PositiveCones F) := by
  constructor
  · by_contra' h
    have h' : P ≤ Subsemiring.closure (P ∪ {a}) := by
      suffices (P : Set F) ≤ (P ∪ {a} : Set F) by
        · apply le_trans this Subsemiring.subset_closure
      simp
    replace h' := le_iff_lt_or_eq.1 h'
    have h''' : ¬(P< Subsemiring.closure (P ∪ {a}))  → P = Subsemiring.closure (P ∪ {a}) := by
      apply or_iff_not_imp_right.1 h'.symm
    have H4 : P = Subsemiring.closure (P ∪ {a}) := by
      exact h''' h
    apply h1
    rw [H4]
    apply Subsemiring.subset_closure
    exact Set.mem_union_right _ rfl
  · unfold PositiveCones
    constructor
    · suffices h1 : P ≤  Subsemiring.closure (P ∪ {a}) by
        · refine' le_trans _ h1
          exact hP.1
      suffices (P : Set F) ⊆ P ∪ {a} by
        · refine' subset_trans this _
          exact Subsemiring.subset_closure
      exact Set.subset_union_left ↑P {a}
    · by_contra h3
      have h4 : ∃ (x y : F), (x ∈ P) ∧ (y ∈ P) ∧ (-1 = x + a * y) := by
        change _ ∈ (_ : Set F) at h3
        rw [span_cone_union_singleton P hP] at h3
        exact h3
      rcases h4 with ⟨x, y, hx, hy, hxy⟩
      by_cases y = 0
      rw [h] at hxy
      simp at hxy
      rw [← hxy] at hx
      exact hP.2 hx
      have ha : -a = (y⁻¹)^2 * y * (1 + x) := by
        field_simp [h]
        -- polyrith
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

theorem exists_maximal_pos_cone {A: Type _} [Ring A] [IsFormallyReal A]
    (hne: Nonempty (PositiveCones A)) :
    ∃ P ∈ PositiveCones A, ∀ S ∈ PositiveCones A, P ≤ S → S = P := by
  -- proving zorn lemma's condition holds
  have zorn_hypothesis : ∀ C, C ⊆ PositiveCones A → IsChain (. ≤ .) C →
      ∀ x ∈ C, ∃ ub ∈ PositiveCones A, ∀ z ∈ C, z ≤ ub := by
    intro C C_in_pos_cone C_is_chain Q Q_in_C
    use sSup C
    constructor
    . unfold PositiveCones
      simp
      constructor
      . intro a a_in_sq
        simp
        apply (Subsemiring.mem_sSup_of_directedOn ⟨Q, Q_in_C⟩ C_is_chain.directedOn).2
        have Q_in_pos_cone : Q ∈ PositiveCones A := by exact C_in_pos_cone Q_in_C
        unfold PositiveCones at Q_in_pos_cone
        simp at Q_in_pos_cone
        have a_in_Q : a ∈ Q := by apply Q_in_pos_cone.1 a_in_sq
        exact ⟨Q, Q_in_C, a_in_Q⟩
      . rcases Subsemiring.mem_sSup_of_directedOn ⟨Q, Q_in_C⟩ C_is_chain.directedOn with h
        rw [h]
        push_neg
        intro S S_in_C
        have S_in_pos_cone : S ∈ PositiveCones A := by exact C_in_pos_cone S_in_C
        unfold PositiveCones at S_in_pos_cone
        simp at S_in_pos_cone
        exact S_in_pos_cone.2
    . intro L L_in_C
      exact le_sSup L_in_C

  -- using zorn lemma
  rcases hne with ⟨B, B_in_pos_cone⟩
  rcases zorn_nonempty_partialOrder₀ (PositiveCones A) zorn_hypothesis B B_in_pos_cone
    with ⟨M, M_in_pos_cone, ⟨_, M_is_maximal⟩⟩
  use M
  constructor
  . exact M_in_pos_cone
  . apply M_is_maximal
