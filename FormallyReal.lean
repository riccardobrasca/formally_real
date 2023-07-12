/- # Formally real semirings -/

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Data.Multiset.Fintype
-- import Mathlib.Tactic

open BigOperators

/- We define formally real semirings. To do so, we define what it means to be a sum of squares in a semiring. -/

def sum_of_squares {A : Type _} [Semiring A] : Multiset A → A :=
  fun M => (M.map (.^2)).sum
  -- fun f => ∑ i , (f i) ^ 2

-- notation "sum_sq" => sum_of_squares

@[mk_iff]
class IsFormallyReal (A : Type _) [Semiring A] : Prop where
  is_formally_real : ∀ L : Multiset A, sum_of_squares L = 0 → (∀ x ∈ L, x = 0)
  -- ∀ (n : ℕ), ∀ (f : Fin n → A), (sum_of_squares f = 0) → (∀ i, f i = 0)

example (A : Type _) [Semiring A] : IsFormallyReal A ↔
    ∀ (n : ℕ), ∀ (f : Fin n → A), (∑ i, (f i) ^ 2 = 0) → (∀ i, f i = 0) := by
  classical
  refine' ⟨fun h n f hf i => _, fun h => ⟨_⟩⟩
  · let M := (Multiset.map f Finset.univ.1)
    have hM : (M.map (.^2)).sum = ∑ i, (f i) ^ 2 := by
      simp only [Multiset.map_map, Function.comp_apply]
      rfl  
    rw [hf] at hM
    refine' h.is_formally_real M hM (f i) _
    simp
  · suffices ∀ L : List A, (L.map (.^2)).sum = 0 → (∀ x ∈ L, x = 0) by
      · intro M hM a ha
        refine' this M.toList _ a (Multiset.mem_toList.2 ha)
        rw [← hM]
        unfold sum_of_squares
        sorry --Generalize `Multiset.sum_toList` to include a function
    intro L
    refine' List.ofFnRec (fun n f H a ha => _) L
    rw [List.map_ofFn, List.sum_ofFn] at H
    obtain ⟨j, rfl⟩ := (List.mem_ofFn _ _).1 ha
    exact h n f H j
    
      
      
      
/- Next, we give basic properties of sums of squares in semirings. -/

variable {A F : Type _}

def squares (A : Type _) [Semiring A] : Set A := {a | ∃ (b : A), a = b ^ 2}

def cone_of_squares (A : Type _) [Semiring A] := AddSubmonoid.closure (squares A)

@[reducible]
def is_sum_of_squares [Semiring A] (S : A) : Prop := S ∈ cone_of_squares A

def sum_sq_add_sum_sq_is_sum_sq [Semiring A] (S1 S2 : A) (h1 : is_sum_of_squares S1) (h2 : is_sum_of_squares S2) : is_sum_of_squares (S1 + S2) := by
  apply AddSubmonoid.add_mem _ h1 h2
  done

/- ## Properties of formally real semirings -/

section ppties_of_formally_real_semirings

/- We first show that if a *non-trivial* ring A is formally real, then -1 is not a sum of squares. 

More generally, if `A` is a formally real nontrivial *semiring* (so `-1` does not make sense in `A`), then we prove that there does *not* exist a sum of squares `S` in `A` such that `1 + S = 0`. -/

theorem _root_.Multiset.exists_map_of_mem_image {α β : Type _} [Nonempty α] {f : α → β}
    {s : Multiset β} (hs : ∀ x ∈ s, ∃ y, f y = x) :
    ∃ t : Multiset α, t.map f = s := by
  sorry

def sum_sq_neq_minus_one {A : Type _} [Semiring A] [ntA : Nontrivial A] : IsFormallyReal A → ¬(∃ S ∈ cone_of_squares A, 1 + S = 0) := by
  intro hA
  by_contra h
  rcases h with ⟨ S, hS1, hS2 ⟩
  have hS3 := AddSubmonoid.exists_multiset_of_mem_closure hS1
  rcases hS3 with ⟨ T, hT, hT1 ⟩
  have hope : ∃ T' : Multiset A, T'.map (.^2) = T := sorry
  rcases hope with ⟨ T', rfl ⟩
  replace hT1 := congr_arg (fun a => 1 + a) hT1
  simp at hT1
  rw [hS2, ← one_pow 2] at hT1
  rw [← Multiset.sum_cons] at hT1
  rw [← Multiset.map_cons (.^2)] at hT1
  have ccl := hA.is_formally_real _ hT1 1 (by simp)
  simp at ccl
  
def sum_sq_neq_minus_one' {A : Type _} [Semifield A] [ntA : Nontrivial A] :
    ¬(∃ S ∈ cone_of_squares A, 1 + S = 0) → IsFormallyReal A := by
  classical
  intro hA
  constructor
  intro M hM
  by_contra' h
  obtain ⟨x, hxmem, hxzero⟩ := h
  dsimp [sum_of_squares] at hM
  rw [← Multiset.cons_erase hxmem, Multiset.map_cons, Multiset.sum_cons] at hM
  apply hA
  replace hM := congr_arg (fun a => a * (x⁻¹) ^ 2) hM
  simp only at hM
  rw [add_mul, inv_pow] at hM
  simp only [ne_eq, zero_lt_two, pow_eq_zero_iff, hxzero, not_false_eq_true, mul_inv_cancel, zero_mul] at hM 
  sorry


  

/- As an example, we show that ordered semirings are formally real. -/

-- **TASK 1:** Prove the above claim.

/- Next, we show that a non-trivial formally real semiring is of characteristic 0. -/

-- **TASK 2:** Prove the above claim.

/- ## Formally real semifields -/

section Formally_real_semifields

/- We prove that, in a semifield, the converse to `sum_sq_neq_minus_one` holds, namely: if there is no sum of squares `S` such that `1 + S = 0`, then the semifield is formally real. -/

def sum_of_sq_eq_zero_iff_all_zero {F : Type _} [Semifield F] [BEq F] : (∀ n : ℕ, ∀ f : Fin n → F, 1 + sum_of_squares f ≠ 0) → IsFormallyReal F := sorry

/- In particular, **a field `F` is formally real if and only if `-1` is not a sum of squares in `F`**. -/

def formally_real_semifield_equiv {F : Type _} [Semifield F] [BEq F] : IsFormallyReal F ↔ ∀ n : ℕ, ∀ f : Fin n → F, 1 + sum_of_squares f ≠ 0 := by
  constructor
  · exact sum_sq_neq_minus_one
  · exact sum_of_sq_eq_zero_iff_all_zero
  done 

def formally_real_field_equiv {F : Type _} [Field F] [BEq F] : IsFormallyReal F ↔ ¬ (∃ n : ℕ, ∃ f : Fin n → F, sum_of_squares f = -1) := sorry

-- **TASK 3:** Prove the above claim.

/- ## Positive cones -/

section Positive_cones

-- We define positive cones and show how maximal positive cones induce orderings.


/- ## Artin-Schreier theory -/

/- We show that formally real fields admit an ordering, not unique in general.

In particular, **a field `F` is formally real if and only if it admits an ordering.** -/