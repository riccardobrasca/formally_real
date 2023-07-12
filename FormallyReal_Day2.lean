/- # Formally real semirings -/

import Mathlib.NumberTheory.Cyclotomic.Basic
-- import Mathlib.Tactic

open BigOperators

/- We define formally real semirings. To do so, we define what it means to be a sum of squares in a semiring. -/

def sum_of_squares {A : Type _} [Semiring A] {n : ℕ} : (Fin n → A) → A :=
  fun f => ∑ i , (f i) ^ 2

-- notation "sum_sq" => sum_of_squares

@[mk_iff]
class IsFormallyReal (A : Type _) [Semiring A] : Prop where
  is_formally_real : ∀ (n : ℕ), ∀ (f : Fin n → A), (sum_of_squares f = 0) → (∀ i, f i = 0)

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

def sum_sq_neq_minus_one {A : Type _} [Semiring A] [ntA : Nontrivial A] : IsFormallyReal A → (∀ n : ℕ, ∀ f : Fin n → A, 1 + sum_of_squares f ≠ 0) := by
  intro H n f
  by_contra hf
  let S := 1 + sum_of_squares f
  have hS1 : S = 1 + sum_of_squares f := by rfl
  have hS2 : is_sum_of_squares S := by
    apply sum_sq_add_sum_sq_is_sum_sq 1 (sum_of_squares f)
    use 1
    use fun i => 1
    simp [sum_of_squares]
    use n, f
  have hS3 : S = 0 := sorry
  rcases hS2 with ⟨ m, g, hg ⟩
  rw [hS3] at hg
  have g_trivial : ∀ i, g i = 0 := by 
    apply IsFormallyReal.is_formally_real
    exact hg
  
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