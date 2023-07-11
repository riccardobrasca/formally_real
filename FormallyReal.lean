import Mathlib.NumberTheory.Cyclotomic.Basic

open BigOperators

/- Sums of squares and definition of a formally real semiring -/

-- def sum_of_squares {A : Type _} [Semiring A] : List A → A
--   | [] => 0
--   | (a :: l) => (a * a) + (sum_of_squares l)

def sum_of_squares {A : Type _} [Semiring A] : List A → A :=
  fun L =>  (L.map (·^2)).sum

#check [1,-2,3]
#check sum_of_squares [1, -2, 3]

#eval sum_of_squares [1, -2, 3]
#eval sum_of_squares [1, 2, 3]

example : sum_of_squares [1, 2, 3] = 14 := rfl

#eval sum_of_squares ([] : List ℕ)

-- structure Formally_real {A : Ring}

@[mk_iff]
class IsFormallyReal (A : Type _) [Semiring A] : Prop where
  is_formally_real : ∀ L : List A, sum_of_squares L = 0 → (∀ l ∈ L, l = 0)

example {A : Type _} [Semiring A] [IsFormallyReal A] {I : Type _} {S : Finset I} {f : I → A} (h : ∑ i in S, (f i) ^ 2 = 0) {i : I} (hi : i ∈ S) : f i = 0 := by
  have := IsFormallyReal.is_formally_real (A := A) (S.toList.map f)
  simp [sum_of_squares] at this
  exact this h i hi

example {A : Type _} [Semiring A] [IsFormallyReal A] {n : ℕ} {f : Fin n → A} (h : ∑ i, (f i) ^ 2 = 0) {i : Fin n} : f i = 0 := by
  sorry

lemma sum_of_squares_head_tail [Semiring A] : (head: A) → (tail: List A) → sum_of_squares (head :: tail) = (sum_of_squares ([head])) + (sum_of_squares tail) := by
  intro head tail
  simp [sum_of_squares]

example {F : Type _} [Semiring A] (nt: (1 : A) ≠ (0 : A)) : IsFormallyReal A → ¬ (∃ L : List A, 1 + sum_of_squares L = 0) := by
  intro h ⟨l, hL⟩
  have h' := h.is_formally_real (1 :: l)
  have h'' := sum_of_squares_head_tail 1 l
  rw [h''] at h'
  simp [sum_of_squares] at h'
  have h''' := h' hL
  have := And.left h'''
  contradiction

/- Alternate characterisation of formally real semifields -/

example {F : Type _} [h : Semifield F] : IsFormallyReal F ↔ ¬ (∃ L : List F, 1 + sum_of_squares L = 0) := by
  constructor
  · intro h1 ⟨ L, hL ⟩
    let L' := 1 :: L
    have h' : sum_of_squares L' = 1 + sum_of_squares L := by
      simp [sum_of_squares]
    rw [← h'] at hL
    have := IsFormallyReal.is_formally_real L' hL 1 (by simp)
    simp at this
  · intro h1
    push_neg at h1
    constructor
    intro L'
    intro hL' i hi
    by_contra h''
    let L'' := L'.map (·/i)
    have : sum_of_squares L'' = (sum_of_squares L') / (i^2) := by
      simp [sum_of_squares]
      simp [div_eq_mul_inv]
      rw [← List.sum_map_mul_right]
      simp [Function.comp]
      congr
      ext
      field_simp
    have : sum_of_squares L'' = 0 := by
      simp [this, hL']
    have : i/i ∈ L'' := by

