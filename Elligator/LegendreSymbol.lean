import Mathlib
import Elligator.FiniteFieldBasic

namespace LegendreSymbol

variable {F : Type*} [Field F] [Fintype F]

/-- χ(a) is the quadratic character of a in the finite field F with q elements, where q is a prime congruent to 3 modulo 4.

This function was added, since Mathlib.NumberTheory.LegendreSymbol.Basic is restricted to ℤ.

Paper definition at chapter 3.1.
-/
noncomputable def χ
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F := a^((Fintype.card F - 1) / 2)

lemma χ_a_zero_eq_zero
  (a : F)
  (a_eq_zero : a = 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = 0 := by
    change a^((Fintype.card F -1)/2) = 0
    rw [field_cardinality]
    rw [a_eq_zero]
    apply zero_pow (FiniteFieldBasic.q_sub_one_over_two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)

lemma χ_a_ne_zero
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a ≠ 0 := by
    change a^((Fintype.card F -1)/2) ≠ 0
    rw [field_cardinality]
    apply pow_ne_zero ((q - 1) / 2) at a_nonzero
    exact a_nonzero

lemma neg_χ_a_ne_χ_a
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a ≠ -χ_of_a := by
    let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
    change a^((Fintype.card F -1)/2) ≠ -a^((Fintype.card F -1)/2)
    rw [field_cardinality]
    intro h
    rw [← add_right_inj (a ^ ((q - 1) / 2))] at h
    ring_nf at h
    rw [← field_cardinality] at h
    change χ_of_a * 2 = 0 at h
    apply mul_ne_zero at h
    · exact h
    · exact χ_a_ne_zero a a_nonzero q field_cardinality q_prime_power q_mod_4_congruent_3
    · exact FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3

lemma χ_a_eq_one
  (a : F)
  (a_nonzero : a ≠ 0)
  (a_square : IsSquare a)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = 1 := by
    change a^((Fintype.card F - 1)/2) = 1
    have h1 : ∃ r, a = r * r := by apply IsSquare.exists_mul_self a a_square
    rcases h1 with ⟨r, h1_1⟩
    rw [h1_1, ← pow_two]
    ring_nf
    have h2 : (Fintype.card F - 1) / 2 * 2 = Fintype.card F - 1 := by
      apply Nat.div_two_mul_two_of_even (FiniteFieldBasic.q_sub_one_even q field_cardinality q_prime_power q_mod_4_congruent_3)
    rw [h2]
    have h3 : r ≠ 0 := by
      intro h3_1
      rw [h3_1, mul_zero] at h1_1
      contradiction
    apply FiniteField.pow_card_sub_one_eq_one r h3

lemma a_IsSquare
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (χ_a_eq_one : χ a q field_cardinality q_prime_power q_mod_4_congruent_3 = 1)
  :
  IsSquare a := by
    let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold χ at χ_a_eq_one
    unfold IsSquare
    let b := a^((Fintype.card F + 1) / 4 )
    use b
    unfold b
    rw [← pow_two, ← pow_mul, add_comm]
    rw [FiniteFieldBasic.one_add_card_over_four_mul_two_eq_one_add_card_over_two q field_cardinality q_mod_4_congruent_3]
    have h : (1 + Fintype.card F) / 2 = (Fintype.card F - 1 + 2) / 2 := by
      omega
    rw [h]
    rw [Nat.add_div_of_dvd_right (FiniteFieldBasic.q_sub_one_dvd_two q field_cardinality q_prime_power q_mod_4_congruent_3) , pow_add]
    simp
    change a = χ_of_a * a
    rw [← mul_left_inj' a_nonzero] at χ_a_eq_one
    simp at χ_a_eq_one
    symm
    trivial

lemma χ_a_eq_one_iff_a_square
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = 1 ↔ IsSquare a := by
    intro χ_of_a
    constructor
    · intro χ_a_eq_one
      exact a_IsSquare a a_nonzero q field_cardinality q_prime_power q_mod_4_congruent_3 χ_a_eq_one
    · intro a_square
      exact χ_a_eq_one a a_nonzero a_square q field_cardinality q_prime_power q_mod_4_congruent_3

lemma a_pow_q_add_one_over_two_eq_χ_of_a_mul_a
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  a ^ ((q + 1) / 2) = χ_of_a * a := by
    intro χ_of_a
    unfold χ_of_a χ
    rw [field_cardinality]
    rw [FiniteFieldBasic.card_sub_one_over_four_mul_two_eq_one_add_card_over_two]
    nth_rw 3 [← pow_one a]
    rw [← pow_add]
    have h'' : (q + 1) / 2 - 1 + 1 = (q + 1) / 2 := by omega
    rw [h'']

lemma χ_a_mul_a_eq_a
  (a : F)
  (a_nonzero : a ≠ 0)
  (a_square : IsSquare a)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a * a = a := by
    have h := (χ_a_eq_one_iff_a_square a a_nonzero q field_cardinality q_prime_power q_mod_4_congruent_3).mpr
    rw [h a_square]
    intro χ_of_a
    unfold χ_of_a
    simp

lemma a_pow_q_add_one_over_two_eq_a
  (a : F)
  (a_nonzero : a ≠ 0)
  (a_square : IsSquare a)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  a ^ ((q + 1) / 2) = a := by
    rw [a_pow_q_add_one_over_two_eq_χ_of_a_mul_a a q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [χ_a_mul_a_eq_a a a_nonzero a_square q field_cardinality q_prime_power q_mod_4_congruent_3]

lemma χ_of_a_pow_n_eq_χ_a
  (a : F)
  (n : {n : ℕ | Odd n})
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a^(n.val) = χ_of_a := by
    sorry

lemma χ_of_a_even_pow_n_eq_one
  (a : F)
  (a_nonzero : a ≠ 0)
  (n : {n : ℕ | Even n})
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a^(n.val) = 1 := by
    sorry

lemma χ_of_a_pow_two_eq_one
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ (a^2) q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = 1 := by
    intro χ_of_a
    unfold χ_of_a χ
    rw [← pow_mul]
    have h : 2 * ((Fintype.card F - 1) / 2) =  Fintype.card F - 1 := by omega
    rw [h]
    -- TODO search proof
    sorry

lemma χ_of_a_eq_neg_one
  (a : F)
  (a_nonzero : a ≠ 0)
  (a_nonsquare : ¬IsSquare a)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = -1 := by sorry

lemma χ_of_neg_one_eq_neg_one
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_neg_one := χ (-1 : F) q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_neg_one = -1 := by
    apply χ_of_a_eq_neg_one
    · apply FiniteFieldBasic.neg_one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    · apply FiniteFieldBasic.neg_one_non_square q field_cardinality q_prime_power q_mod_4_congruent_3

lemma χ_of_χ_of_a_eq_χ_of_a
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_χ_of_a := χ (χ_of_a) q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_χ_of_a = χ_of_a := sorry

lemma χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b
  (a b : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_b := χ b q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_a_mul_b := χ (a * b) q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a_mul_b = χ_of_a * χ_of_b := sorry

lemma χ_of_one_over_a_eq_χ_a
  (a : F)
  (a_non_zero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_1_over_a := χ (1 / a) q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_1_over_a = χ_of_a := sorry

lemma χ_of_one_over_a_eq_one_over_χ_a
  (a : F)
  (a_non_zero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_1_over_a := χ (1 / a) q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_1_over_a = 1 / χ_of_a := sorry

lemma one_over_χ_of_a_eq_χ_a
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  1 / χ_of_a  = χ_of_a := by
    sorry

lemma square_of_a
  (a : {n : F // IsSquare n})
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  a.val^((q + 1) / 2) = a.val := by
    sorry

lemma χ_of_a_eq_χ_a_mul_b_pow_two
  (a : F)
  {b : F}
  (b_nonzero : b ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_a_mul_b_pow_two := χ (a * b^2) q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = χ_of_a_mul_b_pow_two := by
  -- Introduced in paper theory theorem 3.A proof
    sorry

-- TODO used so?
lemma b_eq_χ_of_b_mul_principal_sqrt_a
  (a : {a : F // IsSquare a})
  {b : F}
  (b_h1 : b^2 = a.val)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_b := χ b q field_cardinality q_prime_power q_mod_4_congruent_3
  b = χ_of_b * a.val^((q + 1) / 4) := by
    sorry

lemma b_pow_q_add_one_over_four_eq_χ_of_a_mul_a
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  (a^2)^((q + 1) / 4) = χ_of_a * a := by
    intro χ_of_a
    rw [← pow_mul, mul_comm, ← field_cardinality, add_comm]
    rw [FiniteFieldBasic.one_add_card_over_four_mul_two_eq_one_add_card_over_two q field_cardinality q_mod_4_congruent_3]
    rw [← a_pow_q_add_one_over_two_eq_χ_of_a_mul_a a q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [← field_cardinality, add_comm]

lemma χ_a_mul_a_IsSquare
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  IsSquare (χ_of_a * a) := by
    intro χ_of_a
    have h1 : χ_of_a * a ≠ 0 := by
      apply mul_ne_zero
      · exact χ_a_ne_zero a a_nonzero q field_cardinality q_prime_power q_mod_4_congruent_3
      · exact a_nonzero
    apply (χ_a_eq_one_iff_a_square (χ_of_a * a) h1 q field_cardinality q_prime_power q_mod_4_congruent_3).mp
    rw [χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b χ_of_a a q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [χ_of_χ_of_a_eq_χ_of_a a q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [← pow_two]
    rw [χ_of_a_even_pow_n_eq_one a a_nonzero ⟨2, even_two⟩ ]

lemma χ_values
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_a = 0 ∨ χ_of_a = -1 ∨ χ_of_a = 1 := by
    intro χ_of_a
    by_cases h : a = 0
    · left
      exact χ_a_zero_eq_zero a h q field_cardinality q_prime_power q_mod_4_congruent_3
    · rw [← ne_eq] at h
      by_cases h' : IsSquare a
      · right
        right
        apply χ_a_eq_one a h h' q field_cardinality q_prime_power q_mod_4_congruent_3
      · right
        left
        apply χ_of_a_eq_neg_one a h h' q field_cardinality q_prime_power q_mod_4_congruent_3
