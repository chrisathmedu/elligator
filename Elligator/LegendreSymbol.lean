import Elligator.FiniteFieldBasic
import Elligator.Common

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
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F := a^((Fintype.card F - 1) / 2)

lemma χ_a_zero_eq_zero
  (a : F)
  (a_eq_zero : a = 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a = 0 := by
    change a^((Fintype.card F -1)/2) = 0
    rw [field_cardinality]
    rw [a_eq_zero]
    apply zero_pow (FiniteFieldBasic.q_sub_one_over_two_ne_zero q field_cardinality q_prime q_mod_4_congruent_3)

lemma χ_a_ne_zero
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
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
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a ≠ -χ_of_a := by
    let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
    change a^((Fintype.card F -1)/2) ≠ -a^((Fintype.card F -1)/2)
    rw [field_cardinality]
    intro h
    rw [← add_right_inj (a ^ ((q - 1) / 2))] at h
    ring_nf at h
    rw [← field_cardinality] at h
    change χ_of_a * 2 = 0 at h
    apply mul_ne_zero at h
    · exact h
    · exact χ_a_ne_zero a a_nonzero q field_cardinality q_prime q_mod_4_congruent_3
    · exact FiniteFieldBasic.two_ne_zero q field_cardinality q_prime q_mod_4_congruent_3

lemma χ_a_eq_one
  (a : F)
  (a_nonzero : a ≠ 0)
  (a_square : IsSquare a)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a = 1 := by
    change a^((Fintype.card F - 1)/2) = 1
    have h1 : ∃ r, a = r * r := by apply IsSquare.exists_mul_self a a_square
    rcases h1 with ⟨r, h1_1⟩
    rw [h1_1, ← pow_two]
    ring_nf
    have h2 : (Fintype.card F - 1) / 2 * 2 = Fintype.card F - 1 := by
      apply Nat.div_two_mul_two_of_even (FiniteFieldBasic.q_sub_one_even q field_cardinality q_prime q_mod_4_congruent_3)
    rw [h2]
    have h3 : r ≠ 0 := by 
      intro h3_1
      rw [h3_1, mul_zero] at h1_1
      contradiction
    apply FiniteField.pow_card_sub_one_eq_one r h3

lemma χ_of_a_pow_n_eq_χ_a
  (a : F)
  (n : {n : ℕ | Odd n})
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a^(n.val) = χ_of_a := by 
    sorry

lemma χ_of_a_eq_neg_one
  (a : F)
  (a_nonzero : a ≠ 0)
  (a_nonsquare : ¬IsSquare a)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a = -1 := by sorry

lemma χ_of_neg_one_eq_neg_one 
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_neg_one := χ (-1 : F) q field_cardinality q_prime q_mod_4_congruent_3 
  χ_of_neg_one = -1 := by
    apply χ_of_a_eq_neg_one
    · apply FiniteFieldBasic.neg_one_ne_zero q field_cardinality q_prime q_mod_4_congruent_3
    · apply FiniteFieldBasic.neg_one_non_square q field_cardinality q_prime q_mod_4_congruent_3

lemma χ_of_χ_of_a_eq_χ_of_a
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_χ_of_a := χ (χ_of_a) q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_χ_of_a = χ_of_a := sorry

lemma χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b
  (a b : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_b := χ b q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_a_mul_b := χ (a * b) q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a_mul_b = χ_of_a * χ_of_b := sorry

lemma χ_of_one_over_a_eq_χ_a
  (a : F)
  (a_non_zero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_1_over_a := χ (1 / a) q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_1_over_a = χ_of_a := sorry

lemma χ_of_one_over_a_eq_one_over_χ_a
  (a : F)
  (a_non_zero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_1_over_a := χ (1 / a) q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_1_over_a = 1 / χ_of_a := sorry

lemma one_over_χ_of_a_eq_χ_a
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  1 / χ_of_a  = χ_of_a := by 
    sorry

lemma square_of_a
  (a : {n : F // IsSquare n})
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  a.val^((q + 1) / 2) = a.val := by 
    sorry

