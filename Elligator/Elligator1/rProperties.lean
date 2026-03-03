import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
import Elligator.Elligator1.Sets
import Elligator.Elligator1.sProperties
import Elligator.Elligator1.cProperties

namespace Elligator.Elligator1

section rProperties

variable {F : Type*} [Field F] [Fintype F]

lemma r_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  r_of_s ≠ 0 := by
    change (2 / s^2) + 1 / (2 / s^2) ≠ 0
    intro h
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have h1 : c_of_s  = (-1 : F) / c_of_s := by
      change c_of_s + 1 / c_of_s = 0 at h
      rw [← add_right_inj (-1 / c_of_s)] at h
      rw [add_comm] at h
      rw [add_zero] at h
      have h3 : 1 / c_of_s + -1 / c_of_s = 0 := by
        ring_nf
      nth_rw 1 [← add_zero c_of_s]
      rw [← h3]
      rw [← add_assoc]
      exact h
    have h2 : c_of_s^2 = -1 := by
      calc
        c_of_s^2 = -1 / c_of_s * c_of_s := by
          rw [pow_two]
          nth_rw 1 [h1]
        _ = -1 := by
          nth_rw 1 [← neg_one_mul 1]
          ring
          rw [mul_inv_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)]
    have h3 : IsSquare (-1 : F) := by
      rw [← h2]
      rw [pow_two]
      apply IsSquare.mul_self c_of_s
    have h4 : q % 4 ≠ 3 := by
      rw [FiniteField.isSquare_neg_one_iff] at h3
      rw [field_cardinality] at h3
      exact h3
    contradiction

lemma four_add_r_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  4 + r_of_s ≠ 0 := by
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    change 4 + (c_of_s + 1 / c_of_s) ≠ 0
    intro h
    have h1 : IsSquare (3 : F) := by
      rw [← add_assoc] at h
      rw [← add_right_inj (-(4 + c_of_s))] at h
      ring_nf at h
      rw [← mul_left_inj' (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)] at h
      unfold c_of_s at h
      rw [inv_mul_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)] at h
      rw [sub_mul] at h
      change 1 = (-4 * c_of_s - c_of_s * c_of_s) at h
      have h1_1 : (0 : F) = 4 - 4 := by norm_num
      have h1_2 : -4 * c_of_s - c_of_s * c_of_s = -(c_of_s + 2)^2 + 4 := by ring_nf
      rw [h1_2, ← add_right_inj (-4)] at h
      rw [← mul_left_inj' (FiniteFieldBasic.neg_one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h
      simp at h
      norm_num at h
      unfold IsSquare
      rw [pow_two] at h
      use (c_of_s + 2)
      exact h
    have h2 : ¬IsSquare (3 : F) := by
      exact FiniteFieldBasic.three_nonsquare q field_cardinality q_prime_power q_mod_4_congruent_3
    contradiction

lemma r_h1
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  (r_of_s^2 - 2) = c_of_s^2 + 1 / c_of_s^2 := by
    intro r_of_s c_of_s
    calc
      r_of_s^2 - 2 = (c_of_s + 1 / c_of_s)^2 - 2 := by
        change (c_of_s + 1 / c_of_s)^2 - 2 = (c_of_s + 1 / c_of_s)^2 - 2
        rfl
      _ = c_of_s^2 + 2 * (c_of_s * (1 / c_of_s)) + (1 / c_of_s)^2 - 2 := by
        rw [add_pow_two]
        rw [mul_assoc 2 c_of_s (1 / c_of_s)]
      _ = c_of_s^2 + 2 + 1 / c_of_s^2 - 2 := by
        ring
        rw [mul_inv_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)]
        ring
      _ = c_of_s^2 + 1 / c_of_s^2 := by
        ring_nf
