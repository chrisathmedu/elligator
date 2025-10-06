import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
import Elligator.Elligator1.Sets
import Elligator.Elligator1.sProperties
import Elligator.Elligator1.cProperties
import Elligator.Elligator1.uProperties
import Elligator.Elligator1.vProperties
import Elligator.Elligator1.XProperties
import Elligator.Elligator1.YProperties

namespace Elligator.Elligator1

section xProperties

variable {F : Type*} [Field F] [Fintype F]

lemma x_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let x_of_t := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  x_of_t ≠ (0 : F) := by
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    change (c_of_s - 1) * s * X_of_t * (1 + X_of_t) / Y_of_t ≠ 0
    apply div_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · intro h1
            have h1_1 : c_of_s = 1 := by
              rw [← add_left_inj 1] at h1
              rw [zero_add] at h1
              have h1_1_1 : (1 : F) - (1 : F) = 0 := by ring
              rw [add_comm] at h1
              rw [← add_sub_assoc] at h1
              rw [add_comm 1 c_of_s] at h1
              rw [add_sub_assoc] at h1
              rw [h1_1_1, add_zero] at h1
              exact h1
            have h1_2 : c_of_s ≠ 1 := c_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
            contradiction
          · apply s_h1
        · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
      · apply one_add_X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
    · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t

lemma x_comparison
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let t1 := t
  let t2 := -t1
  let x1 := x ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x2 := x ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  x2 = x1 := by
    intro t1 t2 x1 x2
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X1 := X ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let Y1 := Y ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let Y2 := Y ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have X_pow_three_ne_zero : X1^3 ≠ 0 := by
      apply pow_ne_zero 3 (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩)
    calc
      x2 = (c_of_s - 1) * s * X2 * (1 + X2) / Y2 := by
        change (c_of_s - 1) * s * X2 * (1 + X2) / Y2 = (c_of_s - 1) * s * X2 * (1 + X2) / Y2
        rfl
      _ = (c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) / (Y1 / X1^3) := by
        unfold X2
        rw [X_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
        unfold Y2
        rw [Y_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
        change (c_of_s - 1) * s * (1 / X1) * (1 + 1 / X1) / (Y1 / X1^3) = (c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) / (Y1 / X1 ^ 3)
        ring_nf
      _ = (c_of_s - 1) * s * X1 * (1 + X1) / Y1 := by
        have h2_12_1 : X1^3 / X1^3 = 1 := by
          apply div_self X_pow_three_ne_zero
        rw [← mul_one ((c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) / (Y1 / X1 ^ 3))]
        nth_rw 5 [← h2_12_1]
        rw [← mul_div_mul_comm]
        have h2_12_2 : (c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) * X1 ^ 3 = (c_of_s - 1) * s * X1 * (1 + X1) := by
          calc
            (c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) * X1 ^ 3 = (c_of_s - 1) * s * X1^3 / X1 * (1 + 1 / X1) := by
              repeat rw [mul_assoc]
              rw [mul_comm (1 + 1 / X1) (X1^3)]
              rw [← mul_assoc]
              rw [← mul_assoc, mul_one, div_mul_eq_mul_div]
              ring_nf
            _ = (c_of_s - 1) * s * X1^2 * (1 + 1 / X1) := by
              have h2_12_2_1 : X1^3 = X1^2 * X1 := by ring_nf
              rw [h2_12_2_1, mul_div_assoc, mul_div_assoc]
              rw [div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩)]
              rw [mul_one]
            _ = (c_of_s - 1) * s * X1 * (1 + X1) := by
              have h2_12_2_1 : X1^2 * (1 + 1 / X1) = X1 * (1 + X1) := by
                rw [pow_two, mul_assoc, mul_add, ← mul_div_assoc]
                rw [mul_one]
                rw [div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩)]
                nth_rw 1 [add_comm]
              rw [mul_assoc ((c_of_s - 1) * s), h2_12_2_1]
              repeat rw [← mul_assoc]
        have h2_12_3 : (Y1 / X1 ^ 3 * X1 ^ 3) = Y1 := by
          rw [mul_comm, ← mul_div_assoc, mul_comm]
          rw [mul_div_assoc, div_self X_pow_three_ne_zero]
          simp
        rw [h2_12_2, h2_12_3]
      _ = x1 := by
        unfold x1
        simp
        rfl

