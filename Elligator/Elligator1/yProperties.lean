import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
import Elligator.Elligator1.Sets
import Elligator.Elligator1.sProperties
import Elligator.Elligator1.cProperties
import Elligator.Elligator1.dProperties
import Elligator.Elligator1.uProperties
import Elligator.Elligator1.vProperties
import Elligator.Elligator1.XProperties
import Elligator.Elligator1.YProperties
import Elligator.Elligator1.xProperties

namespace Elligator.Elligator1

section yProperties

variable {F : Type*} [Field F] [Fintype F]

-- Chapter 3.2 Theorem 1
theorem Y_pow_two_eq_X_pow_five_add_r_pow_two_sub_2_mul_X_pow_three_add_X
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  Y_of_t ^2 = X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t := by
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v_of_t := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    intro r_of_s X_of_t Y_of_t
    have h1 : X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t = χ_of_v_of_t * v_of_t := by
      calc
      X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t = χ_of_v_of_t * (u_of_t^5 + (r_of_s^2 -2 ) * u_of_t^3 + u_of_t) := by
        change (χ_of_v_of_t * u_of_t) ^ 5 + (r_of_s ^ 2 - 2) * (χ_of_v_of_t * u_of_t) ^ 3 + (χ_of_v_of_t * u_of_t) = χ_of_v_of_t * (u_of_t^5 + (r_of_s^2 -2 ) * u_of_t^3 + u_of_t)
        rw [mul_pow (χ_of_v_of_t) (u_of_t) 5]
        rw [mul_pow (χ_of_v_of_t) (u_of_t) 3]
        have h1_1 : Odd 5 := by
          apply Nat.odd_iff.2
          norm_num
        have h1_2 : Odd 3 := by
          apply Nat.odd_iff.2
          norm_num
        rw [LegendreSymbol.χ_of_a_pow_n_eq_χ_a v_of_t ⟨5, h1_1⟩ q field_cardinality q_prime_power q_mod_4_congruent_3]
        rw [LegendreSymbol.χ_of_a_pow_n_eq_χ_a v_of_t ⟨3, h1_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3]
        change χ_of_v_of_t * u_of_t^5 + (r_of_s ^ 2 - 2) * (χ_of_v_of_t * u_of_t^3) + (χ_of_v_of_t * u_of_t) = χ_of_v_of_t * (u_of_t^5 + (r_of_s^2 -2 ) * u_of_t^3 + u_of_t)
        ring_nf
      _ = χ_of_v_of_t * v_of_t := by
        change χ_of_v_of_t * v_of_t = χ_of_v_of_t * v_of_t
        rfl
    have h2 : IsSquare (χ_of_v_of_t * v_of_t) := by
      -- TODO unsure why this implies a square given the paper information
      -- v itself does not appear to be a square
      sorry
    have h3 : (χ_of_v_of_t * v_of_t)^((q + 1) / 2) = χ_of_v_of_t * v_of_t := by
      apply LegendreSymbol.square_of_a ⟨(χ_of_v_of_t * v_of_t), h2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_sum := LegendreSymbol.χ (u_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3
    have h4 : Y_of_t^2 = χ_of_v_of_t * v_of_t := by
      calc
        Y_of_t^2 = (χ_of_v_of_t * v_of_t)^((q + 1) / 2) * χ_of_v_of_t^2 * χ_of_sum^2 := by
          change ((χ_of_v_of_t * v_of_t)^((q + 1) / 4) * χ_of_v_of_t * χ_of_sum)^2 = (χ_of_v_of_t * v_of_t)^((q + 1) / 2) * χ_of_v_of_t^2 * χ_of_sum^2
          ring_nf
          have h4_1 : ((1 + q) / 4 * 2) = (1 + q) / 2 := by
            -- TODO problems with Nat div
            sorry
          rw [h4_1]
        _ = (χ_of_v_of_t * v_of_t)^((q + 1) / 2) * 1 := by
          rw [LegendreSymbol.χ_of_a_even_pow_n_eq_one v_of_t (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t) ⟨2, even_two⟩ q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [LegendreSymbol.χ_of_a_even_pow_n_eq_one (u_of_t^2 + 1 / c_of_s^2) (v_h1_third_factor_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t) ⟨2, even_two⟩ q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [mul_one]
        _ = χ_of_v_of_t * v_of_t := by rw [h3, mul_one]
    rw [h1]
    exact h4

lemma y_divisor_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  (r_of_s * X_of_t + (1 + X_of_t)^2) ≠ 0 := by
    let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    intro r_of_s
    intro X_of_t
    intro h
    have h1 : r_of_s * X_of_t = -(1 + X_of_t)^2 := by
      rw [← add_left_inj ((1 + X_of_t)^2)]
      have h1_1 : -((1 + X_of_t)^2) + ((1 + X_of_t)^2) = 0 := by
        rw [neg_add_eq_zero.2]
        ring
      rw [h1_1]
      exact h
    have h2 : (r_of_s^2 + 4 * r_of_s) * X_of_t^2 = X_of_t^4 - 2 * X_of_t^2 + 1 := by
      ring_nf
      repeat rw [pow_two]
      repeat rw [← mul_assoc]
      rw [mul_assoc r_of_s r_of_s X_of_t]
      nth_rw 2 [mul_comm r_of_s X_of_t]
      rw [← mul_assoc]
      rw [h1]
      rw [mul_assoc (-(1 + X_of_t)^2) r_of_s X_of_t]
      rw [h1]
      ring_nf
    have h3 : Y_of_t^2 = -(1 + X_of_t)^2 * X_of_t^2 * (s + 2 / s)^2 := by
      calc
        Y_of_t^2 = X_of_t * (X_of_t^4 + (r_of_s^2 - 2) * X_of_t^2 + 1) := by
          rw [mul_add, mul_one]
          rw [mul_add]
          rw [Y_pow_two_eq_X_pow_five_add_r_pow_two_sub_2_mul_X_pow_three_add_X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
          ring_nf
          change X_of_t - X_of_t ^ 3 * 2 + X_of_t ^ 3 * r_of_s ^ 2 + X_of_t ^ 5 = X_of_t - X_of_t ^ 3 * 2 + X_of_t ^ 3 * r_of_s ^ 2 + X_of_t ^ 5
          rfl
        _ = X_of_t^3 * (2 * r_of_s^2 + 4 * r_of_s) := by
          rw [sub_mul (r_of_s^2) 2 (X_of_t^2)]
          nth_rw 1 [pow_two]
          nth_rw 1 [pow_two]
          rw [← mul_assoc, mul_assoc r_of_s r_of_s X_of_t, mul_comm r_of_s X_of_t]
          rw [← mul_assoc]
          rw [h1, mul_assoc (-(1 + X_of_t)^2) r_of_s X_of_t, h1]
          rw [← neg_one_mul]
          have h3_1 : (-1 : F) * (-1) = 1 := by ring
          nth_rw 1 [mul_comm (-1) ((1 + X_of_t)^2), ← mul_assoc, mul_assoc ((1 + X_of_t)^2) (-1) (-1)]
          rw [h3_1, mul_one]
          have h3_2 : 2 + 2 = 4 := by norm_num
          rw [← pow_add (1 + X_of_t) 2 2]
          rw [h3_2]
          rw [← add_sub_assoc, add_comm (X_of_t^4) ((1 + X_of_t)^4)]
          rw [add_sub_assoc ((1 + X_of_t)^4) (X_of_t^4)]
          rw [add_assoc ((1 + X_of_t)^4) (X_of_t^4 - 2 * X_of_t^2) (1 : F)]
          rw [← h2]
          have h3_3 : -r_of_s * X_of_t = (1 + X_of_t)^2 := by
            rw [← neg_one_mul]
            rw [← mul_right_inj' (FiniteFieldBasic.neg_one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)]
            rw [← mul_assoc, ← mul_assoc, h3_1, one_mul, neg_one_mul]
            exact h1
          rw [← h3_2, pow_add (1 + X_of_t) 2 2, ← h3_3]
          rw [← pow_two]
          ring_nf
        _ = r_of_s * X_of_t * X_of_t^2 * (2 * r_of_s + 4) := by ring_nf
        _ = -(1 + X_of_t)^2 * X_of_t^2 * (s + 2 / s)^2 := by
          rw [← h1]
          change r_of_s * X_of_t * X_of_t ^ 2 * (2 * (c_of_s + 1 / c_of_s) + 4) = r_of_s * X_of_t * X_of_t ^ 2 * (s + 2 / s) ^ 2
          change r_of_s * X_of_t * X_of_t ^ 2 * (2 * (2 / s^2 + 1 / (2 / s^2)) + 4) = r_of_s * X_of_t * X_of_t ^ 2 * (s + 2 / s) ^ 2
          have h3_4 : (2 * (2 / s^2 + 1 / (2 / s^2)) + 4) = (s + 2 / s)^2 := by
            ring_nf
            rw [inv_inv, mul_inv_cancel₀ s_h1, one_mul]
            rw [mul_assoc _ 2⁻¹ 2]
            rw [inv_mul_cancel₀ (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)]
            ring_nf
          rw [h3_4]
    have h4 : IsSquare (-1 : F) := by
      have h4_1 : Y_of_t^2 / ((1 + X_of_t) * X_of_t * (s + 2 / s))^2 = -1 := by
        rw [← neg_one_mul] at h3
        rw [mul_assoc (-1) ((1 + X_of_t)^2) (X_of_t^2)] at h3
        rw [← mul_pow (1 + X_of_t) (X_of_t) 2] at h3
        rw [mul_assoc (-1) (((1 + X_of_t) * X_of_t)^2) _] at h3
        rw [← mul_pow (((1 + X_of_t) * X_of_t))] at h3
        have h4_1_1 : ((1 + X_of_t) * X_of_t * (s + 2 / s))^2 ≠ 0 := by
          apply pow_ne_zero 2
          apply mul_ne_zero
          · apply mul_ne_zero
            · apply one_add_X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
            · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
          · intro h4_1_2
            rw [← mul_right_inj' s_h1] at h4_1_2
            ring_nf at h4_1_2
            rw [mul_inv_cancel₀ s_h1, one_mul] at h4_1_2
            rw [add_comm] at h4_1_2
            have h4_1_2_1 : s^2 + 2 = 0 := by
              exact h4_1_2
            have h4_1_2_2 : (s^2 - 2) * (s^2 + 2) = 0 := by
              rw [h4_1_2_1, mul_zero]
            contradiction
        rw [← div_left_inj' h4_1_1] at h3
        rw [mul_div_assoc] at h3
        rw [div_self h4_1_1, mul_one] at h3
        exact h3
      have h4_2 : (Y_of_t / ((1 + X_of_t) * X_of_t * (s + 2 / s)))^2 = -1 := by
        rw [← div_pow] at h4_1
        exact h4_1
      rw [← h4_2]
      rw [pow_two]
      apply IsSquare.mul_self
    have h5 : q % 4 ≠ 3 := by
      rw [FiniteField.isSquare_neg_one_iff] at h4
      rw [field_cardinality] at h4
      exact h4
    contradiction

lemma y_add_one_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  y_of_t + 1 ≠ (0 : F) := by
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    intro y_of_t
    intro h
    have h1 : y_of_t = -1 := by
      rw [← add_left_inj (-1)] at h
      have h1_1 : (1 : F) + (-1 : F) = 0 := by ring
      rw [add_assoc] at h
      rw [h1_1] at h
      rw [add_zero, zero_add] at h
      exact h
    have h2 : (r_of_s * X_of_t - (1 + X_of_t)^2) / (r_of_s * X_of_t + (1 + X_of_t)^2) = -1 := by
      change y_of_t = -1
      exact h1
    have h3 : r_of_s * X_of_t - (1 + X_of_t)^2 = -(r_of_s * X_of_t + (1 + X_of_t)^2) := by
      have h3_1 : (r_of_s * X_of_t + (1 + X_of_t)^2) ≠ 0 := y_divisor_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
      rw [← div_left_inj' h3_1]
      rw [← neg_one_mul]
      rw [mul_div_assoc]
      rw [div_self h3_1]
      rw [mul_one]
      exact h2
    have h4 : r_of_s * X_of_t = 0 := by
      rw [← add_left_inj (r_of_s * X_of_t + (1 + X_of_t) ^ 2)] at h3
      ring_nf at h3
      rw [← div_left_inj' (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h3
      rw [mul_div_assoc] at h3
      rw [div_self (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h3
      ring_nf at h3
      exact h3
    have h5 : r_of_s * X_of_t ≠ 0 := by
      apply mul_ne_zero
      · apply r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
    contradiction

-- Chapter 3.2 Theorem 1
theorem u_mul_v_mul_X_mul_Y_mul_x_mul_y_add_one_ne_zero
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
  let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x_of_t := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  u_of_t * v_of_t * X_of_t  * Y_of_t * x_of_t * (y_of_t + 1) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · apply mul_ne_zero
            · apply u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 t
            · apply v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
          · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
        · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
      · apply x_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
    · apply y_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t

-- Chapter 3.2 Theorem 1
theorem x_pow_two_add_y_pow_two_eq_one_add_d_mul_x_pow_two_mul_y_pow_two
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let x_of_t := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  x_of_t^2 + y_of_t^2 = 1 + d_of_s * x_of_t^2 * y_of_t^2 := by
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    intro x_of_t y_of_t d_of_s
    have h1 : (c_of_s - 1)^2 * s^2 = 2 * (r_of_s - 2):=
      calc
        (c_of_s - 1)^2 * s^2 = (c_of_s - 1)^2 * (2 / c_of_s) := by
          have h1_1 : s^2 = 2 / c_of_s := by
            change s^2 = 2 / (2 / s^2)
            ring_nf
            rw [inv_inv]
            rw [mul_assoc]
            rw [inv_mul_cancel₀ (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3), mul_one]
          rw [h1_1]
        _ = 2 * (r_of_s - 2) := by
          rw [sub_pow_two, mul_one, one_pow 2]
          rw [add_mul, sub_mul]
          rw [← mul_div_assoc]
          rw [one_mul]
          rw [mul_comm, pow_two, ← mul_assoc]
          rw [mul_div_assoc, div_self (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3), mul_one]
          nth_rw 4 [← mul_one 2]
          rw [add_comm, ← add_sub_assoc]
          rw [mul_div_assoc, ← mul_add 2 (1 / c_of_s) c_of_s, add_comm]
          change 2 * r_of_s - 2 * c_of_s * (2 / c_of_s) = 2 * (r_of_s - 2)
          ring_nf
          rw [mul_inv_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)]
          ring_nf
    have h2 : Y_of_t^2 * (1 - x_of_t^2) = X_of_t * (r_of_s * X_of_t - (1 + X_of_t)^2)^2 := by
      calc
        Y_of_t^2 * (1 - x_of_t^2) = Y_of_t^2 - (c_of_s - 1)^2 * s^2 * X_of_t^2 * (1 + X_of_t)^2 := by
          change Y_of_t^2 * (1 - (((c_of_s - 1) * s * X_of_t * (1 + X_of_t)) / Y_of_t)^2) = Y_of_t^2 - (c_of_s - 1)^2 * s^2 * X_of_t^2 * (1 + X_of_t)^2
          rw [mul_sub, mul_one]
          have h2_1 : Y_of_t^2 ≠ 0 := by
            rw [pow_two]
            apply mul_ne_zero
            · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
            · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
          rw [div_pow, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self h2_1]
          ring_nf
       _ = X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t - 2 * (r_of_s - 2) * X_of_t^2 * (1 + X_of_t)^2 := by
          rw [h1, Y_pow_two_eq_X_pow_five_add_r_pow_two_sub_2_mul_X_pow_three_add_X  t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
       _ = X_of_t * (r_of_s * X_of_t - (1 + X_of_t)^2)^2 := by
          ring_nf
    have h3 : -d_of_s = (r_of_s + 2) / (r_of_s - 2) := by
      calc
        -d_of_s = (c_of_s + 2 + 1 / c_of_s) / (c_of_s - 2 + 1 / c_of_s) := by
          change -(-(c_of_s + 1)^2 / (c_of_s - 1)^2) = (c_of_s + 2 + 1 / c_of_s) / (c_of_s - 2 + 1 / c_of_s)
          rw [← neg_one_mul]
          nth_rw 2 [← neg_one_mul]
          rw [mul_div_assoc, ← mul_assoc]
          rw [add_pow_two, sub_pow_two]
          have h3_1 : 1 / c_of_s ≠ 0 := by
            rw [← inv_eq_one_div]
            apply inv_ne_zero
            apply c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
          have h3_2 : (1 / c_of_s) / (1 / c_of_s) = 1 := by
            rw [div_self h3_1]
          have h3_3 : (-1 : F) * (-1) = 1 := by ring
          rw [h3_3]
          nth_rw 1 [← h3_2]
          rw [← mul_div_mul_comm]
          rw [mul_add, mul_add, mul_add, mul_sub, pow_two, ← mul_assoc]
          rw [← inv_eq_one_div, inv_mul_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3), one_mul]
          rw [mul_one, ← mul_assoc, mul_comm, ← mul_assoc]
          rw [mul_inv_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3), one_mul]
          ring_nf
        _ = (r_of_s + 2) / (r_of_s - 2) := by
          rw [add_assoc, add_comm 2 (1 / c_of_s), ← add_assoc]
          nth_rw 3 [add_comm]
          rw [← add_sub_assoc]
          nth_rw 3 [add_comm]
          change (r_of_s + 2) / (r_of_s - 2) = (r_of_s + 2) / (r_of_s - 2)
          rfl
    have h4 : -d_of_s * (c_of_s - 1)^2 * s^2 = 2 * (r_of_s + 2) := by
      rw [h3, mul_assoc, h1]
      rw [mul_comm, ← mul_div_assoc, mul_assoc, mul_comm (r_of_s - 2) (r_of_s + 2), ← mul_assoc]
      have h4_1 : r_of_s - 2 ≠ 0 := by
        intro h4_1_1
        have h4_1_2 : (c_of_s - 1) ^ 2 * s ^ 2 = 0 := by
          rw [h4_1_1, mul_zero] at h1
          exact h1
        have h4_1_3 : (c_of_s - 1) ^ 2 * s ^ 2 ≠ 0 := by
          apply mul_ne_zero
          · apply pow_ne_zero 2
            exact c_sub_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
          · apply pow_ne_zero 2
            apply s_h1
        contradiction
      rw [mul_div_assoc, div_self h4_1, mul_one]
    have h5 : Y_of_t^2 * (1 - d_of_s * x_of_t^2) = X_of_t * (r_of_s * X_of_t + (1 + X_of_t)^2)^2 := by
      calc
        Y_of_t^2 * (1 - d_of_s * x_of_t^2) = Y_of_t^2 - d_of_s * (c_of_s - 1)^2 * s^2 * X_of_t^2 * (1 + X_of_t)^2 := by
          change Y_of_t^2 * (1 - d_of_s * (((c_of_s - 1) * s * X_of_t * (1 + X_of_t)) / Y_of_t)^2) = Y_of_t^2 - d_of_s * (c_of_s - 1)^2 * s^2 * X_of_t^2 * (1 + X_of_t)^2
          rw [mul_sub, mul_one]
          have h2_1 : Y_of_t^2 ≠ 0 := by
            rw [pow_two]
            apply mul_ne_zero
            · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
            · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
          rw [div_pow, ← mul_assoc, mul_comm (Y_of_t^2), ← mul_div_assoc, mul_assoc]
          rw [mul_comm (Y_of_t ^ 2) (((c_of_s - 1) * s * X_of_t * (1 + X_of_t)) ^ 2)]
          rw [← mul_assoc, mul_div_assoc, div_self h2_1]
          ring_nf
       _ = X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t + 2 * (r_of_s + 2) * X_of_t^2 * (1 + X_of_t)^2 := by
          rw [← neg_add_eq_sub, ← neg_one_mul]
          rw [← mul_assoc (-1 : F)]
          rw [← mul_assoc (-1 : F)]
          rw [← mul_assoc (-1 : F)]
          rw [← mul_assoc (-1 : F)]
          rw [neg_one_mul]
          rw [add_comm]
          rw [h4]
          rw [Y_pow_two_eq_X_pow_five_add_r_pow_two_sub_2_mul_X_pow_three_add_X   t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
       _ = X_of_t * (r_of_s * X_of_t + (1 + X_of_t)^2)^2 := by
          ring_nf
    have h6 : (1 - d_of_s * x_of_t^2) ≠ 0 := by
      intro h6_1
      have h6_2 : IsSquare d_of_s := by
        rw [← add_right_inj (d_of_s * x_of_t^2), add_comm] at h6_1
        have h6_2_1 : 1 - d_of_s * x_of_t ^ 2 + d_of_s * x_of_t ^ 2 = 1 := by ring
        rw [add_zero, h6_2_1] at h6_1
        have h6_2_2 : x_of_t^2 ≠ 0 := by
          rw [pow_two]
          apply mul_ne_zero
          · apply x_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
          · apply x_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
        rw [← div_left_inj' h6_2_2] at h6_1
        rw [mul_div_assoc, div_self h6_2_2, mul_one] at h6_1
        rw [← mul_one 1, ← pow_two, ← div_pow _ _ 2] at h6_1
        rw [← h6_1, pow_two]
        apply IsSquare.mul_self
      have h6_3 : ¬IsSquare d_of_s := by exact d_nonsquare s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      contradiction
    have h7 : Y_of_t^2 * (1 - d_of_s * x_of_t^2) ≠ 0 := by
      apply mul_ne_zero
      · rw [pow_two]
        apply mul_ne_zero
        · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
        · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
      · exact h6
    have h8 : (1 - x_of_t^2) / (1 - d_of_s * x_of_t^2) = y_of_t^2 := by
      calc
        (1 - x_of_t^2) / (1 - d_of_s * x_of_t^2) = (r_of_s * X_of_t - (1 + X_of_t)^2)^2 / (r_of_s * X_of_t + (1 + X_of_t)^2)^2 := by
          have h8_1 : Y_of_t^2 / Y_of_t^2 = 1 := by
            have h7_2 : Y_of_t^2 ≠ 0 := by
              rw [pow_two]
              apply mul_ne_zero
              · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
              · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
            rw [div_self h7_2]
          nth_rw 1 [← one_mul (1 - x_of_t ^ 2), ← h8_1]
          rw [mul_div_assoc, ← mul_div_mul_comm]
          rw [h2, h5]
          rw [mul_div_mul_comm X_of_t _ X_of_t _]
          rw [div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
          rw [one_mul]
        _ = y_of_t^2 := by
          rw [← div_pow _ _ 2]
          change y_of_t^2 = y_of_t^2
          rfl
    rw [← mul_right_inj' h6] at h8
    rw [← mul_div_assoc, mul_comm, mul_div_assoc, div_self h6, mul_one] at h8
    rw [sub_mul, one_mul] at h8
    rw [← add_left_inj (x_of_t^2)] at h8
    rw [← add_left_inj (y_of_t^2 * x_of_t^2 * d_of_s)] at h8
    ring_nf at h8
    symm at h8
    rw [mul_assoc (d_of_s) (x_of_t ^ 2) (y_of_t ^ 2), mul_comm (d_of_s) (x_of_t ^ 2 * y_of_t ^ 2)]
    exact h8

-- Used in Theorem 3 Proof B part as implication for point_in_ϕ_over_F_with_prop2_main_case
-- argument.
lemma y_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X_of_t^2 + (2 + r_of_s * (y_of_t - 1) / (y_of_t + 1)) * X_of_t + 1 = 0 := by
    intro y_of_t r_of_s X_of_t
    rw [← mul_left_inj' (y_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
    change (X_of_t ^ 2 + (2 + r_of_s * (y_of_t - 1) / (y_of_t + 1)) * X_of_t + 1) * (y_of_t + 1) = 0 * (y_of_t + 1)
    repeat rw [add_mul]
    rw [zero_mul]
    have h1 : (2 * X_of_t * (y_of_t + 1) + r_of_s * (y_of_t - 1) / (y_of_t + 1) * X_of_t * (y_of_t + 1)) = (2 * (y_of_t + 1) + r_of_s * (y_of_t - 1)) * X_of_t := by
      rw [add_mul _ _ X_of_t] 
      rw [← div_left_inj' (y_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
      change (2 * X_of_t * (y_of_t + 1) + r_of_s * (y_of_t - 1) / (y_of_t + 1) * X_of_t * (y_of_t + 1)) / (y_of_t + 1) = (2 * (y_of_t + 1) * X_of_t + r_of_s * (y_of_t - 1) * X_of_t) / (y_of_t + 1)
      repeat rw [add_div]
      repeat rw [mul_div_assoc, div_self (y_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
      rw [mul_comm (2 * (y_of_t + 1)) X_of_t, ← mul_assoc]
      nth_rw 2 [mul_div_assoc]
      rw [div_self (y_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
      ring_nf
    rw [h1]
    have h2 : (2 * (y_of_t + 1) + r_of_s * (y_of_t - 1)) = (y_of_t * r_of_s - r_of_s + 2 * y_of_t + 2) := by ring_nf
    rw [h2]
    rw [mul_add, add_mul]
    ring_nf
    rw [← add_right_inj (r_of_s * X_of_t - 1 - 2 * X_of_t - X_of_t^2)]
    ring_nf
    rw [mul_comm (X_of_t^2) y_of_t, mul_comm X_of_t y_of_t]
    rw [mul_assoc, mul_assoc]
    nth_rw 4 [← mul_one y_of_t]
    rw [add_assoc, ← mul_add y_of_t]
    rw [add_assoc, ← mul_add y_of_t, add_comm (X_of_t^2) 1, ← add_assoc, add_comm (X_of_t * 2) 1]
    rw [mul_comm X_of_t 2]
    have h3 : 1 + 2 * X_of_t + X_of_t^2 = (1 + X_of_t)^2 := by ring_nf
    have h4 : -1 + r_of_s * X_of_t + (-(2 * X_of_t) - X_of_t ^ 2) = r_of_s * X_of_t - (1 + 2 * X_of_t + X_of_t^2) := by ring_nf
    rw [h4, h3]
    rw [← mul_assoc, mul_comm, ← mul_add]
    rw [← div_left_inj' (y_divisor_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
    change (y_of_t * (r_of_s * X_of_t + (1 + X_of_t) ^ 2)) / (r_of_s * X_of_t + (1 + X_of_t) ^ 2) = y_of_t 
    rw [mul_div_assoc, div_self (y_divisor_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)] 
    simp

-- Implicated by y_h1. Saved for further proof arguments in Theorem 3 Proof B
lemma y_h2
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  X_of_t^2 + 2 * (1 + η_of_point * r_of_s) * X_of_t + 1 = 0 := by
    intro r_of_s X_of_t point η_of_point 
    let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    calc
      X_of_t^2 + 2 * (1 + η_of_point * r_of_s) * X_of_t + 1 = X_of_t^2 + 2 * (1 + 1 / 2 * ((y_of_t - 1) / (y_of_t + 1)) * r_of_s) * X_of_t + 1 := by
        -- Unfold until reaching the y which is equivalent to y_of_t for comparison
        unfold η_of_point η point ϕ 
        simp only [Subtype.coe_eta, dite_eq_ite, one_div]
        rw [if_pos t.prop]
        change X_of_t ^ 2 + 2 * (1 + (y_of_t - 1) / (2 * (y_of_t + 1)) * r_of_s) * X_of_t + 1 = X_of_t ^ 2 + 2 * (1 + 2⁻¹ * ((y_of_t - 1) / (y_of_t + 1)) * r_of_s) * X_of_t + 1 
        rw [inv_eq_one_div]
        rw [← mul_div_mul_comm] 
        ring_nf
      _ = X_of_t^2 + (2 + r_of_s * (y_of_t - 1) / (y_of_t + 1)) * X_of_t + 1 := by
        rw [mul_add 2]
        rw [div_eq_mul_inv 1 2, mul_one, one_mul, mul_assoc (2⁻¹), ← mul_assoc 2 (2⁻¹) _]
        rw [mul_inv_cancel₀]
        ring_nf
        exact (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)
      _ = 0 := by 
        rw [y_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]

-- Implicated by y_h2. Saved for further proof arguments in TODO
lemma y_h3
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  X_of_t + 1 / X_of_t = -2 * (1 + η_of_point * r_of_s) := by
    intro r_of_s X_of_t point η_of_point 
    rw [← add_right_inj (2 * (1 + η_of_point * r_of_s))]
    rw [← mul_left_inj' (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
    change (2 * (1 + η_of_point * r_of_s) + (X_of_t + 1 / X_of_t)) * X_of_t = (2 * (1 + η_of_point * r_of_s) + -2 * (1 + η_of_point * r_of_s)) * X_of_t
    have h1 : (2 * (1 + η_of_point * r_of_s) + -2 * (1 + η_of_point * r_of_s)) * X_of_t = 0 := by ring_nf
    rw [h1, ← y_h2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    change (2 * (1 + η_of_point * r_of_s) + (X_of_t + 1 / X_of_t)) * X_of_t = X_of_t^2 + 2 * (1 + η_of_point * r_of_s) * X_of_t + 1
    ring_nf
    rw [mul_inv_cancel₀ (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
    ring_nf

lemma X_comparison_implication
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  have h2_2 : (t2 ≠ 1 ∧ t2 ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
  let X1 := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X1 + X2 = -2 * (1 + η_of_point * r_of_s) := by
    intro t1 t2 h2_2 X1 X2 point η_of_point r_of_s
    let u1 := u t q field_cardinality q_prime_power q_mod_4_congruent_3
    let u2 := u ⟨t2, h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    let v1 := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let v2 := v ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v1 := LegendreSymbol.χ v1 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v2 := LegendreSymbol.χ v2 q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold X2
    rw [X_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    exact (y_h3 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)

lemma X_comparison_implication2
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  have h2_2 : (t2 ≠ 1 ∧ t2 ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
  let X1 := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X2 * X1 = 1 := by
    intro t1 t2 h2_2 X1 X2
    unfold X2
    rw [X_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [← inv_eq_one_div]
    rw [inv_mul_cancel₀ (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]

lemma X2_h3
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  have h2_2 : (t2 ≠ 1 ∧ t2 ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X'_of_t := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  (X2_of_t - X_of_t) * (X2_of_t - X'_of_t) = 0 := by
    intro t1 t2 h2_2 point X_of_t X'_of_t X2_of_t 
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      (X2_of_t - X_of_t) * (X2_of_t - X'_of_t) = X2_of_t^2 - (X_of_t + X'_of_t) * X2_of_t + X_of_t * X'_of_t := by ring_nf
      _ = X2_of_t^2 + 2 * (1 + η_of_point * r_of_s) * X2_of_t + 1 := by
        rw [X_comparison_implication t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        change X2_of_t ^ 2 - -2 * (1 + η_of_point * r_of_s) * X2_of_t + X_of_t * X'_of_t = X2_of_t ^ 2 + 2 * (1 + η_of_point * r_of_s) * X2_of_t + 1
        rw [mul_add, mul_comm X_of_t _, X_comparison_implication2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        ring_nf
      _ = 0 := by exact X2_h2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point

-- TODO usage? best possible statement?
lemma X2_h4
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  have h2_2 : (t2 ≠ 1 ∧ t2 ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X'_of_t := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  X2_of_t = X_of_t ∨ X2_of_t = X'_of_t := by
    intro t1 t2 h2_2 point X_of_t X'_of_t X2_of_t 
    have h1 : (X2_of_t - X_of_t) * (X2_of_t - X'_of_t) = 0 := by exact X2_h3 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [mul_eq_zero] at h1
    nth_rw 1 [← add_left_inj (-X_of_t)]
    nth_rw 2 [← add_left_inj (-X'_of_t)]
    ring_nf
    exact h1

lemma χ_IsSquare_h1
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_v := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
  IsSquare ((χ_of_v * v_of_t)^((q + 1) / 4)) := by sorry

lemma y_comparison
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  have h2_2 : (t2 ≠ 1 ∧ t2 ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
  let y1 := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y2 := y ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  y2 = y1 := by
    intro t1 t2 h2_2 y1 y2
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X1 := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      y2 = (r_of_s * X2 - (1 + X2)^2) / (r_of_s * X2 + (1 + X2)^2) := by
        change (r_of_s * X2 - (1 + X2)^2) / (r_of_s * X2 + (1 + X2)^2) = (r_of_s * X2 - (1 + X2)^2) / (r_of_s * X2 + (1 + X2)^2)
        rfl
      _ = (r_of_s * (1 / X1) - (1 + (1 / X1))^2) / (r_of_s * (1 / X1) + (1 + (1 / X1))^2) := by
        unfold X2
        rw [X_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
      _ = (r_of_s * X1 - (X1 + 1)^2) / (r_of_s * X1 + (X1 + 1)^2) := by
        have h2_10_1 : X1^2 / X1^2 = 1 := by
          have h2_10_1_1 : X1^2 ≠ 0 := by
            rw [pow_two]
            apply mul_ne_zero
            · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
            · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t
          apply div_self h2_10_1_1
        rw [← mul_one ((r_of_s * (1 / X1) - (1 + 1 / X1) ^ 2) / (r_of_s * (1 / X1) + (1 + 1 / X1) ^ 2))]
        nth_rw 7 [← h2_10_1]
        rw [← mul_div_mul_comm]
        rw [sub_mul, add_mul]
        have h2_10_2 : (1 / X1) * X1^2 = X1 := by
          rw [mul_comm, ← mul_div_assoc, mul_one]
          rw [pow_two, mul_div_assoc, div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
          simp
        have h2_10_3 : (1 + 1 / X1) ^ 2 * X1^2 = (X1 + 1)^2 := by
          rw [← mul_pow _ _ 2]
          rw [add_mul, one_mul]
          rw [mul_comm, ← mul_div_assoc, mul_one]
          rw [div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
        rw [mul_assoc]
        rw [h2_10_2, h2_10_3]
      _ = y1 := by
        rw [add_comm]
        unfold y1 y X1
        simp
        rfl

lemma point_comparison
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  have h2_2 : (t2 ≠ 1 ∧ t2 ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
  let y1 := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y2 := y ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x1 := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x2 := x ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  (x1, y1) = (x2, y2) := by
    intro t1 t2 h2_2 y1 y2 x1 x2
    unfold x2 y2
    rw [x_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [y_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]

-- Used in the main case of Theorem 3 Proof part B
lemma X_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 : 
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  (X_of_t - 1)^2 = 0 := by
    intro X_of_t
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    have h1_1 : X_of_t + 1 / X_of_t = -2 * (1 + η_of_point * r_of_s) := by exact (y_h3 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
    rw [η_h1] at h1_1
    ring_nf at h1_1
    rw [← mul_left_inj' (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)] at h1_1
    rw [add_mul] at h1_1
    change X_of_t * X_of_t + X_of_t⁻¹ * X_of_t = 2 * X_of_t at h1_1
    rw [← add_left_inj (2 * X_of_t)]
    ring_nf
    rw [inv_mul_cancel₀ (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)] at h1_1
    rw [pow_two, add_comm]
    nth_rw 2 [mul_comm]
    exact h1_1

-- Used in the main case of Theorem 3 Proof part B
lemma X_η_h2
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 : 
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  X_of_t = 1 := by
    intro X_of_t
    have h1 : (X_of_t - 1)^2 = 0 := by exact (X_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)
    simp at h1
    rw [← add_left_inj (-1)]
    ring_nf
    have h2 : -1 + X_of_t = X_of_t - 1 := by ring_nf
    rw [h2]
    exact h1

-- Used in the main case of Theorem 3 Proof part B
lemma u_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 : 
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3;
  u_of_t = 1 := by
    intro u_of_t
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let χ_of_v_of_t := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    have h3_1 : X_of_t = χ_of_v_of_t * u_of_t := by
      unfold X_of_t X
      rfl
    unfold X_of_t at h3_1
    rw [X_η_h2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1] at h3_1
    -- TODO have to make case comparison of chi(v) to conclude that u can only be 1
    sorry

-- Used in the main case of Theorem 3 Proof part B
lemma t_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 : 
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  t.val = 0 := by
    let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
    have h1 : u_of_t = 1 := by exact (u_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)
    unfold u_of_t u at h1
    have h4_1 : 1 + t.val ≠ 0 := by exact FiniteFieldBasic.one_add_t_ne_zero t
    rw [← mul_right_inj' h4_1, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self h4_1] at h1
    rw [← add_left_inj (t.val - 1)] at h1
    ring_nf at h1
    symm at h1
    rw [← div_left_inj' (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h1
    ring_nf at h1
    rw [mul_assoc, inv_mul_cancel₀ (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3), mul_one] at h1
    exact h1

-- Used in the main case of Theorem 3 Proof part B
lemma v_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 : 
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  v_of_t = r_of_s^2 := by
    intro v_of_t r_of_s
    unfold v_of_t v
    rw [(u_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)]
    ring_nf
    rfl

-- Used in the main case of Theorem 3 Proof part B
lemma Y_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 : 
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let χ_of_c_of_s  := (LegendreSymbol.χ c_of_s q field_cardinality q_prime_power q_mod_4_congruent_3)
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  Y_of_t = r_of_s * χ_of_c_of_s := by
    intro Y_of_t c_of_s χ_of_c_of_s r_of_s
    let χ_of_one_add_one_div_c_of_s_pow_two := (LegendreSymbol.χ (1 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3)
    let χ_of_r_of_s := (LegendreSymbol.χ r_of_s q field_cardinality q_prime_power q_mod_4_congruent_3)
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3;
    let χ_of_v_of_t := (LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3)
    let χ_of_r_of_s_div_c_of_s := (LegendreSymbol.χ (r_of_s / c_of_s) q field_cardinality q_prime_power q_mod_4_congruent_3)
    let χ_of_r_of_s_pow_two := (LegendreSymbol.χ (r_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3)
    let χ_of_sum := LegendreSymbol.χ (u_of_t ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      Y_of_t = (r_of_s^2)^((q + 1) / 4) * χ_of_one_add_one_div_c_of_s_pow_two := by
        unfold Y_of_t Y
        rw [(v_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)]
        rw [(u_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)]
        change (χ_of_r_of_s_pow_two  * r_of_s^2) ^ ((q + 1) / 4) * χ_of_r_of_s_pow_two * (LegendreSymbol.χ (1 ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3) = (r_of_s ^ 2) ^ ((q + 1) / 4) * χ_of_one_add_one_div_c_of_s_pow_two
        have h1 : r_of_s^2 ≠ 0 := by
          rw [pow_two]
          apply mul_ne_zero
          · exact r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
          · exact r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
        have h2 : IsSquare (r_of_s^2) := by apply IsSquare.sq
        unfold χ_of_r_of_s_pow_two 
        rw [LegendreSymbol.χ_a_eq_one (r_of_s^2) h1 h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        nth_rw 2 [pow_two] 
        rw [mul_one, one_mul, mul_one]
      _ = χ_of_r_of_s * r_of_s * χ_of_r_of_s_div_c_of_s := by
        -- TODO understand
        sorry
      _ = r_of_s * χ_of_c_of_s := by
        -- TODO same square root argument as above (χ(r)r = r ?) ... understand
        sorry

-- Implicated by main case of Theorem 3 proof part B. Saved for later usage in TODO
lemma y_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 : 
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  y_of_t = (r_of_s - 4) / (r_of_s + 4) := by
    intro r_of_s y_of_t
    unfold y_of_t y
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    change (r_of_s * X_of_t - (1 + X_of_t) ^ 2) / (r_of_s * X_of_t + (1 + X_of_t) ^ 2) = (r_of_s - 4) / (r_of_s + 4)
    unfold X_of_t
    rw [X_η_h2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1]
    ring_nf

lemma y_of_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  have h1 : (0 : F) ≠ 1 ∧ (0 : F) ≠ -1 := by exact FiniteFieldBasic.zero_h1 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let y_of_t := y ⟨(0 : F), h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  y_of_t = (r_of_s - 4) / (r_of_s + 4) := by
    intro h1 y_of_t r_of_s
    unfold y_of_t y
    rw [X_of_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    change (r_of_s * 1 - (1 + 1) ^ 2) / (r_of_s * 1 + (1 + 1) ^ 2) = (r_of_s - 4) / (r_of_s + 4)
    ring_nf

lemma ϕ_of_t_eq_zero_one
  (t : { n : F // n = 1 ∨ n = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_t := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_of_t = (0, 1) := by
    intro ϕ_of_t 
    unfold ϕ_of_t ϕ
    rcases t.prop with h | h
    · rw [h]
      simp
    · rw [h]
      simp

lemma y_add_one_eq_two
  (t : { t : F // t = 1 ∨ t = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y_of_t := point.2
  y_of_t + 1 = 2 := by
    intro point y_of_t
    unfold y_of_t point
    rw [ϕ_of_t_eq_zero_one t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp
    norm_num


