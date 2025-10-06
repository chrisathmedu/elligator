import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
import Elligator.Elligator1.sProperties
import Elligator.Elligator1.cProperties
import Elligator.Elligator1.uProperties
import Elligator.Elligator1.vProperties
import Elligator.Elligator1.XProperties
import Elligator.Elligator1.YProperties
import Elligator.Elligator1.xProperties
import Elligator.Elligator1.yProperties

namespace Elligator.Elligator1

-- Original-Reference: Theorem 1
section Map

variable {F : Type*} [Field F] [Fintype F]

theorem u_defined :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1}, (1 + t.val) ≠ 0 := by
    intro t
    exact FiniteFieldBasic.one_add_t_ne_zero t

theorem Y_defined
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1}, (c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)^2 ≠ 0 := by
    intro t
    exact c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

theorem x_defined
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1}, Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ≠ 0 := by
    intro t
    exact Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t

theorem y_defined
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1},
  ((r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
  * (X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
  + (1 + (X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3))^2)
  ≠ 0 := by
    intro t
    exact y_divisor_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t

-- Chapter 3.2 Theorem 1
theorem map_fulfills_helper_equation
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
    intro r_of_s X_of_t Y_of_t
    exact Y_pow_two_eq_X_pow_five_add_r_pow_two_sub_2_mul_X_pow_three_add_X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

-- Chapter 3.2 Theorem 1
theorem variable_mul_ne_zero
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
  exact u_mul_v_mul_X_mul_Y_mul_x_mul_y_add_one_ne_zero t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

-- Chapter 3.2 Theorem 1
theorem map_fulfills_curve_equation
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
    intro x_of_t y_of_t d_of_s
    exact x_pow_two_add_y_pow_two_eq_one_add_d_mul_x_pow_two_mul_y_pow_two t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

