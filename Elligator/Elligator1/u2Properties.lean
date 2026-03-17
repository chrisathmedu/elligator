import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
import Elligator.Elligator1.sProperties
import Elligator.Elligator1.cProperties
import Elligator.Elligator1.dProperties
import Elligator.Elligator1.uProperties
import Elligator.Elligator1.vProperties
import Elligator.Elligator1.XProperties
import Elligator.Elligator1.YProperties
import Elligator.Elligator1.xProperties
import Elligator.Elligator1.yProperties
import Elligator.Elligator1.etaProperties
import Elligator.Elligator1.X2Properties
import Elligator.Elligator1.zProperties

namespace Elligator.Elligator1

section u2Properties

variable {F : Type*} [Field F] [Fintype F]

lemma u2_eq_zero
  (t : { t : F // t = 1 ∨ t = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let u2_of_point := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  u2_of_point = 0 := by
    intro point u2_of_point
    unfold u2_of_point u2
    rw [z_eq_zero t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp

lemma u2_eq_u
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (X_h :
    let point := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    X2_of_t = X_of_t
  )
  :
  let point := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
  let u2_of_t := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  u2_of_t = u_of_t := by
    intro point u_of_t u2_of_t
    have h2_2 : (-t.val ≠ 1 ∧ -t.val ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X'_of_t := X ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let x_of_t := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let z_of_point := z s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let χ_of_v := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_Y := LegendreSymbol.χ Y_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold u2_of_t u2
    rw [X_h]
    change z_of_point * X_of_t = u_of_t
    have h1 : (c_of_s - 1) * s * X2_of_t * (1 + X2_of_t) = x_of_t * Y_of_t := by
      unfold X2_of_t
      rw [X_h]
      rw [← div_left_inj' (Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
      change x_of_t = x_of_t * Y_of_t / Y_of_t
      rw [mul_div_assoc, div_self (Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)]
      ring_nf
    have h2 : z_of_point = χ_of_Y * (LegendreSymbol.χ (X_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
      calc
        z_of_point = (LegendreSymbol.χ (x_of_t^2 * Y_of_t * (X_of_t^2 + 1 / c_of_s^2)) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
          unfold z_of_point z
          change LegendreSymbol.χ ((c_of_s - 1) * s * X2_of_t * (1 + X2_of_t) * point.1 * (X2_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ (x_of_t ^ 2 * Y_of_t * (X_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3
          unfold point ϕ
          simp only [h1]
          rw [dif_pos t.prop]
          change LegendreSymbol.χ (x_of_t * Y_of_t * x_of_t * (X2_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ (x_of_t ^ 2 * Y_of_t * (X_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3
          unfold X2_of_t X_of_t
          rw [X_h]
          ring_nf
        _ = χ_of_Y * (LegendreSymbol.χ (X_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
          rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (x_of_t^2 * Y_of_t) (X_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (x_of_t^2)  Y_of_t q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [LegendreSymbol.χ_a_eq_one (x_of_t^2) (FiniteFieldBasic.pow_two_ne_zero (x_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)) (IsSquare.sq x_of_t) q field_cardinality q_prime_power q_mod_4_congruent_3]
          unfold χ_of_Y
          ring_nf
    have h3 : (LegendreSymbol.χ (u_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) = (LegendreSymbol.χ (X_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
      unfold X_of_t X
      rw [mul_pow]
      nth_rw 3 [pow_two]
      rw [← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b v_of_t v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [← pow_two, LegendreSymbol.χ_a_eq_one (v_of_t^2) (FiniteFieldBasic.pow_two_ne_zero (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)) (IsSquare.sq v_of_t) q field_cardinality q_prime_power q_mod_4_congruent_3]
      unfold u_of_t
      simp_all
    have h4 : χ_of_Y = χ_of_v * (LegendreSymbol.χ (X_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
      rw [← h3]
      unfold χ_of_Y Y_of_t Y
      let χ_sum := LegendreSymbol.χ (u_of_t ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3;
      change (LegendreSymbol.χ ((χ_of_v * v_of_t)^((q + 1) / 4) * χ_of_v * χ_sum) q field_cardinality q_prime_power q_mod_4_congruent_3) = χ_of_v * χ_sum
      rw [mul_assoc, LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b ((χ_of_v * v_of_t)^((q + 1) / 4)) (χ_of_v * χ_sum) q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_a_eq_one ((χ_of_v * v_of_t)^((q + 1) / 4)) (χ_of_v_mul_v_of_t_pow_q_add_one_over_four_ne_zero t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) (χ_IsSquare_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b χ_of_v χ_sum q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_of_χ_of_a_eq_χ_of_a v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_of_χ_of_a_eq_χ_of_a (u_of_t ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3]
      unfold χ_of_v χ_sum
      simp_all
    have h5 : z_of_point = χ_of_v := by
      rw [h2, h4, mul_assoc]
      rw [← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (X_of_t^2 + 1 / c_of_s^2) (X_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3, ← pow_two]
      rw [LegendreSymbol.χ_a_eq_one ((X_of_t^2 + 1 / c_of_s^2)^2) (FiniteFieldBasic.pow_two_ne_zero (X_pow_two_add_one_over_c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)) (IsSquare.sq (X_of_t^2 + 1 / c_of_s^2)) q field_cardinality q_prime_power q_mod_4_congruent_3]
      simp
    rw [h5]
    unfold X_of_t X
    change χ_of_v * (χ_of_v * u_of_t ) = u_of_t
    rw [← mul_assoc, ← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b v_of_t v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3, ← pow_two]
    have h6 : IsSquare (v_of_t^2) := by exact IsSquare.sq v_of_t
    rw [LegendreSymbol.χ_a_eq_one (v_of_t^2) (FiniteFieldBasic.pow_two_ne_zero (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)) h6 q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp

lemma u2_eq_u'
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (X_h :
    let point := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
    have h2_2 : (-t.val ≠ 1 ∧ -t.val ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
    let X'_of_t := X ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    X2_of_t = X'_of_t
  )
  :
  have h2_2 : (-t.val ≠ 1 ∧ -t.val ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
  let point := (ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let u'_of_t := u ⟨-t.val, h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
  let u2_of_t := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  u2_of_t = u'_of_t := by
    intro h2_2 point u'_of_t u2_of_t
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X'_of_t := X ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let x_of_t := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let x'_of_t := x ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let Y'_of_t := Y ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let z_of_point := z s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let v'_of_t := v ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let χ_of_v := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v' := LegendreSymbol.χ v'_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_Y := LegendreSymbol.χ Y_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_Y' := LegendreSymbol.χ Y'_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold u2_of_t u2
    rw [X_h]
    change z_of_point * X'_of_t = u'_of_t
    have h1 : (c_of_s - 1) * s * X2_of_t * (1 + X2_of_t) = x'_of_t * Y'_of_t := by
      unfold X2_of_t
      rw [X_h]
      rw [← div_left_inj' (Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨-t.val, h2_2⟩)]
      change x'_of_t = x'_of_t * Y'_of_t / Y'_of_t
      rw [mul_div_assoc, div_self (Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨-t.val, h2_2⟩)]
      ring_nf
    have h2 : z_of_point = χ_of_Y' * (LegendreSymbol.χ (X'_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
      calc
        z_of_point = (LegendreSymbol.χ (x'_of_t^2 * Y'_of_t * (X'_of_t^2 + 1 / c_of_s^2)) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
          unfold z_of_point z
          change LegendreSymbol.χ ((c_of_s - 1) * s * X2_of_t * (1 + X2_of_t) * point.1 * (X2_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ (x'_of_t ^ 2 * Y'_of_t * (X'_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3
          unfold point ϕ
          simp only [h1]
          rw [dif_pos t.prop]
          change LegendreSymbol.χ (x'_of_t * Y'_of_t * x_of_t * (X2_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ (x'_of_t ^ 2 * Y'_of_t * (X'_of_t ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3
          unfold X2_of_t X'_of_t x'_of_t x_of_t
          rw [x_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [X_h]
          ring_nf
        _ = χ_of_Y' * (LegendreSymbol.χ (X'_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
          rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (x'_of_t^2 * Y'_of_t) (X'_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (x'_of_t^2) Y'_of_t q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [LegendreSymbol.χ_a_eq_one (x'_of_t^2) (FiniteFieldBasic.pow_two_ne_zero (x_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨-t, h2_2⟩)) (IsSquare.sq x'_of_t) q field_cardinality q_prime_power q_mod_4_congruent_3]
          unfold χ_of_Y'
          ring_nf
    have h3 : (LegendreSymbol.χ (u'_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) = (LegendreSymbol.χ (X'_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
      unfold X'_of_t X
      rw [mul_pow]
      nth_rw 3 [pow_two]
      rw [← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b v'_of_t v'_of_t q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [← pow_two, LegendreSymbol.χ_a_eq_one (v'_of_t^2) (FiniteFieldBasic.pow_two_ne_zero (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨-t, h2_2⟩)) (IsSquare.sq v'_of_t) q field_cardinality q_prime_power q_mod_4_congruent_3]
      unfold u'_of_t
      simp_all
    have h4 : χ_of_Y' = χ_of_v' * (LegendreSymbol.χ (X'_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) := by
      rw [← h3]
      unfold χ_of_Y' Y'_of_t Y
      let χ_sum := LegendreSymbol.χ (u'_of_t ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3;
      change (LegendreSymbol.χ ((χ_of_v' * v'_of_t)^((q + 1) / 4) * χ_of_v' * χ_sum) q field_cardinality q_prime_power q_mod_4_congruent_3) = χ_of_v' * χ_sum
      rw [mul_assoc, LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b ((χ_of_v' * v'_of_t)^((q + 1) / 4)) (χ_of_v' * χ_sum) q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_a_eq_one ((χ_of_v' * v'_of_t)^((q + 1) / 4)) (χ_of_v_mul_v_of_t_pow_q_add_one_over_four_ne_zero ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) (χ_IsSquare_h1 ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b χ_of_v' χ_sum q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_of_χ_of_a_eq_χ_of_a v'_of_t q field_cardinality q_prime_power q_mod_4_congruent_3]
      rw [LegendreSymbol.χ_of_χ_of_a_eq_χ_of_a (u'_of_t ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3]
      unfold χ_of_v' χ_sum
      simp_all
    have h5 : z_of_point = χ_of_v' := by
      rw [h2, h4, mul_assoc]
      rw [← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (X'_of_t^2 + 1 / c_of_s^2) (X'_of_t^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3, ← pow_two]
      rw [LegendreSymbol.χ_a_eq_one ((X'_of_t^2 + 1 / c_of_s^2)^2) (FiniteFieldBasic.pow_two_ne_zero (X_pow_two_add_one_over_c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨-t.val, h2_2⟩)) (IsSquare.sq (X'_of_t^2 + 1 / c_of_s^2)) q field_cardinality q_prime_power q_mod_4_congruent_3]
      simp
    rw [h5]
    unfold X'_of_t X
    change χ_of_v' * (χ_of_v' * u'_of_t ) = u'_of_t
    rw [← mul_assoc, ← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b v'_of_t v'_of_t q field_cardinality q_prime_power q_mod_4_congruent_3, ← pow_two]
    have h6 : IsSquare (v'_of_t^2) := by exact IsSquare.sq v'_of_t
    rw [LegendreSymbol.χ_a_eq_one (v'_of_t^2) (FiniteFieldBasic.pow_two_ne_zero (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨-t.val, h2_2⟩)) h6 q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp

lemma u2_h1
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
  have h2_2 : (-t.val ≠ 1 ∧ -t.val ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
  let u'_of_t := u ⟨-t.val, h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
  let u2_of_t := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  u2_of_t = u_of_t ∨ u2_of_t = u'_of_t := by
    intro point u_of_t h2_2 u'_of_t u2_of_t
    rcases (X2_h4 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) with h | h
    · left
      exact u2_eq_u t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h
    · right
      exact u2_eq_u' t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h

-- Theorem 3 part C define
noncomputable def u'
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  : F :=
  let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  z * X

lemma u'_eq_X2_or_u'_eq_neg_X2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  u = X ∨ u = -X := by
    intro u X
    let z'_eq_one_or_z'_eq_neg_one := z'_eq_one_or_z'_eq_neg_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    unfold u u'
    grind

lemma u'_ne_neg_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  (y_ne_one : point.val.2 ≠ 1)
  :
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let X := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  X ≠ 1 → u ≠ -1 := by
    intro u X h1
    let z'_eq_one_or_z'_eq_neg_one := z'_eq_one_or_z'_eq_neg_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero y_ne_one
    let z := z' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
    let X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one := X2_ne_one_and_X2_ne_neg_one_of_X2_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_props⟩ y_ne_one
    unfold u u'
    grind

-- Theorem 3 part C define
noncomputable def v'
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  : F :=
  let u := u' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props
  let r := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  -- Note: this is just the definition of v as in theorem 1
  u^5 + (r^2 - 2) * u^3 + u
