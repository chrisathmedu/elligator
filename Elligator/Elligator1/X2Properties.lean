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
import Elligator.Elligator1.Map
import Elligator.Elligator1.MapProperties
import Elligator.Elligator1.etaProperties

namespace Elligator.Elligator1

section X2Properties

variable {F : Type*} [Field F] [Fintype F]

lemma X2_eq_neg_one
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
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  X2_of_point = -1 := by
    intro point X2_of_point
    unfold X2_of_point X2
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    change -(1 + η_of_point * r_of_s) + ((1 + η_of_point * r_of_s) ^ 2 - 1) ^ ((q + 1) / 4) = -1
    unfold η_of_point
    rw [η_eq_zero t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    ring_nf
    rw [zero_pow, add_zero]
    exact FiniteFieldBasic.q_add_one_over_four_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3

lemma X2_h1
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  :
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  (1 + η_of_point * r_of_s + X2_of_t)^2 = (1 + η_of_point * r_of_s)^2 - 1 := by
    intro η_of_point r_of_s X2_of_t
    unfold X2_of_t X2
    let a := ((1 + η_of_point * r_of_s)^2 - 1)^((q + 1) / 4)
    let a_sqr := (1 + η_of_point * r_of_s)^2 - 1
    change (1 + η_of_point * r_of_s + (-(1 + η_of_point * r_of_s) + a))^2 = a_sqr
    ring_nf
    unfold a a_sqr
    rw [← field_cardinality]
    nth_rw 2 [add_comm]
    rw [← pow_mul, FiniteFieldBasic.one_add_card_over_four_mul_two_eq_one_add_card_over_two q field_cardinality q_mod_4_congruent_3]
    unfold η_of_point
    nth_rw 2 [add_comm]
    rw [field_cardinality, LegendreSymbol.a_pow_q_add_one_over_two_eq_a point.prop.2.1 q field_cardinality q_prime_power q_mod_4_congruent_3]

lemma X2_h2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  :
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  X2_of_t^2 + 2 * (1 + η_of_point *r_of_s) * X2_of_t + 1 = 0 := by
    intro η_of_point r_of_s X2_of_t
    have h : (1 + η_of_point * r_of_s + X2_of_t)^2 = (1 + η_of_point * r_of_s)^2 - 1 := by exact X2_h1 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    grind

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
    let point_of_ϕ_fulfills_ϕ_over_F_props := point_of_ϕ_fulfills_ϕ_over_F_props t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      (X2_of_t - X_of_t) * (X2_of_t - X'_of_t) = X2_of_t^2 - (X_of_t + X'_of_t) * X2_of_t + X_of_t * X'_of_t := by grind
      _ = X2_of_t^2 + 2 * (1 + η_of_point * r_of_s) * X2_of_t + 1 := by
        rw [X_comparison_implication t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        change X2_of_t ^ 2 - -2 * (1 + η_of_point * r_of_s) * X2_of_t + X_of_t * X'_of_t = X2_of_t ^ 2 + 2 * (1 + η_of_point * r_of_s) * X2_of_t + 1
        rw [mul_add, mul_comm X_of_t _, X_comparison_implication2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        grind
      _ = 0 := by exact X2_h2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point.val, point_of_ϕ_fulfills_ϕ_over_F_props⟩

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

lemma X2_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  :
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  X2_of_point ≠ 0 := by
    intro X2_of_point
    let X2_equation := X2_h2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let point_prop := point.prop
    simp at X2_equation
    change X2_of_point^2 + 2 * (1 + η_of_point * r_of_s) * X2_of_point + 1 = 0 at X2_equation
    intro h
    rw [h] at X2_equation
    simp at X2_equation

lemma y_divisor_ne_zero_with_X2_for_X
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  r_of_s * X2_of_point + (1 + X2_of_point)^2 ≠ 0 := by
    intro r_of_s X2_of_point h1
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
    let X2_equation := X2_h2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let point_prop := point.prop
    simp at X2_equation
    change X2_of_point^2 + 2 * (1 + η_of_point * r_of_s) * X2_of_point + 1 = 0 at X2_equation
    let y := point.val.2
    have h2 : (1 - 2 * η_of_point ) * r_of_s * X2_of_point = 0 := by
      rw [← h1]
      grind
    have h3 : 2 * η_of_point = 1 := by
      have h3_1 : r_of_s * X2_of_point ≠ 0 := by
        apply mul_ne_zero
        · exact (r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
        · exact (X2_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
      rw [← div_left_inj' h3_1]
      grind
    have h4 : y - 1 = y + 1 := by
      unfold η_of_point η at h3
      grind
    have h5 : y - 1 ≠ y + 1 := by grind
    contradiction

lemma X2_ne_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  (y_eq_one : point.val.2 ≠ 1)
  :
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  X2_of_point ≠ -1 := by
    intro X2_of_point h1
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
    let X2_equation := X2_h2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let point_prop := point.prop
    let y := point.val.2
    simp at X2_equation
    change X2_of_point^2 + 2 * (1 + η_of_point * r_of_s) * X2_of_point + 1 = 0 at X2_equation
    rw [h1] at X2_equation
    simp at X2_equation
    have h2 : η_of_point = 0 := by
      ring_nf at X2_equation
      let r_ne_zero := r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      rw [← div_left_inj' (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at X2_equation
      rw [← div_left_inj' r_ne_zero] at X2_equation
      ring_nf at X2_equation
      change -(η_of_point * r_of_s * 2⁻¹ * r_of_s⁻¹ * 2) = 0 at X2_equation
      have h2_1 : -(η_of_point * r_of_s * 2⁻¹ * r_of_s⁻¹ * 2) = -(η_of_point * (r_of_s * r_of_s⁻¹) * (2 * 2⁻¹)) := by grind
      rw [h2_1] at X2_equation
      rw [mul_inv_cancel₀ r_ne_zero, mul_inv_cancel₀ (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at X2_equation
      grind
    have h3 : η_of_point ≠ 0 := by
      unfold η_of_point η
      have h3_1 : y - 1 ≠ 0 := by
        intro h3_1_1
        grind
      have h3_2 : 2 * (y + 1) ≠ 0 := by
        intro h3_2_1
        let y_add_one_ne_zero := point_prop.1
        unfold ϕ_over_F_prop1 at y_add_one_ne_zero
        rw [← div_left_inj' (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h3_2_1
        ring_nf at h3_2_1
        rw [inv_mul_cancel₀ (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h3_2_1
        grind
      apply div_ne_zero h3_1 h3_2
    contradiction

lemma y_with_X2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  (y_eq_one : point.val.2 ≠ 1)
  :
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y := point.val.2
  y = (r_of_s * X2_of_point - (1 + X2_of_point)^2) / (r_of_s * X2_of_point + (1 + X2_of_point)^2) := by
    intro X2_of_point r_of_s y
    let X2_equation := X2_h2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let point_prop := point.prop
    let y_add_one_ne_zero := point_prop.1
    let X2_ne_zero := X2_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let two_ne_zero := FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_ne_zero := r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    simp at X2_equation
    change X2_of_point^2 + 2 * (1 + η_of_point * r_of_s) * X2_of_point + 1 = 0 at X2_equation
    have h1 : y = (1 + 2 * η_of_point) / (1 - 2 * η_of_point) := by
      have h1_1 : η_of_point = (y - 1) / (2 * (y + 1)) := by
        unfold η_of_point η y
        simp
      have h1_2 : (2 * (y + 1)) ≠ 0 := by
        apply mul_ne_zero
        · exact two_ne_zero
        · exact y_add_one_ne_zero
      grind
    have h2 : 2 * η_of_point = - ((1 + X2_of_point)^2) / (r_of_s * X2_of_point) := by
      have h2_1 : 1 + η_of_point * r_of_s = - (X2_of_point^2 + 1) / (2 * X2_of_point) := by
        have h2_1_1 : 2 * X2_of_point ≠ 0 := by
          apply mul_ne_zero
          · exact two_ne_zero
          · exact X2_ne_zero
        rw [← add_left_inj (-X2_of_point^2), ← add_left_inj (-1)] at X2_equation
        rw [← div_left_inj' h2_1_1] at X2_equation
        ring_nf at X2_equation
        grind
      have h2_2 : 2 * η_of_point = -((1 + X2_of_point)^2) / (r_of_s * X2_of_point) := by
        have h2_2_1 : η_of_point = (-(X2_of_point^2 + 1) / (2 * X2_of_point) -1) / r_of_s := by grind
        have h2_2_2 : η_of_point = -(X2_of_point + 1)^2 / (2 * r_of_s * X2_of_point) := by
          have h2_2_2_1 : (2 * X2_of_point) / (2 * X2_of_point) = 1 := by grind
          rw [← h2_2_2_1] at h2_2_1
          grind
        rw [← mul_left_inj' two_ne_zero] at h2_2_2
        simp_all
        ring_nf
        grind
      grind
    have h3 : (1 + 2 * η_of_point) / (1 - 2 * η_of_point) = ((r_of_s * X2_of_point - (1 + X2_of_point)^2)) / ((r_of_s * X2_of_point + (1 + X2_of_point)^2)) := by
      have h3_1 : 1 = (r_of_s * X2_of_point) / (r_of_s * X2_of_point) := by grind
      rw [h2]
      nth_rw 1 [h3_1]
      nth_rw 2 [h3_1]
      rw [← add_div, ← sub_div, div_div]
      grind
    rw [← h3]
    exact h1

lemma y_with_X2_of_X2_eq_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  (y_eq_one : point.val.2 ≠ 1)
  :
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y := point.val.2
  X2_of_point = 1 → y = (r_of_s - 4) / (r_of_s + 4) := by
    intro X2_of_point r_of_s y X2_h
    let y_with_X2 := y_with_X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point y_eq_one
    grind

lemma η_mul_r_eq_neg_two_of_X2_eq_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {P : F × F // ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 P})
  (y_eq_one : point.val.2 ≠ 1)
  :
  let x := point.val.1
  let y := point.val.2
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let ϕ_of_zero  := ϕ 0 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X2_of_point = 1 → η_of_point * r_of_s = -2 := by
    intro x y η_of_point  X2_of_point r_of_s ϕ_of_zero X2_h
    unfold η_of_point η
    have h1 : y = (r_of_s - 4) / (r_of_s + 4) := by exact y_with_X2_of_X2_eq_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point y_eq_one X2_h
    change (y - 1) / (2 * (y + 1)) * r_of_s = -2
    rw [h1]

    ring_nf
    simp_all
    sorry
