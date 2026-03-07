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
