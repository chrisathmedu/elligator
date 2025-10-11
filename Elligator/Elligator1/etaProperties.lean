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
import Elligator.Elligator1.yProperties

namespace Elligator.Elligator1

section etaProperties

variable {F : Type*} [Field F] [Fintype F]

lemma η_eq_zero
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
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  η_of_point = 0 := by
    intro point η_of_point 
    unfold η_of_point η
    let y_of_t := point.2
    change (y_of_t - 1) / (2 * (y_of_t + 1)) = 0
    unfold y_of_t point
    rw [ϕ_of_t_eq_zero_one t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp

lemma η_ne_zero
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
  :
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  η_of_point ≠ 0 := by
    intro η_of_point
    let x := point.val.1
    let y := point.val.2
    unfold η_of_point η
    change (y - 1) / (2 * (y + 1)) ≠ 0
    apply div_ne_zero 
    · intro h1
      have h2 : y ≠ 1 := by exact y_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero
      have h2 : y = 1 := by
        rw [← add_left_inj 1] at h1
        simp at h1
        exact h1
      contradiction
    · unfold ϕ_over_F_props at point_props
      apply mul_ne_zero
      · exact FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
      · exact point_props.1

