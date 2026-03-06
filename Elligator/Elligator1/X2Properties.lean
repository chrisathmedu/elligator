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
