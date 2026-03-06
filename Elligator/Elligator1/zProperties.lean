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

namespace Elligator.Elligator1

section zProperties

variable {F : Type*} [Field F] [Fintype F]

lemma z_eq_zero
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
  let z_of_point := z s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  z_of_point = 0 := by
    intro point z_of_point
    unfold z_of_point z
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    repeat rw [X2_eq_neg_one t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    change LegendreSymbol.χ ((c_of_s - 1) * s * (-1) * (1 + (-1)) * point.1 * ((-1) ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3 = 0
    simp
    exact LegendreSymbol.χ_a_zero_eq_zero (0 : F) (rfl) q field_cardinality q_prime_power q_mod_4_congruent_3
