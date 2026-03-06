import Mathlib
import Elligator.Elligator1.Variables
import Elligator.Elligator1.dProperties

namespace Elligator.Elligator1

section EdwardsCurve

variable {F : Type*} [Field F] [Fintype F]

-- TODO generalize to actual characteristic ≠ 2
def edwards_curve_equation
  (x y : F)
  (d : {d : F // d ≠ 0 ∧ d ≠ 1})
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  := x^2 + y^2 = 1 + d * x^2 * y^2

-- E_over_F(s, q) is the set of points on the curve defined by the equation in the paper.
def E_over_F
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : Set (F × F) :=
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  have d_h : d_of_s ≠ 0 ∧ d_of_s ≠ 1 := by exact d_ne_zero_and_d_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  {p | edwards_curve_equation p.fst p.snd ⟨d_of_s, d_h⟩ q field_cardinality q_prime_power q_mod_4_congruent_3}

lemma zero_one_fulfill_edwards_curve_equation
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  have d_h : d_of_s ≠ 0 ∧ d_of_s ≠ 1 := by exact d_ne_zero_and_d_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  edwards_curve_equation (0 : F) (1 : F) ⟨d_of_s, d_h⟩ q field_cardinality q_prime_power q_mod_4_congruent_3 := by
    intro d_of_s d_h
    unfold edwards_curve_equation
    ring
