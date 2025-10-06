import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
import Elligator.Elligator1.Properties
import Elligator.Elligator1.Sets

namespace Elligator.Elligator1

-- Original-Reference: Theorem 3
section InvertedMap

variable {F : Type*} [Field F] [Fintype F]

-- Chapter 3.3 Theorem 3.1
lemma ϕ_inv_only_two_specific_preimages
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_t := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let ϕ_of_neg_t := ϕ (-t) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_of_t = ϕ_of_neg_t
  ↔ ¬ (∃ (w : { n : F // n ≠ t ∧ n ≠ -t}), ϕ w.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 = ϕ_of_t) := by
    intro ϕ_of_t ϕ_of_neg_t
    constructor
    · sorry
    · sorry
    -- TODO rethink actual statement
    --· exact ϕ_inv_only_two_specific_preimages_mpr t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    --· exact ϕ_inv_only_two_specific_preimages_mp t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

lemma X2_defined
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  :
  let y := point.val.snd
  2 * (y + 1) ≠ 0 := by
    intro y
    have h1 : y + 1 ≠ 0 := by 
    -- TODO how to use property as implication
      --exact point.property.left
      sorry
    apply mul_ne_zero
    · exact (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)
    · exact h1

lemma z_defined
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  c_of_s^2 ≠ 0
  := by
    exact (c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)

lemma t2_defined
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  :
  let u2_of_point := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  (1 + u2_of_point) ≠ 0 := by
    intro u2_of_point
    sorry
