import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables

namespace Elligator.Elligator1

section sProperties

variable {F : Type*} [Field F] [Fintype F]

lemma s_pow_two_ne_two
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : s^2 ≠ 2 := by
  have h1 : s^2 - 2 ≠ 0 := by
    intro h
    rw [h] at s_h2
    norm_num at s_h2
  intro h
  rw [h] at h1
  norm_num at h1

lemma s_pow_two_ne_neg_two
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : s^2 ≠ -2 := by
  have h1 : s^2 + 2 ≠ 0 := by
    intro h
    rw [h] at s_h2
    norm_num at s_h2
  intro h
  rw [h] at h1
  norm_num at h1
