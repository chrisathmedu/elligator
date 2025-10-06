import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables

namespace Elligator.Elligator1

-- Original-Reference: Definition 2
section DecodingFunction

variable {F : Type*} [Field F] [Fintype F]

noncomputable def DecodingFunction
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F × F := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
