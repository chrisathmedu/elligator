import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables

namespace Elligator.Elligator1

section Sets

variable {F : Type*} [Field F] [Fintype F]

/-- E_over_F(s, q) is the set of points on the curve defined by the equation in the paper.

Paper definition at chapter 3.3 theorem 3.
-/
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
  {p | p.fst^2 + p.snd^2 = 1 + d_of_s * p.fst^2 * p.snd^2}

-- Properties do not have to assume that the given `point` is element of E(F)
-- since these are just returning a Prop which would be false in the other case.
--
-- Actual assumption of E(F) is done in theorems using the following `def`s.

noncomputable def ϕ_over_F_prop1
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : Prop :=
  let y := point.snd
  y + 1 ≠ 0

def ϕ_over_F_prop2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : Prop :=
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  IsSquare ((1 + η_of_point * r_of_s)^2 - 1)

def ϕ_over_F_prop3
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : Prop :=
  let x := point.fst
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_c_of_s := LegendreSymbol.χ c_of_s q field_cardinality q_prime_power q_mod_4_congruent_3
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  η_of_point * r_of_s = -2 → x = 2 * s * (c_of_s - 1) * χ_of_c_of_s / r_of_s

-- Chapter 3.3 Theorem 3.2
noncomputable def ϕ_over_F
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  Set (F × F) :=
  let E_over_F_of_s := E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  {
    p |
    (h : p ∈ E_over_F_of_s) →
    (
        ϕ_over_F_prop1 q field_cardinality q_prime_power q_mod_4_congruent_3 p
      ∧ ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 p
      ∧ ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 p
    )
  }

def S (b : ℕ) : Set (List Binary) := {n | n.length = b}

noncomputable def σ
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (τ : {n : List Binary // n ∈ S (b q q_prime_power q_mod_4_congruent_3)})
  : F :=
  ∑ i ∈ (Finset.range (b q q_prime_power q_mod_4_congruent_3 - 1)), τ.val[i]! * 2^i

