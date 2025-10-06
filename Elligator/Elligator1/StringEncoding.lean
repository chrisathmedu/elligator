import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
import Elligator.Elligator1.Sets

namespace Elligator.Elligator1

-- Original-Reference: Theorem 4
section StringEncoding

variable {F : Type*} [Field F] [Fintype F]

/-- \`ι` is the injective map that maps a binary string `τ` to a point on the curve `E(F_q)`.

Paper definition at chapter 3.4 Theorem 4.
-/
noncomputable def ι
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (τ : {n : List Binary // n ∈ S (b q q_prime_power q_mod_4_congruent_3)})
  : (F × F)
  :=
  let σ_of_τ := σ q field_cardinality q_prime_power q_mod_4_congruent_3 τ
  ϕ σ_of_τ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

noncomputable def ι_S
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  Set ((F) × (F)) :=
  {
    e | ∃ (τ : {n : List Binary // n ∈ S (b q q_prime_power q_mod_4_congruent_3)}),
      e = ι s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 τ
  }

lemma S_cardinality
  (q : ℕ)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : Set.ncard (S (b q q_prime_power q_mod_4_congruent_3)) = (q + 1) / 2 := by sorry

lemma ι_injective_map
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ (τ₁ τ₂ : {n : List Binary // n ∈ S (b q q_prime_power q_mod_4_congruent_3)}),
  ι s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 τ₁ = ι s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 τ₂
  → τ₁ = τ₂ := by
  sorry

lemma ι_S_eq_ϕ_over_F
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_over_F_of_s := ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let ι_S_of_s := ι_S s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_of_s = ι_S_of_s := by
    sorry
