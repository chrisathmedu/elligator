import Elligator.Common

variable {F : Type*} [Field F] [Fintype F]

namespace FiniteFieldBasic

lemma q_ne_two 
  (q : ℕ)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : q ≠ 2 := by
  intro h
  have mod_two : 2 % 4 = 2 := by norm_num
  nth_rw 1 [← h] at mod_two
  rw [q_mod_4_congruent_3] at mod_two
  norm_num at mod_two

lemma q_not_dvd_two
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : ¬(q ∣ 2) := by
  intro h
  -- Since q is prime and (q % 4 = 3 => q ≠ 2), it cannot divide 2. 
  -- So in this assumption, q must be 2.
  rw [Nat.prime_dvd_prime_iff_eq q_prime (Nat.prime_two)] at h
  apply q_ne_two q q_prime q_mod_4_congruent_3 at h
  have h1 : q ≠ 2 := q_ne_two q q_prime q_mod_4_congruent_3
  contradiction

lemma two_ne_zero 
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 
  (2 : F) ≠ 0 := by
    intro h
    have h1 : (2 : F) = 0 ↔ q ∣ 2 := by
      sorry
    rw [h1] at h
    --apply prime_two_or_dvd_of_dvd_two_mul_pow_self_two q_prime h
    --apply h1.2
    -- Because q prime and does not divide 2, 2 cannot be zero since q is 
    -- 0 in a field with q elements!
    have h2 : ¬(q ∣ 2) := by
      apply q_not_dvd_two q field_cardinality q_prime q_mod_4_congruent_3 
    contradiction

lemma neg_one_ne_zero 
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 
  (-1 : F) ≠ 0 := by
    sorry

lemma q_sub_one_over_two_ne_zero
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  (q - 1) / 2 ≠ 0 := by 
  apply Nat.div_ne_zero_iff.2
  constructor
  · norm_num
  · sorry

