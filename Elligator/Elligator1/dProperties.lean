import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
import Elligator.Elligator1.Sets
import Elligator.Elligator1.sProperties
import Elligator.Elligator1.cProperties

namespace Elligator.Elligator1

section dProperties

variable {F : Type*} [Field F] [Fintype F]

lemma d_nonsquare
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  ¬IsSquare d_of_s := by
    intro d_of_s
    rw [isSquare_iff_exists_mul_self d_of_s]
    change ¬∃ r, (-((2 / s^2) + 1)^2 / ((2 / s^2) - 1)^2) = r * r
    rintro ⟨w, Pw⟩
    have h00 : (2 / s^2 - 1)^2 ≠ 0 := by
      rw [pow_two]
      apply mul_ne_zero
      · apply sub_ne_zero.2
        exact c_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      · apply sub_ne_zero.2
        exact c_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have h01 : (2 / s^2 + 1)^2 ≠ 0 := by
      rw [pow_two]
      apply mul_ne_zero
      change c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 + 1 ≠ 0
      · intro h
        have h' : (c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) = -1 := by
          rw [← add_right_inj (-1)] at h
          rw [add_zero] at h
          rw [add_comm] at h
          have h8 : (1 : F) + (-1 : F) = 0 := by ring
          rw [add_assoc] at h
          rw [h8] at h
          rw [add_zero] at h
          exact h
        apply c_ne_neg_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 at h'
        exact h'
      · intro h
        have h' : (c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) = -1 := by
          rw [← add_right_inj (-1)] at h
          rw [add_zero] at h
          rw [add_comm] at h
          have h8 : (1 : F) + (-1 : F) = 0 := by ring
          rw [add_assoc] at h
          rw [h8] at h
          rw [add_zero] at h
          exact h
        apply c_ne_neg_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 at h'
        exact h'
    have h1 : w^2 * ((2 / s^2) - 1)^2 / ((2 / s^2) + 1)^2 = -1 := by
      rw [pow_two, ← Pw]
      rw [div_eq_mul_inv]
      rw [div_eq_mul_inv]
      rw [← neg_one_mul]
      rw [mul_assoc (-1 * (2 / s ^ 2 + 1) ^ 2) (((2 / s ^ 2 - 1) ^ 2)⁻¹) ((2 / s ^ 2 - 1) ^ 2)]
      rw [inv_mul_cancel₀ h00]
      rw [mul_one]
      rw [mul_assoc]
      rw [mul_inv_cancel₀ h01]
      rw [mul_one]
    have h2 : IsSquare (-1 : F) := by
      rw [← h1]
      have h3 : IsSquare (w^2) := by
        rw [pow_two]
        apply IsSquare.mul_self w
      have h4 : IsSquare (((2 / s^2) - 1)^2 / ((2 / s^2) + 1)^2) := by
        apply IsSquare.div
        · rw [pow_two]
          apply IsSquare.mul_self (2 / s^2 - 1)
        · rw [pow_two]
          apply IsSquare.mul_self (2 / s^2 + 1)
      rw [mul_div_assoc]
      apply IsSquare.mul h3 h4
    have h5 : q % 4 ≠ 3 := by
      rw [FiniteField.isSquare_neg_one_iff] at h2
      rw [field_cardinality] at h2
      exact h2
    contradiction

lemma d_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  d_of_s ≠ 0 := by
    intro d_of_s
    let d_nonsquare := d_nonsquare s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    intro h
    have h1 : IsSquare d_of_s := by
      unfold IsSquare
      use 0
      grind
    contradiction

lemma d_ne_one
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  d_of_s ≠ 1 := by
    intro d_of_s
    let d_nonsquare := d_nonsquare s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    intro h
    have h1 : IsSquare d_of_s := by
      unfold IsSquare
      use 0
      grind
    contradiction
