import Mathlib

namespace Elligator1

set_option linter.unusedVariables false
set_option diagnostics true

variable {F : Type*} [Field F] [Fintype F]

variable (q : ℕ) 
variable (q_prime : Nat.Prime q) [Fact (Nat.Prime q)] 
variable (q_mod_4_congruent_3 : q % 4 = 3)
variable (field_cardinality : Fintype.card F = q)

/-- χ(a) is the quadratic character of a in the finite field F with q elements, where q is a prime congruent to 3 modulo 4.

This function was added, since Mathlib.NumberTheory.LegendreSymbol.Basic is restricted to ℤ.

Paper definition at chapter 3.1.
-/
noncomputable def χ 
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F := a^((Fintype.card F - 1) / 2)

lemma χ_a_zero_eq_zero
  (a : F)
  (a_eq_zero : a = 0)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a = 0 := by
    change a^((Fintype.card F -1)/2) = 0
    rw [field_cardinality]
    rw [a_eq_zero]
    apply zero_pow
    intro h
    have h0 : q > 1 := by 
      apply Nat.Prime.one_lt
      apply q_prime
    sorry

    --have h1 : q-1 ≠ 0 := by sorry
    --have h2 : 2 ≠ 0 := by sorry
    --apply div_ne_zero h1 h2

lemma χ_a_square_eq_square
  (a : F)
  (a_eq_nonzero : a ≠ 0)
  (a_square : ∃ (w : F), w^2 = a)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a = 1 := by
    --change a^((q-1)/2) = 1
    sorry

lemma χ_a_nonsquare_eq_nonsquare
  (a : F)
  (a_eq_nonzero : a ≠ 0)
  (a_square : ¬ (∃ (w : F), w^2 = a))
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a = -1 := sorry

lemma χ_neg_one_eq_nonsquare :
  let χ_of_neg_one := χ (-1 : F) q field_cardinality q_prime q_mod_4_congruent_3 
  χ_of_neg_one = -1 := sorry

lemma χ_χ_a_eq_χ_a
  (a : F)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_χ_of_a := χ (χ_of_a) q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_χ_of_a = χ_of_a := sorry

lemma χ_ab_eq_χ_a_mul_χ_b
  (a b : F)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_b := χ b q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_a_mul_b := χ (a * b) q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a_mul_b = χ_of_a * χ_of_b := sorry

lemma χ_1_over_a_eq_χ_a
  (a : F)
  (a_non_zero : a ≠ 0)
  :
  let χ_of_1_over_a := χ (1 / a) q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_1_over_a = χ_of_a := sorry

lemma χ_1_over_a_eq_1_over_χ_a
  (a : F)
  (a_non_zero : a ≠ 0)
  :
  let χ_of_1_over_a := χ (1 / a) q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_1_over_a = 1 / χ_of_a := sorry

variable (s : F)
variable (s_h1 : s ≠ 0) 
variable (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)

/-- c(s) is a constant defined in the paper.

Paper definition at chapter 3.2 theorem 1.
-/
noncomputable def c 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F := 2 / s^2

/-- r(s) is a constant defined in the paper.

Paper definition at chapter 3.2 theorem 1.
-/
noncomputable def r 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F := 
  let c_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  c_s + 1 / c_s

/-- d(s) is a constant defined in the paper.

Paper definition at chapter 3.2 theorem 1.
-/
noncomputable def d 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F := 
  let c_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  (-(c_s + 1)^2 / (c_s - 1)^2)

/-- u(t) is a function defined in the paper.

Paper definition at chapter 3.2 theorem 1.
-/
noncomputable def u 
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  : F :=
  (1 - t.val) / (1 + t.val)

/-- v(t, s) is a function defined in the paper.

Paper definition at chapter 3.2 theorem 1.
-/
noncomputable def v 
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F := 
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  (u t)^5 + (r_of_s^2 - 2) * (u t)^3 + u t

/-- X(t, s) is a function defined in the paper.

Paper definition at chapter 3.2 theorem 1.
-/
noncomputable def X 
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F := 
  let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_v_of_t := χ v_of_t q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_v_of_t * u t

/-- Y(t, s) is a function defined in the paper.

Paper definition at chapter 3.2 theorem 1.
-/
noncomputable def Y
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F :=
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_v_of_t := χ v_of_t q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_sum := χ ((u t)^2 + 1 / c_of_s^2) q field_cardinality q_prime q_mod_4_congruent_3
  (χ_of_v_of_t * v_of_t)^((q + 1) / 4) * χ_of_v_of_t * χ_of_sum  

/-- x(t, s) is a function defined in the paper. It is the x-coordinate of the point on the curve.

Paper definition at chapter 3.2 theorem 1.
-/
noncomputable def x 
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F :=
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  (c_of_s - 1) * s * X_of_t * (1 + X_of_t) / Y_of_t

/-- y(t, s) is a function defined in the paper. It is the y-coordinate of the point on the curve.

Paper definition at chapter 3.2 theorem 1.
-/
noncomputable def y 
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F :=
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  (r_of_s * X_of_t - (1 + X_of_t)^2) / (r_of_s * X_of_t + (1 + X_of_t)^2)

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
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (field_cardinality : Fintype.card F = q)
  : ¬(q ∣ 2) := by
  intro h
  -- Since q is prime and (q % 4 = 3 => q ≠ 2), it cannot divide 2. 
  -- So in this assumption, q must be 2.
  rw [Nat.prime_dvd_prime_iff_eq q_prime (Nat.prime_two)] at h
  apply q_ne_two q q_prime q_mod_4_congruent_3 at h
  exact h

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
      apply q_not_dvd_two q q_prime q_mod_4_congruent_3 field_cardinality
    contradiction

lemma c_ne_zero 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  c_of_s ≠ 0 := by
  change 2 / s^2 ≠ 0
  apply div_ne_zero
  · apply two_ne_zero q field_cardinality q_prime q_mod_4_congruent_3
  · rw [pow_two]
    apply mul_ne_zero s_h1 s_h1

lemma s_pow_two_ne_two 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
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
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : s^2 ≠ -2 := by
  have h1 : s^2 + 2 ≠ 0 := by 
    intro h
    rw [h] at s_h2
    norm_num at s_h2
  intro h
  rw [h] at h1
  norm_num at h1

lemma c_ne_one
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  c_of_s ≠ 1 := by
  change 2 / s^2 ≠ 1
  apply div_ne_one_of_ne
  apply Ne.symm
  apply s_pow_two_ne_two s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3

lemma c_ne_neg_one
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  c_of_s ≠ -1 := by
  change 2 / s^2 ≠ -1
  intro h
  have h1 : s^2 = -2 := by 
    calc 
      s^2 = 2 / (-1 : F) := by
        rw [← h]
        ring_nf
        rw [inv_inv]
        rw [mul_assoc]
        rw [mul_comm (2⁻¹) 2]
        rw [mul_inv_cancel₀ (two_ne_zero q field_cardinality q_prime q_mod_4_congruent_3)]
        rw [mul_one]
      _ = -2 := by norm_num
  apply s_pow_two_ne_neg_two s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 at h1
  exact h1

theorem c_h 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  c_of_s * (c_of_s - 1) * (c_of_s + 1) ≠ 0 := by
  change (2 / s^2) * ((2 / s^2) - 1) * ((2 / s^2) + 1) ≠ 0
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
    · apply sub_ne_zero.2
      exact c_ne_one s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  · intro h
    have h1 : (-1 : F) + 1 = 0 := by norm_num 
    rw [← h1] at h
    apply add_right_cancel_iff.1 at h
    have h2 : s^2 = -2 := by
      calc 
        s^2 = 2 / (-1 : F) := by
          rw [← h]
          ring_nf
          rw [inv_inv]
          rw [mul_assoc]
          rw [mul_comm (2⁻¹) 2]
          rw [mul_inv_cancel₀ (two_ne_zero q field_cardinality q_prime q_mod_4_congruent_3)]
          rw [mul_one]
        _ = -2 := by norm_num
    apply s_pow_two_ne_neg_two s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 at h2
    exact h2

theorem r_ne_zero 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  r_of_s ≠ 0 := by 
  change (2 / s^2) + 1 / (2 / s^2) ≠ 0
  intro h
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  have h1 : c_of_s  = (-1 : F) / c_of_s := by 
    change c_of_s + 1 / c_of_s = 0 at h
    rw [← add_right_inj (-1 / c_of_s)] at h
    rw [add_comm] at h
    rw [add_zero] at h
    have h3 : 1 / c_of_s + -1 / c_of_s = 0 := by 
      ring_nf
    nth_rw 1 [← add_zero c_of_s]
    rw [← h3]
    rw [← add_assoc]
    exact h
  have h2 : c_of_s^2 = -1 := by 
    calc 
      c_of_s^2 = -1 / c_of_s * c_of_s := by 
        rw [pow_two]
        nth_rw 1 [h1]
      _ = -1 := by
        nth_rw 1 [← neg_one_mul 1]
        ring
        rw [mul_inv_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3)]
  have h3 : IsSquare (-1 : F) := by
    rw [← h2]
    rw [pow_two]
    apply IsSquare.mul_self c_of_s
  have h4 : q % 4 ≠ 3 := by 
    rw [FiniteField.isSquare_neg_one_iff] at h3
    rw [field_cardinality] at h3
    exact h3
  contradiction

theorem d_nonsquare 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  ¬ (∃ w : F, w^2 = d_of_s) := by
    change ¬∃ w, w ^ 2 = (-((2 / s^2) + 1)^2 / ((2 / s^2) - 1)^2)
    intro h
    sorry

theorem u_defined :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1}, ∃ (w : F), w = u t := by
  sorry

theorem v_defined 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1},
  ∃ (w : F), w = v t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  := by
  sorry

theorem X_defined
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1},
  ∃ (w : F), w = X t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  := by
  sorry

theorem Y_defined
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1},
  ∃ (w : F), w = Y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  := by
  sorry

theorem x_defined
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1},
  ∃ (w : F), w = x t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  := by
  sorry

theorem y_defined
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1},
  ∃ (w : F), w = y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  := by
  sorry

-- Chapter 3.2 Theorem 1
theorem map_fulfills_curve_equation
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let x_of_t := x t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let y_of_t := x t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  x_of_t^2 + y_of_t^2 = 1 + d_of_s * x_of_t^2 * y_of_t^2 := sorry

-- Chapter 3.2 Theorem 1
theorem map_variables_mul_neq_zero
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let x_of_t := x t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let y_of_t := x t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  u t * v_of_t * X_of_t  * Y_of_t * x_of_t * (y_of_t + 1) ≠ 0 := by
    sorry

-- Chapter 3.2 Theorem 1
theorem map_fulfills_specific_equation
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  Y_of_t ^2 = X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t := sorry

/-- ϕ(t, s) is a function defined in the paper. It maps a numer `t` in F s to a point on the curve.

Paper definition at chapter 3.2 definition 2.
-/
-- Chapter 3.2 Definition 2
noncomputable def ϕ
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : (F) × (F) :=
  open scoped Classical in if h : t ≠ 1 ∧ t ≠ -1
  then 
  (
    x ⟨t, h⟩ s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3,
    y ⟨t, h⟩ s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  )
  else (0, 1) 

-- Chapter 3.3 Theorem 3.1
theorem ϕ_inv_only_two_specific_preimages 
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 
  let ϕ_of_t := ϕ t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
  let ϕ_of_neg_t := ϕ (-t) s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
  ϕ_of_t = ϕ_of_neg_t  
  ↔ ¬ (∃ (w : F) (h: w ≠ -t), ϕ w s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 = ϕ_of_t) := by 
  sorry

/-- E_over_F(s, q) is the set of points on the curve defined by the equation in the paper.

Paper definition at chapter 3.3 theorem 3.
-/
def E_over_F
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : Set ((F) × (F)) := 
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  {p | p.fst^2 + p.snd^2 = 1 + d_of_s * p.fst^2 * p.snd^2}

def ϕ_over_F_prop1 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3})
  := 
  let y := point.val.snd
  y + 1 ≠ 0

/-- η(s, q, point) is a function defined in the paper.

Paper definition at chapter 3.3 theorem 3.
-/
noncomputable def η 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3})
  : F 
  := 
  let y := point.val.snd
  (y - 1) / (2 * (y + 1))

def ϕ_over_F_prop2 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3})
  := 
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let η_of_point := η s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 point
  ∃ (w : F), w^2 = (1 + η_of_point * r_of_s)^2 - 1

def ϕ_over_F_prop3
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3})
  := 
  let x := point.val.fst
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_c_of_s := χ c_of_s q field_cardinality q_prime q_mod_4_congruent_3
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let η_of_point := η s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 point
  η_of_point * r_of_s = -2 → x = 2 * s * (c_of_s - 1) * χ_of_c_of_s / r_of_s

-- Chapter 3.3 Theorem 3.2
noncomputable def ϕ_over_F 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  Set ((F) × (F)) :=
  let E_over_F_of_s := E_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  { 
    p | 
    (h : p ∈ E_over_F_of_s) → 
    (ϕ_over_F_prop1 s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 ⟨p, h⟩
    ∧ ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 ⟨p, h⟩
    ∧ ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 ⟨p, h⟩)
  }

theorem point_in_E_over_F_with_props_iff_point_in_ϕ_over_F
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3})
  :
  ((h : point.val ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3) →
    ϕ_over_F_prop1 s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 ⟨point.val, h⟩
    ∧ ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 ⟨point.val, h⟩
    ∧ ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 ⟨point.val, h⟩)
  ↔ point.val ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 := by
    sorry

-- Used to build definitions for arguments which sometimes require different
-- assumptions regarding group membership.
theorem E_over_F_subset_ϕ_over_F 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 
  let E_over_F_of_s := E_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let ϕ_over_F_q_of_s := ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  E_over_F_of_s ⊆ ϕ_over_F_q_of_s := by sorry

theorem point_in_E_over_F
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3})
  : 
  let E_over_F_of_s := E_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  point.val ∈ E_over_F_of_s 
  := by sorry

noncomputable def X2
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3})
  (h : point.val ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3)
  := 
  let η_of_point := η s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 ⟨point.val, h⟩
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  (-(1 + η_of_point * r_of_s) + ((1 + η_of_point * r_of_s)^2 - 1)^((q + 1) / 4))

noncomputable def z 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3})
  : F 
  := 
  let x := point.val.fst
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 point (point_in_E_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 point)
  let a := (c_of_s - 1) * s * X2_of_point * (1 + X2_of_point) * x * (X2_of_point^2 + 1 / c_of_s^2)
  χ a q field_cardinality q_prime q_mod_4_congruent_3

noncomputable def u2 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3})
  : F 
  := 
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 point (point_in_E_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 point)
  let z_of_point := z s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 point
  z_of_point * X2_of_point 

noncomputable def t2 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3})
  : F 
  := 
  let u2_of_point := u2 s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 point
  (1 - u2_of_point) / (1 + u2_of_point)

theorem X2_defined
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ point : {p : F × F // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3},
  ∃ (w : F), w = X2 s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 point (point_in_E_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 point)
  := by
  sorry

theorem z_defined
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ point : {p : F × F // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3},
  ∃ (w : F), w = z s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 point
  := by
  sorry

theorem u2_defined
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ point : {p : F × F // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3},
  ∃ (w : F), w = u2 s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 point
  := by
  sorry

theorem t2_defined
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ point : {p : F × F // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3},
  ∃ (w : F), w = t2 s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 point
  := by
  sorry

/-- `invmap_representative` is ...

Paper definition at chapter 3.3 Theorem 3.3.
-/
theorem invmap_representative
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3})
  :
  let t2_of_point := t2 s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 point
  let ϕ_of_t2_of_point := ϕ t2_of_point s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  ϕ_of_t2_of_point = point :=
  sorry

noncomputable def b : ℕ := Int.toNat ⌊ Real.logb 2 q ⌋

abbrev Binary := Fin 2

def S (b : ℕ) : Set (List Binary) := {n | n.length = b}

noncomputable def σ
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (τ : {n : List Binary // n ∈ S (b q)}) 
  : F := 
  ∑ i ∈ (Finset.range (b q - 1)), τ.val[i]! * 2^i

/-- \`ι` is the injective map that maps a binary string `τ` to a point on the curve `E(F_q)`.

Paper definition at chapter 3.4 Theorem 4.
-/
noncomputable def ι 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (τ : {n : List Binary // n ∈ S (b q)}) 
  : (F × F)
  := 
  let σ_of_τ := σ q field_cardinality q_prime q_mod_4_congruent_3 τ
  ϕ (σ_of_τ) s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3

theorem S_cardinality : Set.ncard (S (b q)) = (q + 1) / 2 := by sorry

theorem ι_injective_map
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ∀ (τ₁ τ₂ : {n : List Binary // n ∈ S (b q)}),
  ι s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 τ₁ = ι s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 τ₂
  → τ₁ = τ₂ := by
  sorry

noncomputable def ι_S
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  Set ((F) × (F)) :=
  { 
    e | ∃ (τ : {n : List Binary // n ∈ S (b q)}), 
      e = ι s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 τ
  }

theorem ι_S_eq_ϕ_over_F
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_over_F_of_s := ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let ι_S_of_s := ι_S s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  ϕ_over_F_of_s = ι_S_of_s := by
    sorry

