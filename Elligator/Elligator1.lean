import Mathlib

namespace Elligator1

set_option linter.unusedVariables false
set_option diagnostics true

variable {F : Type*} [Field F] [Fintype F]

variable (q : ℕ) 
variable (q_prime : Nat.Prime q)
variable (q_mod_4_congruent_3 : q % 4 = 3)
variable (field_cardinality : Fintype.card F = q)

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
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a = 0 := by
    change a^((Fintype.card F -1)/2) = 0
    rw [field_cardinality]
    rw [a_eq_zero]
    apply zero_pow (q_sub_one_over_two_ne_zero q field_cardinality q_prime q_mod_4_congruent_3)

lemma χ_a_ne_zero
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a ≠ 0 := by
    change a^((Fintype.card F -1)/2) ≠ 0
    sorry

lemma neg_χ_a_ne_χ_a
  (a : F)
  (a_nonzero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a ≠ -χ_of_a := by
    sorry

lemma χ_a_eq_one
  (a : F)
  (a_nonzero : a ≠ 0)
  (a_square : IsSquare a)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a = 1 := by
    --change a^((q-1)/2) = 1
    sorry

lemma χ_of_a_pow_n_eq_χ_a
  (a : F)
  (n : {n : ℕ | Odd n})
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a^(n.val) = χ_of_a := by 
    sorry

lemma χ_of_a_eq_neg_one
  (a : F)
  (a_nonzero : a ≠ 0)
  (a_nonsquare : IsSquare a = false)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a = -1 := sorry

lemma χ_of_neg_one_eq_neg_one 
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_neg_one := χ (-1 : F) q field_cardinality q_prime q_mod_4_congruent_3 
  χ_of_neg_one = -1 := sorry

lemma χ_of_χ_of_a_eq_χ_of_a
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_χ_of_a := χ (χ_of_a) q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_χ_of_a = χ_of_a := sorry

lemma χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b
  (a b : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_b := χ b q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_a_mul_b := χ (a * b) q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_a_mul_b = χ_of_a * χ_of_b := sorry

lemma χ_of_one_over_a_eq_χ_a
  (a : F)
  (a_non_zero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_1_over_a := χ (1 / a) q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_1_over_a = χ_of_a := sorry

lemma χ_of_one_over_a_eq_one_over_χ_a
  (a : F)
  (a_non_zero : a ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_1_over_a := χ (1 / a) q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  χ_of_1_over_a = 1 / χ_of_a := sorry

lemma one_over_χ_of_a_eq_χ_a
  (a : F)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let χ_of_a := χ a q field_cardinality q_prime q_mod_4_congruent_3
  1 / χ_of_a  = χ_of_a := by 
    sorry

lemma square_of_a
  (a : {n : F // IsSquare n})
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  a.val^((q + 1) / 2) = a.val := by 
    sorry

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

theorem c_add_one_ne_zero 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  c_of_s + 1 ≠ 0 := by
    intro c_of_s
    intro h
    change 2 / s^2 + 1 = 0 at h
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

theorem c_sub_one_ne_zero 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  c_of_s - 1 ≠ 0 := by
    apply sub_ne_zero.2
    exact c_ne_one s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3

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
    · exact c_sub_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  · exact c_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
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
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
  ¬IsSquare d_of_s := by
    intro d_of_s
    rw [isSquare_iff_exists_mul_self d_of_s]
    change ¬∃ r, (-((2 / s^2) + 1)^2 / ((2 / s^2) - 1)^2) = r * r
    rintro ⟨w, Pw⟩ 
    have h00 : (2 / s^2 - 1)^2 ≠ 0 := by
      rw [pow_two]
      apply mul_ne_zero
      · apply sub_ne_zero.2
        exact c_ne_one s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
      · apply sub_ne_zero.2
        exact c_ne_one s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
    have h01 : (2 / s^2 + 1)^2 ≠ 0 := by
      rw [pow_two]
      apply mul_ne_zero
      change c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 + 1 ≠ 0
      · intro h
        have h' : (c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3) = -1 := by
          rw [← add_right_inj (-1)] at h
          rw [add_zero] at h
          rw [add_comm] at h
          have h8 : (1 : F) + (-1 : F) = 0 := by ring
          rw [add_assoc] at h
          rw [h8] at h
          rw [add_zero] at h
          exact h
        apply c_ne_neg_one s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 at h'
        exact h'
      · intro h
        have h' : (c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3) = -1 := by
          rw [← add_right_inj (-1)] at h
          rw [add_zero] at h
          rw [add_comm] at h
          have h8 : (1 : F) + (-1 : F) = 0 := by ring
          rw [add_assoc] at h
          rw [h8] at h
          rw [add_zero] at h
          exact h
        apply c_ne_neg_one s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 at h'
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

lemma one_sub_t_ne_zero
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  (1 : F) - t.val ≠ 0 := by 
  intro h
  have h1 : t.val = 1 := by 
    rw [← add_right_inj t.val] at h
    rw [add_zero] at h
    rw [add_comm] at h
    have h' : t.val - t.val = 0 := by ring
    rw [sub_add] at h
    rw [h'] at h
    rw [sub_zero] at h
    symm at h
    exact h
  have h2 : t.val ≠ 1 := by 
    apply And.left
    exact t.property
  contradiction

lemma one_add_t_ne_zero
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  (1 : F) + t.val ≠ 0 := by 
  intro h
  have h1 : t.val = -1 := by 
    rw [← add_right_inj (-1)] at h
    rw [add_zero] at h
    rw [add_comm] at h
    have h' : (-1 : F) + 1 = 0 := by ring
    rw [add_comm] at h
    rw [← add_assoc] at h
    rw [h'] at h
    rw [zero_add] at h
    exact h
  have h2 : t.val ≠ -1 := by 
    apply And.right
    exact t.property
  contradiction

lemma u_ne_zero
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  u t ≠ (0 : F) := by
  change (1 - t.val) / (1 + t.val) ≠ 0
  apply div_ne_zero (one_sub_t_ne_zero t) (one_add_t_ne_zero t) 

theorem u_defined :
  ∀ t : {n : F // n ≠ 1 ∧ n ≠ -1}, ∃ (w : F), w = u t := by
  intro t
  use u t

lemma v_ne_zero
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  v t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 ≠ (0 : F) := by
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let u_of_t := u t
  change u_of_t^5 + (r_of_s^2 - 2) * u_of_t^3 + u_of_t ≠ 0
  have h1 : (r_of_s^2 - 2) = c_of_s^2 + 1 / c_of_s^2 := by
    calc 
      r_of_s^2 - 2 = (c_of_s + 1 / c_of_s)^2 - 2 := by
        change (c_of_s + 1 / c_of_s)^2 - 2 = (c_of_s + 1 / c_of_s)^2 - 2
        rfl
      _ = c_of_s^2 + 2 * (c_of_s * (1 / c_of_s)) + (1 / c_of_s)^2 - 2 := by
        rw [add_pow_two]
        rw [mul_assoc 2 c_of_s (1 / c_of_s)]
      _ = c_of_s^2 + 2 + 1 / c_of_s^2 - 2 := by
        ring
        rw [mul_inv_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3)]
        ring
      _ = c_of_s^2 + 1 / c_of_s^2 := by
        ring_nf
  rw [h1]
  intro h
  have h2 : u_of_t * (u_of_t^2 + c_of_s^2) * (u_of_t^2 + 1 / c_of_s^2) = 0 := by
    calc 
      u_of_t * (u_of_t^2 + c_of_s^2) * (u_of_t^2 + 1 / c_of_s^2) 
    = u_of_t * (u_of_t^2 * (u_of_t^2 + 1 / c_of_s^2) + c_of_s^2 * (u_of_t^2 + 1 / c_of_s^2)) := by
        rw [mul_assoc]
        rw [add_mul]
    _ = u_of_t ^ 5 + (c_of_s ^ 2 + 1 / c_of_s ^ 2) * u_of_t ^ 3 + u_of_t := by 
        ring_nf
        rw [mul_assoc]
        rw [← mul_pow c_of_s c_of_s⁻¹ 2]
        rw [mul_inv_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3)]
        rw [pow_two]
        repeat rw [mul_one]
    _  = 0 := by apply h
  have h3 : u_of_t * (u_of_t^2 + c_of_s^2) * (u_of_t^2 + 1 / c_of_s^2) ≠ 0 := by
    apply mul_ne_zero 
    · apply mul_ne_zero
      · apply u_ne_zero t
      · intro h3_1
        have h3_1_1 : -1 = (u_of_t / c_of_s)^2 := by
          rw [← add_left_inj (-c_of_s^2)] at h3_1
          rw [zero_add] at h3_1
          rw [add_assoc] at h3_1
          have h3_1_1_1 : c_of_s^2 = c_of_s^2 := by rfl
          rw [add_neg_eq_zero.2 h3_1_1_1] at h3_1
          rw [add_zero] at h3_1
          rw [← neg_one_mul] at h3_1
          rw [div_pow u_of_t c_of_s 2]
          have h3_1_1_2 : c_of_s^2 ≠ 0 := by 
            rw [pow_two]
            apply mul_ne_zero
            · apply c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
            · apply c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
          rw [← div_left_inj' h3_1_1_2] at h3_1
          rw [mul_div_assoc] at h3_1
          rw [← div_eq_one_iff_eq h3_1_1_2] at h3_1_1_1
          rw [h3_1_1_1] at h3_1
          rw [mul_one] at h3_1
          symm at h3_1
          exact h3_1
        have h3_1_2 : IsSquare (-1 : F) := by
          rw [h3_1_1]
          rw [pow_two]
          apply IsSquare.mul_self (u_of_t / c_of_s)
        have h3_1_3 : q % 4 ≠ 3 := by 
          rw [FiniteField.isSquare_neg_one_iff] at h3_1_2
          rw [field_cardinality] at h3_1_2
          exact h3_1_2
        contradiction
    · intro h3_2
      have h3_2_1 : -1 = (u_of_t * c_of_s)^2 := by 
        ring
        have h3_2_1_1 : c_of_s^2 = c_of_s^2 := by rfl
        have h3_2_1_2 : c_of_s^2 ≠ 0 := by 
          rw [pow_two]
          apply mul_ne_zero
          · apply c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
          · apply c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
        rw [← div_left_inj' h3_2_1_2]
        rw [mul_div_assoc]
        rw [← div_eq_one_iff_eq h3_2_1_2] at h3_2_1_1
        rw [h3_2_1_1, mul_one]
        rw [← add_left_inj (1 / c_of_s^2)]
        have h3_2_1_3 : 1 / c_of_s^2 = 1 / c_of_s^2 := by rfl
        rw [← neg_one_mul, mul_div_assoc, neg_one_mul]
        rw [neg_add_eq_zero.2 h3_2_1_3]
        symm
        exact h3_2
      have h3_2_2 : IsSquare (-1 : F) := by
        rw [h3_2_1]
        rw [pow_two]
        apply IsSquare.mul_self (u_of_t * c_of_s)
      have h3_2_3 : q % 4 ≠ 3 := by
        rw [FiniteField.isSquare_neg_one_iff] at h3_2_2
        rw [field_cardinality] at h3_2_2
        exact h3_2_2
      contradiction
  contradiction

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
  intro t
  use v t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3

lemma X_ne_zero
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  : 
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  X_of_t ≠ 0 := by
  let u_of_t := u t
  let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  apply mul_ne_zero
  · apply χ_a_ne_zero v_of_t (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t) q field_cardinality q_prime q_mod_4_congruent_3
  · apply u_ne_zero t


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
  intro t
  use X t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3

lemma Y_ne_zero
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  : 
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  Y_of_t ≠ 0 := by 
  let u_of_t := u t
  let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_v_of_t := χ v_of_t q field_cardinality q_prime q_mod_4_congruent_3
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_v_of_t := χ v_of_t q field_cardinality q_prime q_mod_4_congruent_3
  let χ_of_sum := χ ((u t)^2 + 1 / c_of_s^2) q field_cardinality q_prime q_mod_4_congruent_3
  change (χ_of_v_of_t * v_of_t)^((q + 1) / 4) * χ_of_v_of_t * χ_of_sum ≠ 0
  apply mul_ne_zero
  · apply mul_ne_zero
    · rw [mul_pow (χ_of_v_of_t) (v_of_t) ((q + 1) / 4)]
      apply mul_ne_zero
      · apply pow_ne_zero (((q + 1) / 4) : ℕ)
        apply χ_a_ne_zero v_of_t (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t) q field_cardinality q_prime q_mod_4_congruent_3 
      · apply pow_ne_zero (((q + 1) / 4) : ℕ)
        apply v_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
    · apply χ_a_ne_zero v_of_t (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t) q field_cardinality q_prime q_mod_4_congruent_3 
  · have χ_sum_ne_zero : (u_of_t)^2 + 1 / c_of_s^2 ≠ 0 := by 
      intro h3_2
      have h3_2_1 : -1 = (u_of_t * c_of_s)^2 := by 
        ring
        have h3_2_1_1 : c_of_s^2 = c_of_s^2 := by rfl
        have h3_2_1_2 : c_of_s^2 ≠ 0 := by 
          rw [pow_two]
          apply mul_ne_zero
          · apply c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
          · apply c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
        rw [← div_left_inj' h3_2_1_2]
        rw [mul_div_assoc]
        rw [← div_eq_one_iff_eq h3_2_1_2] at h3_2_1_1
        rw [h3_2_1_1, mul_one]
        rw [← add_left_inj (1 / c_of_s^2)]
        have h3_2_1_3 : 1 / c_of_s^2 = 1 / c_of_s^2 := by rfl
        rw [← neg_one_mul, mul_div_assoc, neg_one_mul]
        rw [neg_add_eq_zero.2 h3_2_1_3]
        symm
        exact h3_2
      have h3_2_2 : IsSquare (-1 : F) := by
        rw [h3_2_1]
        rw [pow_two]
        apply IsSquare.mul_self (u_of_t * c_of_s)
      have h3_2_3 : q % 4 ≠ 3 := by
        rw [FiniteField.isSquare_neg_one_iff] at h3_2_2
        rw [field_cardinality] at h3_2_2
        exact h3_2_2
      contradiction
    apply χ_a_ne_zero ((u t)^2 + 1 / c_of_s^2) χ_sum_ne_zero q field_cardinality q_prime q_mod_4_congruent_3 

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
  intro t
  use Y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3

lemma X_mul_Y_ne_zero
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  : 
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  X_of_t * Y_of_t ≠ 0 := by 
  apply mul_ne_zero 
  · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
  · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t

-- TODO this should result from lemma X_mul_Y_ne_zero. How to formalize this properly?
-- Do I have to state the problematic divisors in those lemmas?
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
  intro t
  use x t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3

lemma one_add_X_ne_zero 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
  (1 + X_of_t) ≠ (0 : F) := by
    let u_of_t := u t
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
    let χ_of_v_of_t := χ v_of_t q field_cardinality q_prime q_mod_4_congruent_3
    intro X
    change 1 + χ_of_v_of_t * u t ≠ 0
    intro h
    have h1 : χ_of_v_of_t * u_of_t = -1 := by
      rw [← add_right_inj (-1)] at h
      rw [add_zero] at h
      have h1_1 : (-1 : F) + (1 : F) = 0 := by ring
      rw [← add_assoc] at h
      rw [h1_1] at h
      rw [zero_add] at h
      exact h
    have h2 : u_of_t = -χ_of_v_of_t := by
      rw [← neg_one_mul (χ_of_v_of_t)]
      change u_of_t = -1 * χ v_of_t q field_cardinality q_prime q_mod_4_congruent_3
      rw [← one_over_χ_of_a_eq_χ_a v_of_t q field_cardinality q_prime q_mod_4_congruent_3]
      rw [← mul_left_inj' (χ_a_ne_zero v_of_t (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t) q field_cardinality q_prime q_mod_4_congruent_3)]
      ring_nf
      rw [mul_inv_cancel₀ (χ_a_ne_zero v_of_t (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t) q field_cardinality q_prime q_mod_4_congruent_3)]
      rw [mul_comm]
      change χ_of_v_of_t * u t = -1
      exact h1
    have h3 : v_of_t = -χ_of_v_of_t * (1 + r_of_s^2 - 2 + 1) := by 
      change u_of_t^5 + (r_of_s^2 - 2) * u_of_t^3 + u_of_t = -χ_of_v_of_t * (1 + r_of_s^2 - 2 + 1)
      repeat rw [h2]
      have h3_1: Odd 5 := by 
        apply Nat.odd_iff.2
        norm_num
      rw [← neg_one_mul, mul_pow, mul_pow]
      rw [χ_of_a_pow_n_eq_χ_a v_of_t ⟨5, h3_1⟩ q field_cardinality q_prime q_mod_4_congruent_3]
      have h3_2: Odd 3 := by 
        apply Nat.odd_iff.2
        norm_num
      rw [χ_of_a_pow_n_eq_χ_a v_of_t ⟨3, h3_2⟩ q field_cardinality q_prime q_mod_4_congruent_3]
      change (-1) ^ 5 * χ_of_v_of_t + (r_of_s ^ 2 - 2) * ((-1) ^ 3 * χ_of_v_of_t) + -1 * χ_of_v_of_t = -1 * χ_of_v_of_t * (1 + r_of_s ^ 2 - 2 + 1)
      ring
    have h4 : v_of_t = -χ_of_v_of_t * r_of_s^2 := by 
      rw [add_comm] at h3
      rw [← add_sub_assoc] at h3
      rw [← add_assoc] at h3
      have h4_1 : (1 : F) + (1 : F) = 2 := by ring
      rw [h4_1] at h3
      rw [add_comm] at h3
      rw [add_sub_assoc] at h3
      have h4_2 : (2 : F) - (2 : F) = 0 := by ring
      rw [h4_2, add_zero] at h3
      exact h3
    have h5 : χ_of_v_of_t = -χ_of_v_of_t := by 
      rw [h2] at h1
      change χ v_of_t q field_cardinality q_prime q_mod_4_congruent_3 * -χ_of_v_of_t = -1 at h1
      rw [h4] at h1
      rw [χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (-χ_of_v_of_t) (r_of_s ^ 2) q field_cardinality q_prime q_mod_4_congruent_3] at h1
      nth_rw 1 [← neg_one_mul] at h1
      rw [χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (-1) χ_of_v_of_t q field_cardinality q_prime q_mod_4_congruent_3] at h1
      rw [χ_of_neg_one_eq_neg_one q field_cardinality q_prime q_mod_4_congruent_3] at h1
      rw [χ_of_χ_of_a_eq_χ_of_a v_of_t q field_cardinality q_prime q_mod_4_congruent_3] at h1
      change -1 * χ_of_v_of_t * χ (r_of_s ^ 2) q field_cardinality q_prime q_mod_4_congruent_3 * -χ_of_v_of_t = -1 at h1
      have h5_1 : r_of_s^2 ≠ 0 := by 
        rw [pow_two]
        apply mul_ne_zero
        · apply r_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
        · apply r_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
      have h5_2 : IsSquare (r_of_s^2) := by 
        rw [pow_two]
        apply IsSquare.mul_self r_of_s
      rw [χ_a_eq_one (r_of_s^2) h5_1 h5_2 q field_cardinality q_prime q_mod_4_congruent_3] at h1
      rw [mul_one] at h1
      rw [neg_one_mul] at h1
      have h5_3 : χ_of_v_of_t ≠ 0 := χ_a_ne_zero v_of_t (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t) q field_cardinality q_prime q_mod_4_congruent_3
      rw [← mul_left_inj' h5_3] at h1
      change -χ_of_v_of_t * -χ_of_v_of_t * χ v_of_t q field_cardinality q_prime q_mod_4_congruent_3 = -1 * χ_of_v_of_t at h1
      rw [← one_over_χ_of_a_eq_χ_a v_of_t q field_cardinality q_prime q_mod_4_congruent_3] at h1
      change -χ_of_v_of_t * -χ_of_v_of_t * (1 / χ_of_v_of_t) = -1 * χ_of_v_of_t at h1
      rw [← inv_eq_one_div χ_of_v_of_t] at h1
      rw [← neg_one_mul] at h1
      ring_nf at h1
      rw [pow_two, mul_assoc] at h1
      rw [mul_inv_cancel₀ h5_3] at h1
      rw [mul_one] at h1
      exact h1
    have h6 : χ_of_v_of_t ≠ -χ_of_v_of_t := neg_χ_a_ne_χ_a v_of_t (v_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t) q field_cardinality q_prime q_mod_4_congruent_3
    contradiction

lemma x_ne_zero 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let x_of_t := x t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
  x_of_t ≠ (0 : F) := by 
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  change (c_of_s - 1) * s * X_of_t * (1 + X_of_t) / Y_of_t ≠ 0
  apply div_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · intro h1
          have h1_1 : c_of_s = 1 := by 
            rw [← add_left_inj 1] at h1
            rw [zero_add] at h1
            have h1_1_1 : (1 : F) - (1 : F) = 0 := by ring
            rw [add_comm] at h1
            rw [← add_sub_assoc] at h1
            rw [add_comm 1 c_of_s] at h1
            rw [add_sub_assoc] at h1
            rw [h1_1_1, add_zero] at h1
            exact h1
          have h1_2 : c_of_s ≠ 1 := c_ne_one s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
          contradiction
        · apply s_h1
      · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
    · apply one_add_X_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
  · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t

theorem y_add_one_ne_zero
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
  y_of_t + 1 ≠ (0 : F) := by 
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
    intro y_of_t
    intro h
    have h1 : y_of_t = -1 := by 
      rw [← add_left_inj (-1)] at h
      have h1_1 : (1 : F) + (-1 : F) = 0 := by ring
      rw [add_assoc] at h
      rw [h1_1] at h
      rw [add_zero, zero_add] at h
      exact h
    have h2 : (r_of_s * X_of_t - (1 + X_of_t)^2) / (r_of_s * X_of_t + (1 + X_of_t)^2) = -1 := by 
      change y_of_t = -1
      exact h1
    have h3 : r_of_s * X_of_t - (1 + X_of_t)^2 = -(r_of_s * X_of_t + (1 + X_of_t)^2) := by
      have h3_1 : (r_of_s * X_of_t + (1 + X_of_t)^2) ≠ 0 := y_divisor_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
      rw [← div_left_inj' h3_1]
      rw [← neg_one_mul]
      rw [mul_div_assoc]
      rw [div_self h3_1]
      rw [mul_one]
      exact h2
    have h4 : r_of_s * X_of_t = 0 := by 
      rw [← add_left_inj (r_of_s * X_of_t + (1 + X_of_t) ^ 2)] at h3
      ring_nf at h3
      rw [← div_left_inj' (two_ne_zero q field_cardinality q_prime q_mod_4_congruent_3)] at h3
      rw [mul_div_assoc] at h3
      rw [div_self (two_ne_zero q field_cardinality q_prime q_mod_4_congruent_3)] at h3
      ring_nf at h3
      exact h3
    have h5 : r_of_s * X_of_t ≠ 0 := by 
      apply mul_ne_zero
      · apply r_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
      · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
    contradiction

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
  intro t
  use y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3

-- Chapter 3.2 Theorem 1
theorem u_mul_v_mul_X_mul_Y_mul_x_mul_y_add_one_ne_zero
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
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  u t * v_of_t * X_of_t  * Y_of_t * x_of_t * (y_of_t + 1) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · apply mul_ne_zero
            · apply u_ne_zero t
            · apply v_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
          · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
        · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
      · apply x_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
    · apply y_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t

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
  Y_of_t ^2 = X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t := by
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
    let u_of_t := u t
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
    let χ_of_v_of_t := χ v_of_t q field_cardinality q_prime q_mod_4_congruent_3
    intro r_of_s X_of_t Y_of_t
    have h1 : X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t = χ_of_v_of_t * v_of_t := by
      calc
      X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t = χ_of_v_of_t * (u_of_t^5 + (r_of_s^2 -2 ) * u_of_t^3 + u_of_t) := by 
        change (χ_of_v_of_t * u_of_t) ^ 5 + (r_of_s ^ 2 - 2) * (χ_of_v_of_t * u_of_t) ^ 3 + (χ_of_v_of_t * u_of_t) = χ_of_v_of_t * (u_of_t^5 + (r_of_s^2 -2 ) * u_of_t^3 + u_of_t)
        rw [mul_pow (χ_of_v_of_t) (u_of_t) 5]
        rw [mul_pow (χ_of_v_of_t) (u_of_t) 3]
        have h1_1 : Odd 5 := by 
          apply Nat.odd_iff.2
          norm_num
        have h1_2 : Odd 3 := by 
          apply Nat.odd_iff.2
          norm_num
        rw [χ_of_a_pow_n_eq_χ_a v_of_t ⟨5, h1_1⟩ q field_cardinality q_prime q_mod_4_congruent_3]
        rw [χ_of_a_pow_n_eq_χ_a v_of_t ⟨3, h1_2⟩ q field_cardinality q_prime q_mod_4_congruent_3]
        change χ_of_v_of_t * u_of_t^5 + (r_of_s ^ 2 - 2) * (χ_of_v_of_t * u_of_t^3) + (χ_of_v_of_t * u_of_t) = χ_of_v_of_t * (u_of_t^5 + (r_of_s^2 -2 ) * u_of_t^3 + u_of_t)
        ring_nf
      _ = χ_of_v_of_t * v_of_t := by 
        change χ_of_v_of_t * v_of_t = χ_of_v_of_t * v_of_t
        rfl
    have h2 : IsSquare (χ_of_v_of_t * v_of_t) := by
      sorry
    have h3 : (χ_of_v_of_t * v_of_t)^((q + 1) / 2) = χ_of_v_of_t * v_of_t := by 
      apply square_of_a ⟨(χ_of_v_of_t * v_of_t), h2⟩ q field_cardinality q_prime q_mod_4_congruent_3
    rw [h1]
    let χ_of_sum := χ ((u t)^2 + 1 / c_of_s^2) q field_cardinality q_prime q_mod_4_congruent_3
    change ((χ_of_v_of_t * v_of_t)^((q + 1) / 4) * χ_of_v_of_t * χ_of_sum)^2 = χ_of_v_of_t * v_of_t
    sorry

lemma y_divisor_ne_zero 
  (s : F)
  (s_h1 : s ≠ 0) 
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Nat.Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
  (r_of_s * X_of_t + (1 + X_of_t)^2) ≠ 0 := by
    let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
    intro r_of_s
    intro X_of_t
    intro h
    have h1 : r_of_s * X_of_t = -(1 + X_of_t)^2 := by 
      rw [← add_left_inj ((1 + X_of_t)^2)]
      have h1_1 : -((1 + X_of_t)^2) + ((1 + X_of_t)^2) = 0 := by 
        rw [neg_add_eq_zero.2]
        ring
      rw [h1_1]
      exact h
    have h2 : (r_of_s^2 + 4 * r_of_s) * X_of_t^2 = X_of_t^4 - 2 * X_of_t^2 + 1 := by
      ring_nf
      repeat rw [pow_two]
      repeat rw [← mul_assoc]
      rw [mul_assoc r_of_s r_of_s X_of_t]
      nth_rw 2 [mul_comm r_of_s X_of_t]
      rw [← mul_assoc]
      rw [h1]
      rw [mul_assoc (-(1 + X_of_t)^2) r_of_s X_of_t]
      rw [h1]
      ring_nf
    have h3 : Y_of_t^2 = -(1 + X_of_t)^2 * X_of_t^2 * (s + 2 / s)^2 := by 
      calc 
        Y_of_t^2 = X_of_t * (X_of_t^4 + (r_of_s^2 - 2) * X_of_t^2 + 1) := by 
          rw [mul_add, mul_one]
          rw [mul_add]
          rw [map_fulfills_specific_equation t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3]
          ring_nf
          change X_of_t - X_of_t ^ 3 * 2 + X_of_t ^ 3 * r_of_s ^ 2 + X_of_t ^ 5 = X_of_t - X_of_t ^ 3 * 2 + X_of_t ^ 3 * r_of_s ^ 2 + X_of_t ^ 5
          rfl
        _ = X_of_t^3 * (2 * r_of_s^2 + 4 * r_of_s) := by 
          rw [sub_mul (r_of_s^2) 2 (X_of_t^2)]
          nth_rw 1 [pow_two]
          nth_rw 1 [pow_two]
          rw [← mul_assoc, mul_assoc r_of_s r_of_s X_of_t, mul_comm r_of_s X_of_t]
          rw [← mul_assoc]
          rw [h1, mul_assoc (-(1 + X_of_t)^2) r_of_s X_of_t, h1]
          rw [← neg_one_mul]
          have h3_1 : (-1 : F) * (-1) = 1 := by ring
          nth_rw 1 [mul_comm (-1) ((1 + X_of_t)^2), ← mul_assoc, mul_assoc ((1 + X_of_t)^2) (-1) (-1)]
          rw [h3_1, mul_one]
          have h3_2 : 2 + 2 = 4 := by norm_num
          rw [← pow_add (1 + X_of_t) 2 2]
          rw [h3_2]
          rw [← add_sub_assoc, add_comm (X_of_t^4) ((1 + X_of_t)^4)]
          rw [add_sub_assoc ((1 + X_of_t)^4) (X_of_t^4)]
          rw [add_assoc ((1 + X_of_t)^4) (X_of_t^4 - 2 * X_of_t^2) (1 : F)]
          rw [← h2]
          have h3_3 : -r_of_s * X_of_t = (1 + X_of_t)^2 := by 
            rw [← neg_one_mul]
            rw [← mul_right_inj' (neg_one_ne_zero q field_cardinality q_prime q_mod_4_congruent_3)]
            rw [← mul_assoc, ← mul_assoc, h3_1, one_mul, neg_one_mul]
            exact h1
          rw [← h3_2, pow_add (1 + X_of_t) 2 2, ← h3_3]
          rw [← pow_two] 
          ring_nf
        _ = r_of_s * X_of_t * X_of_t^2 * (2 * r_of_s + 4) := by ring_nf
        _ = -(1 + X_of_t)^2 * X_of_t^2 * (s + 2 / s)^2 := by 
          rw [← h1]
          change r_of_s * X_of_t * X_of_t ^ 2 * (2 * (c_of_s + 1 / c_of_s) + 4) = r_of_s * X_of_t * X_of_t ^ 2 * (s + 2 / s) ^ 2 
          change r_of_s * X_of_t * X_of_t ^ 2 * (2 * (2 / s^2 + 1 / (2 / s^2)) + 4) = r_of_s * X_of_t * X_of_t ^ 2 * (s + 2 / s) ^ 2 
          have h3_4 : (2 * (2 / s^2 + 1 / (2 / s^2)) + 4) = (s + 2 / s)^2 := by 
            ring_nf
            rw [inv_inv, mul_inv_cancel₀ s_h1, one_mul]
            rw [mul_assoc _ 2⁻¹ 2]
            rw [inv_mul_cancel₀ (two_ne_zero q field_cardinality q_prime q_mod_4_congruent_3)]
            ring_nf
          rw [h3_4]
    have h4 : IsSquare (-1 : F) := by
      have h4_1 : Y_of_t^2 / ((1 + X_of_t) * X_of_t * (s + 2 / s))^2 = -1 := by 
        rw [← neg_one_mul] at h3
        rw [mul_assoc (-1) ((1 + X_of_t)^2) (X_of_t^2)] at h3
        rw [← mul_pow (1 + X_of_t) (X_of_t) 2] at h3
        rw [mul_assoc (-1) (((1 + X_of_t) * X_of_t)^2) _] at h3
        rw [← mul_pow (((1 + X_of_t) * X_of_t))] at h3
        have h4_1_1 : ((1 + X_of_t) * X_of_t * (s + 2 / s))^2 ≠ 0 := by 
          apply pow_ne_zero 2
          apply mul_ne_zero
          · apply mul_ne_zero
            · apply one_add_X_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
            · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
          · intro h4_1_2
            rw [← mul_right_inj' s_h1] at h4_1_2
            ring_nf at h4_1_2
            rw [mul_inv_cancel₀ s_h1, one_mul] at h4_1_2
            rw [add_comm] at h4_1_2
            have h4_1_2_1 : s^2 + 2 = 0 := by 
              exact h4_1_2
            have h4_1_2_2 : (s^2 - 2) * (s^2 + 2) = 0 := by 
              rw [h4_1_2_1, mul_zero]
            contradiction
        rw [← div_left_inj' h4_1_1] at h3
        rw [mul_div_assoc] at h3
        rw [div_self h4_1_1, mul_one] at h3
        exact h3
      have h4_2 : (Y_of_t / ((1 + X_of_t) * X_of_t * (s + 2 / s)))^2 = -1 := by 
        rw [← div_pow] at h4_1
        exact h4_1
      rw [← h4_2]
      rw [pow_two]
      apply IsSquare.mul_self
    have h5 : q % 4 ≠ 3 := by 
      rw [FiniteField.isSquare_neg_one_iff] at h4
      rw [field_cardinality] at h4
      exact h4
    contradiction

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
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
  x_of_t^2 + y_of_t^2 = 1 + d_of_s * x_of_t^2 * y_of_t^2 := by
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
    let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
    let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3;
    intro x_of_t y_of_t d_of_s
    have h1 : (c_of_s - 1)^2 * s^2 = 2 * (r_of_s - 2):= 
      calc
        (c_of_s - 1)^2 * s^2 = (c_of_s - 1)^2 * (2 / c_of_s) := by 
          have h1_1 : s^2 = 2 / c_of_s := by 
            change s^2 = 2 / (2 / s^2)
            ring_nf
            rw [inv_inv]
            rw [mul_assoc]
            rw [inv_mul_cancel₀ (two_ne_zero q field_cardinality q_prime q_mod_4_congruent_3), mul_one]
          rw [h1_1]
        _ = 2 * (r_of_s - 2) := by 
          rw [sub_pow_two, mul_one, one_pow 2]
          rw [add_mul, sub_mul]
          rw [← mul_div_assoc]
          rw [one_mul]
          rw [mul_comm, pow_two, ← mul_assoc]
          rw [mul_div_assoc, div_self (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3), mul_one]
          nth_rw 4 [← mul_one 2]
          rw [add_comm, ← add_sub_assoc]
          rw [mul_div_assoc, ← mul_add 2 (1 / c_of_s) c_of_s, add_comm]
          change 2 * r_of_s - 2 * c_of_s * (2 / c_of_s) = 2 * (r_of_s - 2)
          ring_nf
          rw [mul_inv_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3)]
          ring_nf
    have h2 : Y_of_t^2 * (1 - x_of_t^2) = X_of_t * (r_of_s * X_of_t - (1 + X_of_t)^2)^2 := by 
      calc 
        Y_of_t^2 * (1 - x_of_t^2) = Y_of_t^2 - (c_of_s - 1)^2 * s^2 * X_of_t^2 * (1 + X_of_t)^2 := by 
          change Y_of_t^2 * (1 - (((c_of_s - 1) * s * X_of_t * (1 + X_of_t)) / Y_of_t)^2) = Y_of_t^2 - (c_of_s - 1)^2 * s^2 * X_of_t^2 * (1 + X_of_t)^2
          rw [mul_sub, mul_one]
          have h2_1 : Y_of_t^2 ≠ 0 := by
            rw [pow_two]
            apply mul_ne_zero
            · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
            · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
          rw [div_pow, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self h2_1]
          ring_nf
       _ = X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t - 2 * (r_of_s - 2) * X_of_t^2 * (1 + X_of_t)^2 := by 
          rw [h1, map_fulfills_specific_equation t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3]
       _ = X_of_t * (r_of_s * X_of_t - (1 + X_of_t)^2)^2 := by 
          ring_nf
    have h3 : -d_of_s = (r_of_s + 2) / (r_of_s - 2) := by 
      calc 
        -d_of_s = (c_of_s + 2 + 1 / c_of_s) / (c_of_s - 2 + 1 / c_of_s) := by 
          change -(-(c_of_s + 1)^2 / (c_of_s - 1)^2) = (c_of_s + 2 + 1 / c_of_s) / (c_of_s - 2 + 1 / c_of_s)
          rw [← neg_one_mul]
          nth_rw 2 [← neg_one_mul]
          rw [mul_div_assoc, ← mul_assoc]
          rw [add_pow_two, sub_pow_two]
          have h3_1 : 1 / c_of_s ≠ 0 := by 
            rw [← inv_eq_one_div]
            apply inv_ne_zero
            apply c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
          have h3_2 : (1 / c_of_s) / (1 / c_of_s) = 1 := by 
            rw [div_self h3_1]
          have h3_3 : (-1 : F) * (-1) = 1 := by ring
          rw [h3_3]
          nth_rw 1 [← h3_2]
          rw [← mul_div_mul_comm]
          rw [mul_add, mul_add, mul_add, mul_sub, pow_two, ← mul_assoc]
          rw [← inv_eq_one_div, inv_mul_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3), one_mul]
          rw [mul_one, ← mul_assoc, mul_comm, ← mul_assoc]
          rw [mul_inv_cancel₀ (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3), one_mul]
          ring_nf 
        _ = (r_of_s + 2) / (r_of_s - 2) := by 
          rw [add_assoc, add_comm 2 (1 / c_of_s), ← add_assoc]
          nth_rw 3 [add_comm]
          rw [← add_sub_assoc]
          nth_rw 3 [add_comm]
          change (r_of_s + 2) / (r_of_s - 2) = (r_of_s + 2) / (r_of_s - 2)
          rfl
    have h4 : -d_of_s * (c_of_s - 1)^2 * s^2 = 2 * (r_of_s + 2) := by 
      rw [h3, mul_assoc, h1]
      rw [mul_comm, ← mul_div_assoc, mul_assoc, mul_comm (r_of_s - 2) (r_of_s + 2), ← mul_assoc]
      have h4_1 : r_of_s - 2 ≠ 0 := by 
        intro h4_1_1
        have h4_1_2 : (c_of_s - 1) ^ 2 * s ^ 2 = 0 := by
          rw [h4_1_1, mul_zero] at h1
          exact h1
        have h4_1_3 : (c_of_s - 1) ^ 2 * s ^ 2 ≠ 0 := by 
          apply mul_ne_zero
          · apply pow_ne_zero 2
            exact c_sub_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
          · apply pow_ne_zero 2
            apply s_h1
        contradiction
      rw [mul_div_assoc, div_self h4_1, mul_one] 
    have h5 : Y_of_t^2 * (1 - d_of_s * x_of_t^2) = X_of_t * (r_of_s * X_of_t + (1 + X_of_t)^2)^2 := by 
      calc 
        Y_of_t^2 * (1 - d_of_s * x_of_t^2) = Y_of_t^2 - d_of_s * (c_of_s - 1)^2 * s^2 * X_of_t^2 * (1 + X_of_t)^2 := by 
          change Y_of_t^2 * (1 - d_of_s * (((c_of_s - 1) * s * X_of_t * (1 + X_of_t)) / Y_of_t)^2) = Y_of_t^2 - d_of_s * (c_of_s - 1)^2 * s^2 * X_of_t^2 * (1 + X_of_t)^2 
          rw [mul_sub, mul_one]
          have h2_1 : Y_of_t^2 ≠ 0 := by
            rw [pow_two]
            apply mul_ne_zero
            · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
            · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
          rw [div_pow, ← mul_assoc, mul_comm (Y_of_t^2), ← mul_div_assoc, mul_assoc]
          rw [mul_comm (Y_of_t ^ 2) (((c_of_s - 1) * s * X_of_t * (1 + X_of_t)) ^ 2)]
          rw [← mul_assoc, mul_div_assoc, div_self h2_1]
          ring_nf
       _ = X_of_t^5 + (r_of_s^2 - 2) * X_of_t^3 + X_of_t + 2 * (r_of_s + 2) * X_of_t^2 * (1 + X_of_t)^2 := by 
          rw [← neg_add_eq_sub, ← neg_one_mul] 
          rw [← mul_assoc (-1 : F)]
          rw [← mul_assoc (-1 : F)]
          rw [← mul_assoc (-1 : F)]
          rw [← mul_assoc (-1 : F)]
          rw [neg_one_mul]
          rw [add_comm]
          rw [h4]
          rw [map_fulfills_specific_equation t s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3]
       _ = X_of_t * (r_of_s * X_of_t + (1 + X_of_t)^2)^2 := by 
          ring_nf
    have h6 : (1 - d_of_s * x_of_t^2) ≠ 0 := by 
      intro h6_1
      have h6_2 : IsSquare d_of_s := by 
        rw [← add_right_inj (d_of_s * x_of_t^2), add_comm] at h6_1 
        have h6_2_1 : 1 - d_of_s * x_of_t ^ 2 + d_of_s * x_of_t ^ 2 = 1 := by ring
        rw [add_zero, h6_2_1] at h6_1
        have h6_2_2 : x_of_t^2 ≠ 0 := by
          rw [pow_two]
          apply mul_ne_zero
          · apply x_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
          · apply x_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
        rw [← div_left_inj' h6_2_2] at h6_1
        rw [mul_div_assoc, div_self h6_2_2, mul_one] at h6_1
        rw [← mul_one 1, ← pow_two, ← div_pow _ _ 2] at h6_1 
        rw [← h6_1, pow_two]
        apply IsSquare.mul_self
      have h6_3 : ¬IsSquare d_of_s := by exact d_nonsquare s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3
      contradiction
    have h7 : Y_of_t^2 * (1 - d_of_s * x_of_t^2) ≠ 0 := by 
      apply mul_ne_zero
      · rw [pow_two]
        apply mul_ne_zero
        · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
        · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
      · exact h6
    have h8 : (1 - x_of_t^2) / (1 - d_of_s * x_of_t^2) = y_of_t^2 := by
      calc
        (1 - x_of_t^2) / (1 - d_of_s * x_of_t^2) = (r_of_s * X_of_t - (1 + X_of_t)^2)^2 / (r_of_s * X_of_t + (1 + X_of_t)^2)^2 := by 
          have h8_1 : Y_of_t^2 / Y_of_t^2 = 1 := by 
            have h7_2 : Y_of_t^2 ≠ 0 := by
              rw [pow_two]
              apply mul_ne_zero
              · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
              · apply Y_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t
            rw [div_self h7_2]
          nth_rw 1 [← one_mul (1 - x_of_t ^ 2), ← h8_1]
          rw [mul_div_assoc, ← mul_div_mul_comm]
          rw [h2, h5]
          rw [mul_div_mul_comm X_of_t _ X_of_t _]
          rw [div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime q_mod_4_congruent_3 t)]
          rw [one_mul] 
        _ = y_of_t^2 := by 
          rw [← div_pow _ _ 2] 
          change y_of_t^2 = y_of_t^2
          rfl
    rw [← mul_right_inj' h6] at h8
    rw [← mul_div_assoc, mul_comm, mul_div_assoc, div_self h6, mul_one] at h8
    rw [sub_mul, one_mul] at h8 
    rw [← add_left_inj (x_of_t^2)] at h8
    rw [← add_left_inj (y_of_t^2 * x_of_t^2 * d_of_s)] at h8
    ring_nf at h8
    symm at h8
    rw [mul_assoc (d_of_s) (x_of_t ^ 2) (y_of_t ^ 2), mul_comm (d_of_s) (x_of_t ^ 2 * y_of_t ^ 2)]
    exact h8

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

