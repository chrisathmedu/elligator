import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
import Elligator.Elligator1.Sets
import Elligator.Elligator1.sProperties
import Elligator.Elligator1.cProperties
import Elligator.Elligator1.dProperties
import Elligator.Elligator1.uProperties
import Elligator.Elligator1.vProperties
import Elligator.Elligator1.XProperties
import Elligator.Elligator1.YProperties
import Elligator.Elligator1.xProperties
import Elligator.Elligator1.yProperties

namespace Elligator.Elligator1

section phiProperties

variable {F : Type*} [Field F] [Fintype F]

lemma ϕ_of_t_eq_ϕ_of_neg_t_base_case
  (t : { t : F // t = 1 ∨ t = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_t := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let ϕ_of_neg_t := ϕ (-t.val) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_of_t = ϕ_of_neg_t := by
    rcases t.property with h2_1 | h2_1
    · change ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 = ϕ (-t.val) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      rw [h2_1]
      unfold ϕ
      simp
    · change ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 = ϕ (-t.val) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      rw [h2_1]
      unfold ϕ
      simp

lemma ϕ_of_t_eq_ϕ_of_neg_t_main_case
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_t := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let ϕ_of_neg_t := ϕ (-t.val) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_of_t = ϕ_of_neg_t := by
    let t1 := t.val
    let t2 := -t.val
    have h2_2 : (t2 ≠ 1 ∧ t2 ≠ -1) := by
      unfold t2
      rw [ne_eq, ne_eq]
      constructor
      · intro h2_2_1
        have h2_2_1_1 : t1 = -1 := by
          rw [← neg_one_mul]
          nth_rw 2 [← h2_2_1]
          unfold t1
          simp
        have h2_2_1_2 : t.val ≠ -1 := by exact t.property.right
        contradiction
      · intro h2_2_2
        have h2_2_1_1 : t.val = 1 := by
          simp at h2_2_2
          exact h2_2_2
        have h2_2_1_2 : t.val ≠ 1 := by exact t.property.left
        contradiction
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let u1 := u t q field_cardinality q_prime_power q_mod_4_congruent_3
    let v1 := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let v2 := v ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let x1 := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let x2 := x ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let y1 := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let y2 := y ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let x1 := x t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let x2 := x ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let y1 := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let y2 := y ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have h2_10 : y2 = y1 := by exact y_comparison t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t.property h2_2
    have h2_12 : x2 = x1 := by exact x_comparison t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t.property h2_2
    change ϕ t1 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 = ϕ t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold ϕ
    rw [dif_pos h2_2, dif_pos t.property]
    change (x1, y1) = (x2, y2)
    rw [h2_10, h2_12]

-- Original: Theorem 3.1 forward statement, Proof A
lemma ϕ_of_t_eq_ϕ_of_neg_t
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
  ϕ_of_t = ϕ_of_neg_t := by
    intro ϕ_of_t ϕ_of_neg_t
    by_cases h2 : t = 1 ∨ t = -1
    · exact ϕ_of_t_eq_ϕ_of_neg_t_base_case ⟨t, h2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · have h2_1 : (t ≠ 1 ∧ t ≠ -1) := by
        rw [ne_eq, ne_eq]
        rw [← not_or]
        exact h2
      exact ϕ_of_t_eq_ϕ_of_neg_t_main_case ⟨t, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

-- Original: Theorem 3 Proof B latter part
lemma ϕ_inv_only_two_specific_preimages_mpr
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
  ¬ ∃ (w : { n : F // n ≠ t ∧ n ≠ -t}), ϕ w.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 = ϕ_of_t := by
    intro ϕ_of_t h1
    sorry

lemma point_in_ϕ_over_F_with_prop1_base_case
  (t : {n : F // n = 1 ∨ n = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop1 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop1 
    intro y
    have h1 : ¬ (t.val ≠ 1 ∧ t.val ≠ -1) := by
      rcases t.property with h1_1 | h1_1
      · rw [h1_1]
        simp
      · rw [h1_1]
        simp
    unfold y point ϕ 
    rw [dif_neg h1]
    ring_nf
    exact (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)

lemma point_in_ϕ_over_F_with_prop1_main_case
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop1 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop1
    intro y
    unfold y point ϕ
    rw [dif_pos t.property]
    exact y_add_one_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t

-- Original: Theorem 3.3 Proof B prop 1 argumentation
lemma point_in_ϕ_over_F_with_prop1
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop1 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop1
    intro y
    by_cases h1 : t ≠ 1 ∧ t ≠ -1
    · exact point_in_ϕ_over_F_with_prop1_main_case ⟨t, h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · have h1_1 : (t = 1 ∨ t = -1) := by
        rw [ne_eq, ne_eq] at h1
        rw [← not_or, not_not] at h1
        exact h1
      exact point_in_ϕ_over_F_with_prop1_base_case ⟨t, h1_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

lemma point_in_ϕ_over_F_with_prop2_base_case
  (t : {n : F // n = 1 ∨ n = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop2  
    intro r_of_s η_of_point
    have h1 : ¬ (t.val ≠ 1 ∧ t.val ≠ -1) := by
      rcases t.property with h1_1 | h1_1
      · rw [h1_1]
        simp
      · rw [h1_1]
        simp
    unfold η_of_point η point ϕ 
    rw [dif_neg h1]
    ring_nf
    rw [isSquare_iff_exists_sq 0]
    use 0
    simp

lemma point_in_ϕ_over_F_with_prop2_main_case
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop2  
    intro r_of_s η_of_point
    let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    have h1 : X_of_t^2 + 2 * (1 + η_of_point * r_of_s) * X_of_t + 1 = 0 := by
      exact (y_h2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
    have h2 : NeZero (2 : F) := by
      rw [neZero_iff]
      apply (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)
    rw [pow_two] at h1
    nth_rw 1 [← one_mul X_of_t, mul_assoc] at h1
    apply (@quadratic_eq_zero_iff_discrim_eq_sq F _ 1 (2 * (1 + η_of_point * r_of_s)) 1 h2 _ (FiniteFieldBasic.one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3) X_of_t).mp at h1
    unfold discrim at h1
    rw [mul_pow 2 _ 2] at h1
    have h3 : 2^2 = (4 : F) := by norm_num
    rw [mul_one, h3, ← mul_sub, mul_comm] at h1
    rw [← div_left_inj' (FiniteFieldBasic.four_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h1
    rw [mul_div_assoc, div_self (FiniteFieldBasic.four_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h1
    rw [mul_one, ← h3, ← div_pow _ _ 2] at h1
    rw [h1]
    apply IsSquare.sq

-- Original: Theorem 3.3 Proof B prop 2 argumentation
lemma point_in_ϕ_over_F_with_prop2
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop2
    intro y
    by_cases h1 : t ≠ 1 ∧ t ≠ -1
    · exact point_in_ϕ_over_F_with_prop2_main_case ⟨t, h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · have h1_1 : (t = 1 ∨ t = -1) := by
        rw [ne_eq, ne_eq] at h1
        rw [← not_or, not_not] at h1
        exact h1
      exact point_in_ϕ_over_F_with_prop2_base_case ⟨t, h1_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

lemma point_in_ϕ_over_F_with_prop3_base_case
  (t : {n : F // n = 1 ∨ n = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop3
    intro x c_of_s χ_of_c_of_s r_of_s η_of_point h1
    have h2 : ¬ (t.val ≠ 1 ∧ t.val ≠ -1) := by
      rcases t.property with h2_1 | h2_1
      · rw [h2_1]
        simp
      · rw [h2_1]
        simp
    unfold η_of_point η point ϕ at h1
    rw [dif_neg h2] at h1
    ring_nf at h1
    simp at h1
    have h3 : (2 : F) ≠ 0 := by apply FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    contradiction 

lemma point_in_ϕ_over_F_with_prop3_main_case
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop3
    intro x_of_point c_of_s χ_of_c_of_s r_of_s η_of_point h1
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_c_of_s := LegendreSymbol.χ c_of_s q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v_of_s := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold x_of_point point ϕ 
    rw [dif_pos t.prop]
    unfold x
    simp
    change (c_of_s - 1) * s * X_of_t * (1 + X_of_t) / Y_of_t = 2 * s * (c_of_s - 1) * χ_of_c_of_s / r_of_s
    unfold X_of_t Y_of_t
    rw [(X_η_h2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h1)]
    rw [(Y_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h1)]
    simp
    nth_rw 2 [mul_div_assoc] 
    unfold χ_of_c_of_s 
    nth_rw 2 [← LegendreSymbol.one_over_χ_of_a_eq_χ_a c_of_s q field_cardinality q_prime_power q_mod_4_congruent_3]
    change (c_of_s - 1) * s * (1 + 1) / (r_of_s * χ_of_c_of_s) = 2 * s * (c_of_s - 1) * (1 / χ_of_c_of_s / r_of_s)
    ring_nf

-- Original: Theorem 3.3 Proof B prop 3 argumentation
lemma point_in_ϕ_over_F_with_prop3
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point := by
    intro point
    unfold ϕ_over_F_prop3
    intro y
    by_cases h1 : t ≠ 1 ∧ t ≠ -1
    · exact point_in_ϕ_over_F_with_prop3_main_case ⟨t, h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · have h1_1 : (t = 1 ∨ t = -1) := by
        rw [ne_eq, ne_eq] at h1
        rw [← not_or, not_not] at h1
        exact h1
      exact point_in_ϕ_over_F_with_prop3_base_case ⟨t, h1_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

-- Implicated by main case of Theorem 3 Proof part B
lemma ϕ_of_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_of_zero := ϕ (0 : F) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let χ_of_c_of_s  := (LegendreSymbol.χ c_of_s q field_cardinality q_prime_power q_mod_4_congruent_3)
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_of_zero  = (2 * (c_of_s - 1) * s * χ_of_c_of_s / r_of_s, (r_of_s - 4) / (r_of_s + 4)) := by
    intro ϕ_of_zero c_of_s χ_of_c_of_s r_of_s 
    unfold ϕ_of_zero ϕ
    let h1 := FiniteFieldBasic.zero_h1 q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [dif_pos h1]
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 ϕ_of_zero 
    have h2 : η_of_point * r_of_s = -2 := by
      unfold η_of_point η ϕ_of_zero ϕ
      rw [dif_pos h1]
      let y_of_t := y ⟨(0 : F), h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
      let X_of_zero := X ⟨(0 : F), h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
      change (y_of_t - 1) / (2 * (y_of_t + 1)) * r_of_s = -2 
      -- This has to be proven again here as in y_η_h1 and X_η_h1 since 
      -- the lemmas itself do not help with concret t values
      unfold y_of_t
      rw [(y_of_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)]
      change ((r_of_s - 4) / (r_of_s + 4) - 1) / (2 * ((r_of_s - 4) / (r_of_s + 4) + 1)) * r_of_s = -2 
      have h2_2 : 1 = (r_of_s + 4) / (r_of_s + 4) := by 
        rw [add_comm]
        rw [div_self (four_add_r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)]
      nth_rw 1 [h2_2]
      nth_rw 1 [h2_2]
      rw [← sub_div, ← add_div, ← sub_sub, ← add_assoc]
      ring_nf
      rw [inv_inv, mul_comm r_of_s, mul_assoc _ r_of_s, mul_inv_cancel₀ (r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3), mul_one]
      rw [inv_mul_cancel₀ (four_add_r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3), one_mul]
      rw [← mul_neg_one, ← mul_right_inj' (FiniteFieldBasic.four_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)]
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (FiniteFieldBasic.four_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)]
      ring_nf
    rw [y_η_h1 ⟨0, h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2]
    let x_of_t := ϕ_of_zero.1
    have h3 : x_of_t = 2 * s * (c_of_s - 1) * χ_of_c_of_s / r_of_s := by
      apply point_in_ϕ_over_F_with_prop3 (0 : F) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      exact h2
    unfold x_of_t ϕ_of_zero ϕ at h3
    rw [dif_pos h1] at h3
    simp at h3
    rw [h3]
    change (2 * s * (c_of_s - 1) * χ_of_c_of_s / r_of_s, (r_of_s - 4) / (r_of_s + 4)) = (2 * (c_of_s - 1) * s * χ_of_c_of_s / r_of_s, (r_of_s - 4) / (r_of_s + 4))
    ring_nf

-- Original: Theorem 3 Proof B
lemma point_in_E_over_F_with_props_iff_point_in_ϕ_over_F_mp
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  :
  ((h : point.val ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) →
    ϕ_over_F_prop1 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
    ∧ ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
    ∧ ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val)
    → point.val ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 := by
    sorry

-- Original: Theorem 3 Proof B
lemma point_in_E_over_F_with_props_iff_point_in_ϕ_over_F_mpr
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  :
  point.val ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 
  → ((h : point.val ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) →
    ϕ_over_F_prop1 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
    ∧ ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
    ∧ ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val)
  := by
    sorry

-- Original: Theorem 3 Proof B and C
lemma point_in_E_over_F_with_props_iff_point_in_ϕ_over_F
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  :
  ((h : point.val ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) →
    ϕ_over_F_prop1 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
    ∧ ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
    ∧ ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val)
  ↔ point.val ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 := by
    constructor
    · exact point_in_E_over_F_with_props_iff_point_in_ϕ_over_F_mp s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    · exact point_in_E_over_F_with_props_iff_point_in_ϕ_over_F_mpr s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point

-- Used to build definitions for arguments which sometimes require different
-- assumptions regarding group membership.
lemma E_over_F_subset_ϕ_over_F
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let E_over_F_of_s := E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let ϕ_over_F_q_of_s := ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  E_over_F_of_s ⊆ ϕ_over_F_q_of_s := by sorry

lemma point_in_E_over_F
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  :
  let E_over_F_of_s := E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  point.val ∈ E_over_F_of_s
  := by sorry

/-- `invmap_representative` is ...

Paper definition at chapter 3.3 Theorem 3.3.
-/
lemma invmap_representative_base_case
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (t' : { n : F // n = 1 ∨ n = -1})
  (representative : t'.val = t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  :
  let ϕ_of_t' := ϕ t'.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_of_t' = (0, 1) := by
    intro ϕ_of_t'
    unfold ϕ_of_t'
    --rw [t'.property.left]
    rcases t'.property with h1_1 | h1_1
    · rw [h1_1]
      unfold ϕ 
      simp
    · rw [h1_1]
      unfold ϕ 
      simp

/-- `invmap_representative` is ...

Paper definition at chapter 3.3 Theorem 3.3.
-/
lemma invmap_representative_main_case
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : (F) × (F) // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (t' : { n : F // n ≠ 1 ∧ n ≠ -1})
  (representative : t'.val = t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  :
  let ϕ_of_t' := ϕ t'.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x_of_t' := x t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let y_of_t' := y t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  ϕ_of_t' = (x_of_t', y_of_t') := by
    intro ϕ_of_t' x_of_t' y_of_t'
    unfold ϕ_of_t' ϕ
    rw [dif_pos t'.property]

-- TODO how to get invmap_representative* theorems into one theorem handling both
-- cases? This currently fails since the rhs is not settable to (0,1) and (x,y)
-- by case or rather derivable as such depending on the t case.

