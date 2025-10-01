import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.InjectiveMap
import Elligator.Elligator1.Common

variable {F : Type*} [Field F] [Fintype F]

lemma u_comparison
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let t1 := t
  let t2 := -t1
  let u1 := u ⟨t1, h2_1⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
  let u2 := u ⟨t2, h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
  u2 = 1 / u1 := by
    intro t1 t2 u1 u2
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      u2 = (1 - t2) / (1 + t2) := by
        unfold u2 u
        simp
     _ = (1 + t) / (1 - t) := by
       unfold t2 t1
       simp
       ring_nf
     _ = 1 / u1 := by
       unfold u1 u
       simp
       unfold t1
       rfl

lemma v_comparison
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let t1 := t
  let t2 := -t1
  let u1 := u ⟨t1, h2_1⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
  let v2 := v ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  v2 = 1 / u1^5 + (r_of_s^2 - 2) * 1 / u1^3 + 1 / u1 := by
    intro t1 t2 u1 v2 r_of_s
    let u2 := u ⟨t2, h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      v2 = u2^5 + (r_of_s^2 - 2) * u2^3 + u2 := by
        unfold v2 v u2
        rfl
      _ = 1 / u1^5 + (r_of_s^2 - 2) * 1/ u1^3 + 1 / u1 := by
        unfold u2 u1 t2 t1
        rw [u_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
        ring_nf

lemma v_comparison_implication1
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let t1 := t
  let t2 := -t1
  let u1 := u ⟨t1, h2_1⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
  let v1 := v ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let v2 := v ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  v2 * u1^6 = v1 := by
    intro t1 t2 u1 v1 v2
    let u2 := u ⟨t2, h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      v2 * u1^6 = u1 + (r_of_s^2 - 2) * u1^3 + u1^5 := by
        unfold v2
        rw [v_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
        rw [add_mul _ _ (u1^6)]
        rw [add_mul _ _ (u1^6)]
        have u1_ne_zero : u1 ≠ 0 := by
          unfold u1
          exact u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩
        have h2_5_1 : 1 / u1 ^ 5 * u1 ^ 6 = u1 := by
          rw [mul_comm, ← mul_div_assoc, mul_one]
          have h2_5_1_1 : 5 ≤ 6 := by norm_num
          rw [div_eq_mul_inv, ← pow_sub₀ u1 u1_ne_zero h2_5_1_1]
          simp
        have h2_5_2 : 1 / u1 ^ 3 * u1 ^ 6 = u1^3 := by
          rw [mul_comm, ← mul_div_assoc, mul_one]
          have h2_5_2_1 : 3 ≤ 6 := by norm_num
          rw [div_eq_mul_inv, ← pow_sub₀ u1 u1_ne_zero h2_5_2_1]
        have h2_5_3 : 1 / u1 * u1 ^ 6 = u1^5 := by
          rw [mul_comm, ← mul_div_assoc, mul_one]
          have h2_5_3_1 : 1 ≤ 6 := by norm_num
          nth_rw 2 [← pow_one u1]
          rw [div_eq_mul_inv, ← pow_sub₀ u1 u1_ne_zero h2_5_3_1]
        rw [h2_5_1, mul_div_assoc, mul_assoc, h2_5_2, h2_5_3]
      _ = v1 := by
        unfold v1 v u1 t1
        rw [add_assoc]
        nth_rw 2 [add_comm]
        rw [add_comm]

lemma v_comparison_implication2
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let t1 := t
  let t2 := -t1
  let u1 := u ⟨t1, h2_1⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
  let v1 := v ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let v2 := v ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  v2 = v1 / u1^6 := by
    intro t1 t2 u1 v1 v2
    let u2 := u ⟨t2, h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have h2_6_1 : u1^6 ≠ 0 := by apply pow_ne_zero 6 (u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩)
    rw [← mul_right_inj' h2_6_1]
    unfold v1
    rw [← v_comparison_implication1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
    change u1 ^ 6 * v2 = u1 ^ 6 * (v2 * u1 ^ 6 / u1 ^ 6)
    ring_nf
    have h2_6_2 : 6 ≤ 12 := by norm_num
    have u1_ne_zero : u1 ≠ 0 := by
      unfold u1
      exact u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩
    rw [mul_comm (u1^12) v2, inv_pow, mul_assoc, ← pow_sub₀ u1 u1_ne_zero h2_6_2]
    simp
    rw [mul_comm]

lemma v_comparison_implication3
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let t1 := t
  let t2 := -t1
  let u1 := u ⟨t1, h2_1⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_u1_pow_6 := LegendreSymbol.χ (u1^6) q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_u1_pow_6 = 1 := by
    intro t1 t2 u1 χ_of_u1_pow_6
    have h2_7_1 : u1^6 = u1^2 * u1^2 * u1^2 := by ring_nf
    unfold χ_of_u1_pow_6
    rw [h2_7_1]
    rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (u1^2 * u1^2) (u1^2) q field_cardinality q_prime_power q_mod_4_congruent_3]
    rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (u1^2) (u1^2) q field_cardinality q_prime_power q_mod_4_congruent_3]
    have h2_7_2 : u1 ≠ 0 := by exact u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩
    rw [LegendreSymbol.χ_of_a_pow_two_eq_one u1 (u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩) q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp

lemma v_comparison_implication4
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let t1 := t
  let t2 := -t1
  let u1 := u ⟨t1, h2_1⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
  let v1 := v ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let v2 := v ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_v1 := LegendreSymbol.χ v1 q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_v2 := LegendreSymbol.χ v2 q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_v2 = χ_of_v1 := by
    intro t1 t2 u1 v1 v2 χ_of_v1 χ_of_v2
    unfold χ_of_v2 χ_of_v1 v1
    rw [← v_comparison_implication1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
    change LegendreSymbol.χ v2 q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ (v2 * u1^6) q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b v2 (u1^6) q field_cardinality q_prime_power q_mod_4_congruent_3]
    let χ_of_u1_pow_6 := LegendreSymbol.χ (u1^6) q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [v_comparison_implication3 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
    simp

lemma X_comparison
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let t1 := t
  let t2 := -t1
  let X1 := X ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X2 = 1 / X1 := by
    intro t1 t2 X1 X2
    let u1 := u ⟨t1, h2_1⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    let u2 := u ⟨t2, h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    let v1 := v ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let v2 := v ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v1 := LegendreSymbol.χ v1 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v2 := LegendreSymbol.χ v2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      X2 = χ_of_v2 * u2 := by
        change χ_of_v2 * u2 = χ_of_v2 * u2
        rfl
      _ = χ_of_v1 / u1 := by
        unfold χ_of_v2 v2 t2
        rw [v_comparison_implication4 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
        unfold u2
        rw [u_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
        change χ_of_v1 * (1 / u1) = χ_of_v1 / u1
        ring_nf
      _ = 1 / (χ_of_v1 * u1) := by
        unfold χ_of_v1
        nth_rw 1 [← LegendreSymbol.one_over_χ_of_a_eq_χ_a v1 q field_cardinality q_prime_power q_mod_4_congruent_3]
        ring_nf
      _ = 1 / X1 := by
        change 1 / X1 = 1 / X1
        rfl

lemma X_comparison_implication
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let t1 := t
  let t2 := -t1
  let X1 := X ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X1 + X2 = -2 * (1 + η_of_point * r_of_s) := by
    intro t1 t2 X1 X2 point η_of_point r_of_s
    let u1 := u ⟨t1, h2_1⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    let u2 := u ⟨t2, h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    let v1 := v ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let v2 := v ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v1 := LegendreSymbol.χ v1 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v2 := LegendreSymbol.χ v2 q field_cardinality q_prime_power q_mod_4_congruent_3
    unfold X2
    rw [X_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
    exact (y_h3 ⟨t, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)

lemma X_comparison_implication2
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let t1 := t
  let t2 := -t1
  let X1 := X ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  X2 * X1 = 1 := by
    intro t1 t2 X1 X2
    unfold X2
    rw [X_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
    rw [← inv_eq_one_div]
    rw [inv_mul_cancel₀ (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩)]

lemma Y_comparison
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let t1 := t
  let t2 := -t1
  let X1 := X ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let Y1 := Y ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let Y2 := Y ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  Y2 = Y1 / X1^3 := by
    intro t1 t2 X1 X2 Y1 Y2
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let u1 := u ⟨t1, h2_1⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    let u2 := u ⟨t2, h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    let v1 := v ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let v2 := v ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let x1 := x ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let x2 := x ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let y1 := y ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let y2 := y ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_u1 := LegendreSymbol.χ u1 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_u2 := LegendreSymbol.χ u2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v1 := LegendreSymbol.χ v1 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v2 := LegendreSymbol.χ v2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_u1_mul_v1  := LegendreSymbol.χ (u1 * v1) q field_cardinality q_prime_power q_mod_4_congruent_3
    have first_factor : (χ_of_v2 * v2)^((q + 1) / 4) = (χ_of_v1 * v1)^((q + 1) / 4) * χ_of_u1 / u1^3:= by
      have h1_1 : χ_of_v2 * v2 = χ_of_v1 * v1 / u1^6 := by
        unfold χ_of_v2
        rw [v_comparison_implication4 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
        unfold v2
        rw [v_comparison_implication2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
        change χ_of_v1 * (v1 / u1^6) = χ_of_v1 * v1 / u1 ^ 6
        rw [← mul_div_assoc]
      -- TODO square argumentation to be understood
      have h1_2 : IsSquare (χ_of_u1 * u1^3) := by sorry
      have h1_3 : (u1^6)^((q + 1) / 4) = χ_of_u1 * u1^3  := by
        -- TODO understand
        sorry
      --apply LegendreSymbol.square_of_a ⟨(χ_of_v_of_t * v_of_t), h2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
      calc
        (χ_of_v2 * v2)^((q + 1) / 4) = (χ_of_v1 * v1 / u1^6)^((q + 1) / 4) := by
          rw [h1_1]
        _ = (χ_of_v1 * v1)^((q + 1) / 4) * χ_of_u1 / u1^3:= by
          rw [div_pow]
          rw [h1_3]
          unfold χ_of_u1
          nth_rw 2 [← LegendreSymbol.one_over_χ_of_a_eq_χ_a u1 q field_cardinality q_prime_power q_mod_4_congruent_3]
          ring_nf
    have second_factor : χ_of_v2 = χ_of_v1 := by exact v_comparison_implication4 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2
    have third_factor : LegendreSymbol.χ (u2^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ (u1 * v1 * (u1^2 + 1 / c_of_s^2)) q field_cardinality q_prime_power q_mod_4_congruent_3 := by
      calc
        LegendreSymbol.χ (u2^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ ((c_of_s^2 * u1^4 * (u2^2 + 1 / c_of_s^2)) * (u1^2 + 1 / c_of_s^2)^2) q field_cardinality q_prime_power q_mod_4_congruent_3 := by
          rw [LegendreSymbol.χ_of_a_eq_χ_a_mul_b_pow_two (u2^2 + 1 / c_of_s^2) (c_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [mul_comm] 
          rw [LegendreSymbol.χ_of_a_eq_χ_a_mul_b_pow_two _ (u_pow_two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩) q field_cardinality q_prime_power q_mod_4_congruent_3]
          rw [mul_comm] 
          rw [LegendreSymbol.χ_of_a_eq_χ_a_mul_b_pow_two _ (v_h1_third_factor_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩) q field_cardinality q_prime_power q_mod_4_congruent_3]
          change LegendreSymbol.χ ((u1^2)^2 * (c_of_s^2 * (u2^2 + 1 / c_of_s^2)) * (u1^2 + 1 / c_of_s^2)^2) q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ (c_of_s ^ 2 * u1 ^ 4 * (u2 ^ 2 + 1 / c_of_s ^ 2) * (u1 ^ 2 + 1 / c_of_s ^ 2) ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3
          ring_nf
        _ = LegendreSymbol.χ ((u1^2 * (c_of_s^2 + u1^2)) * (u1^2 + 1 / c_of_s^2)^2) q field_cardinality q_prime_power q_mod_4_congruent_3 := by
          rw [pow_two u2]
          unfold u2
          rw [u_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
          change LegendreSymbol.χ (c_of_s ^ 2 * u1 ^ 4 * (1 / u1 * (1 / u1) + 1 / c_of_s ^ 2) * (u1 ^ 2 + 1 / c_of_s ^ 2) ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ (u1 ^ 2 * (c_of_s ^ 2 + u1 ^ 2) * (u1 ^ 2 + 1 / c_of_s ^ 2) ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3
          have h1 : c_of_s ^ 2 * u1 ^ 4 * (1 / u1 * (1 / u1) + 1 / c_of_s ^ 2) = u1^2 * (c_of_s^2 + u1^2) := by
            rw [mul_add]
            ring_nf
            simp
            nth_rw 4 [mul_comm]
            rw [mul_assoc (u1 ^ 4) (c_of_s ^ 2) ((c_of_s ^ 2)⁻¹)]
            rw [mul_inv_cancel₀ (c_pow_two_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)]
            have h1_2 : 4 = 2 + 2 := by norm_num
            rw [h1_2, pow_add, ← mul_assoc _ (u1^2) (u1^2), mul_assoc (c_of_s^2 * u1^2) (u1^2) _]
            rw [mul_inv_cancel₀ (u_pow_two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩)]
            ring_nf
          rw [h1]
        _ = LegendreSymbol.χ (u1 * v1 * (u1^2 + 1 / c_of_s^2)) q field_cardinality q_prime_power q_mod_4_congruent_3 := by
          nth_rw 1 [pow_two u1]
          rw [pow_two ((u1^2 + 1 / c_of_s^2))]
          repeat rw [← mul_assoc]
          rw [add_comm]
          unfold v1
          rw [v_h1 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
          change LegendreSymbol.χ (u1 * u1 * (u1 ^ 2 + c_of_s ^ 2) * (u1 ^ 2 + 1 / c_of_s ^ 2) * (u1 ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3 = LegendreSymbol.χ (u1 * (u1 * (u1 ^ 2 + c_of_s ^ 2) * (u1 ^ 2 + 1 / c_of_s ^ 2)) * (u1 ^ 2 + 1 / c_of_s ^ 2)) q field_cardinality q_prime_power q_mod_4_congruent_3
          repeat rw [← mul_assoc]
    calc
      Y2 = Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1^3 := by
        unfold Y2 Y
        change (χ_of_v2 * v2)^((q + 1) / 4) * χ_of_v2 * LegendreSymbol.χ (u2^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3  = Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1 ^ 3
        rw [first_factor, second_factor, third_factor]
        rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b (u1 * v1) (u1^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3]
        change (χ_of_v1 * v1) ^ ((q + 1) / 4) * χ_of_u1 / u1 ^ 3 * χ_of_v1 * (χ_of_u1_mul_v1 * (LegendreSymbol.χ (u1 ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3)) = Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1 ^ 3
        have h1 : (χ_of_v1 * v1) ^ ((q + 1) / 4) * χ_of_u1 / u1 ^ 3 * χ_of_v1 * (χ_of_u1_mul_v1 * (LegendreSymbol.χ (u1 ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3)) = (χ_of_v1 * v1) ^ ((q + 1) / 4) * χ_of_v1 * (LegendreSymbol.χ (u1 ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3) * χ_of_u1 * χ_of_u1_mul_v1 / u1 ^ 3 := by ring_nf
        rw [h1]
        change Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1 ^ 3 = Y1 * χ_of_u1 * χ_of_u1_mul_v1 / u1 ^ 3
        rfl
      _ = Y1 / (χ_of_v1 * u1)^3 := by
        unfold χ_of_u1_mul_v1 χ_of_u1
        rw [LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b u1 v1 q field_cardinality q_prime_power q_mod_4_congruent_3]
        rw [← mul_assoc, mul_assoc Y1 (LegendreSymbol.χ u1 q field_cardinality q_prime_power q_mod_4_congruent_3) (LegendreSymbol.χ u1 q field_cardinality q_prime_power q_mod_4_congruent_3)]
        rw [← LegendreSymbol.χ_of_a_mul_b_eq_χ_of_a_mul_χ_of_b u1 u1 q field_cardinality q_prime_power q_mod_4_congruent_3]
        rw [← pow_two]
        rw [LegendreSymbol.χ_of_a_pow_two_eq_one u1 (u_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩) q field_cardinality q_prime_power q_mod_4_congruent_3]
        rw [← LegendreSymbol.one_over_χ_of_a_eq_χ_a v1 q field_cardinality q_prime_power q_mod_4_congruent_3]
        have h2 : Odd 3 := by
          apply Nat.odd_iff.mpr
          norm_num
        rw [← LegendreSymbol.χ_of_a_pow_n_eq_χ_a v1 ⟨3, h2⟩   q field_cardinality q_prime_power q_mod_4_congruent_3]
        change Y1 * 1 * (1 / χ_of_v1^3) / u1 ^ 3 = Y1 / (χ_of_v1 * u1) ^ 3
        simp
        ring_nf
      _ = Y1 / X1^3 := by
        change Y1 / X1^3 = Y1 / X1^3
        rfl

lemma x_comparison
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let t1 := t
  let t2 := -t1
  let x1 := x ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x2 := x ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  x2 = x1 := by
    intro t1 t2 x1 x2
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X1 := X ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let Y1 := Y ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let Y2 := Y ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have X_pow_three_ne_zero : X1^3 ≠ 0 := by
      apply pow_ne_zero 3 (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩)
    calc
      x2 = (c_of_s - 1) * s * X2 * (1 + X2) / Y2 := by
        change (c_of_s - 1) * s * X2 * (1 + X2) / Y2 = (c_of_s - 1) * s * X2 * (1 + X2) / Y2
        rfl
      _ = (c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) / (Y1 / X1^3) := by
        unfold X2
        rw [X_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
        unfold Y2
        rw [Y_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
        change (c_of_s - 1) * s * (1 / X1) * (1 + 1 / X1) / (Y1 / X1^3) = (c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) / (Y1 / X1 ^ 3)
        ring_nf
      _ = (c_of_s - 1) * s * X1 * (1 + X1) / Y1 := by
        have h2_12_1 : X1^3 / X1^3 = 1 := by
          apply div_self X_pow_three_ne_zero
        rw [← mul_one ((c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) / (Y1 / X1 ^ 3))]
        nth_rw 5 [← h2_12_1]
        rw [← mul_div_mul_comm]
        have h2_12_2 : (c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) * X1 ^ 3 = (c_of_s - 1) * s * X1 * (1 + X1) := by
          calc
            (c_of_s - 1) * s * 1 / X1 * (1 + 1 / X1) * X1 ^ 3 = (c_of_s - 1) * s * X1^3 / X1 * (1 + 1 / X1) := by
              repeat rw [mul_assoc]
              rw [mul_comm (1 + 1 / X1) (X1^3)]
              rw [← mul_assoc]
              rw [← mul_assoc, mul_one, div_mul_eq_mul_div]
              ring_nf
            _ = (c_of_s - 1) * s * X1^2 * (1 + 1 / X1) := by
              have h2_12_2_1 : X1^3 = X1^2 * X1 := by ring_nf
              rw [h2_12_2_1, mul_div_assoc, mul_div_assoc]
              rw [div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩)]
              rw [mul_one]
            _ = (c_of_s - 1) * s * X1 * (1 + X1) := by
              have h2_12_2_1 : X1^2 * (1 + 1 / X1) = X1 * (1 + X1) := by
                rw [pow_two, mul_assoc, mul_add, ← mul_div_assoc]
                rw [mul_one]
                rw [div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩)]
                nth_rw 1 [add_comm]
              rw [mul_assoc ((c_of_s - 1) * s), h2_12_2_1]
              repeat rw [← mul_assoc]
        have h2_12_3 : (Y1 / X1 ^ 3 * X1 ^ 3) = Y1 := by
          rw [mul_comm, ← mul_div_assoc, mul_comm]
          rw [mul_div_assoc, div_self X_pow_three_ne_zero]
          simp
        rw [h2_12_2, h2_12_3]
      _ = x1 := by
        unfold x1
        simp
        rfl

lemma y_comparison
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let t1 := t
  let t2 := -t1
  let y1 := y ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y2 := y ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  y2 = y1 := by
    intro t1 t2 y1 y2
    let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X1 := X ⟨t1, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2 := X ⟨t2, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      y2 = (r_of_s * X2 - (1 + X2)^2) / (r_of_s * X2 + (1 + X2)^2) := by
        change (r_of_s * X2 - (1 + X2)^2) / (r_of_s * X2 + (1 + X2)^2) = (r_of_s * X2 - (1 + X2)^2) / (r_of_s * X2 + (1 + X2)^2)
        rfl
      _ = (r_of_s * (1 / X1) - (1 + (1 / X1))^2) / (r_of_s * (1 / X1) + (1 + (1 / X1))^2) := by
        unfold X2
        rw [X_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
      _ = (r_of_s * X1 - (X1 + 1)^2) / (r_of_s * X1 + (X1 + 1)^2) := by
        have h2_10_1 : X1^2 / X1^2 = 1 := by
          have h2_10_1_1 : X1^2 ≠ 0 := by
            rw [pow_two]
            apply mul_ne_zero
            · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩
            · apply X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩
          apply div_self h2_10_1_1
        rw [← mul_one ((r_of_s * (1 / X1) - (1 + 1 / X1) ^ 2) / (r_of_s * (1 / X1) + (1 + 1 / X1) ^ 2))]
        nth_rw 7 [← h2_10_1]
        rw [← mul_div_mul_comm]
        rw [sub_mul, add_mul]
        have h2_10_2 : (1 / X1) * X1^2 = X1 := by
          rw [mul_comm, ← mul_div_assoc, mul_one]
          rw [pow_two, mul_div_assoc, div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩)]
          simp
        have h2_10_3 : (1 + 1 / X1) ^ 2 * X1^2 = (X1 + 1)^2 := by
          rw [← mul_pow _ _ 2]
          rw [add_mul, one_mul]
          rw [mul_comm, ← mul_div_assoc, mul_one]
          rw [div_self (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨t, h2_1⟩)]
        rw [mul_assoc]
        rw [h2_10_2, h2_10_3]
      _ = y1 := by
        rw [add_comm]
        unfold y1 y X1
        simp
        rfl

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

-- Chapter 3.3 Theorem 3.1
theorem ϕ_inv_only_two_specific_preimages
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

theorem point_in_ϕ_over_F_with_prop1_base_case
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

theorem point_in_ϕ_over_F_with_prop1_main_case
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
theorem point_in_ϕ_over_F_with_prop1
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

theorem point_in_ϕ_over_F_with_prop2_base_case
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

theorem point_in_ϕ_over_F_with_prop2_main_case
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
theorem point_in_ϕ_over_F_with_prop2
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

theorem point_in_ϕ_over_F_with_prop3_base_case
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

-- Used in the main case of Theorem 3 Proof part B
theorem X_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 : 
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  (X_of_t - 1)^2 = 0 := by
    intro X_of_t
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    have h1_1 : X_of_t + 1 / X_of_t = -2 * (1 + η_of_point * r_of_s) := by exact (y_h3 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
    rw [η_h1] at h1_1
    ring_nf at h1_1
    rw [← mul_left_inj' (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)] at h1_1
    rw [add_mul] at h1_1
    change X_of_t * X_of_t + X_of_t⁻¹ * X_of_t = 2 * X_of_t at h1_1
    rw [← add_left_inj (2 * X_of_t)]
    ring_nf
    rw [inv_mul_cancel₀ (X_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 t)] at h1_1
    rw [pow_two, add_comm]
    nth_rw 2 [mul_comm]
    exact h1_1

-- Used in the main case of Theorem 3 Proof part B
theorem X_η_h2
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 : 
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  X_of_t = 1 := by
    intro X_of_t
    have h1 : (X_of_t - 1)^2 = 0 := by exact (X_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)
    simp at h1
    rw [← add_left_inj (-1)]
    ring_nf
    have h2 : -1 + X_of_t = X_of_t - 1 := by ring_nf
    rw [h2]
    exact h1

-- Used in the main case of Theorem 3 Proof part B
theorem u_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 : 
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3;
  u_of_t = 1 := by
    intro u_of_t
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let χ_of_v_of_t := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    have h3_1 : X_of_t = χ_of_v_of_t * u_of_t := by
      unfold X_of_t X
      rfl
    unfold X_of_t at h3_1
    rw [X_η_h2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1] at h3_1
    -- TODO have to make case comparison of chi(v) to conclude that u can only be 1
    sorry

-- Used in the main case of Theorem 3 Proof part B
theorem t_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 : 
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  t.val = 0 := by
    let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
    have h1 : u_of_t = 1 := by exact (u_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)
    unfold u_of_t u at h1
    have h4_1 : 1 + t.val ≠ 0 := by exact u_defined t
    rw [← mul_right_inj' h4_1, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self h4_1] at h1
    rw [← add_left_inj (t.val - 1)] at h1
    ring_nf at h1
    symm at h1
    rw [← div_left_inj' (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h1
    ring_nf at h1
    rw [mul_assoc, inv_mul_cancel₀ (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3), mul_one] at h1
    exact h1

-- Used in the main case of Theorem 3 Proof part B
theorem v_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 : 
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  v_of_t = r_of_s^2 := by
    intro v_of_t r_of_s
    unfold v_of_t v
    rw [(u_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)]
    ring_nf
    rfl

-- Used in the main case of Theorem 3 Proof part B
theorem Y_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 : 
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let χ_of_c_of_s  := (LegendreSymbol.χ c_of_s q field_cardinality q_prime_power q_mod_4_congruent_3)
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  Y_of_t = r_of_s * χ_of_c_of_s := by
    intro Y_of_t c_of_s χ_of_c_of_s r_of_s
    let χ_of_one_add_one_div_c_of_s_pow_two := (LegendreSymbol.χ (1 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3)
    let χ_of_r_of_s := (LegendreSymbol.χ r_of_s q field_cardinality q_prime_power q_mod_4_congruent_3)
    let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3;
    let χ_of_v_of_t := (LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3)
    let χ_of_r_of_s_div_c_of_s := (LegendreSymbol.χ (r_of_s / c_of_s) q field_cardinality q_prime_power q_mod_4_congruent_3)
    let χ_of_r_of_s_pow_two := (LegendreSymbol.χ (r_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3)
    let χ_of_sum := LegendreSymbol.χ (u_of_t ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      Y_of_t = (r_of_s^2)^((q + 1) / 4) * χ_of_one_add_one_div_c_of_s_pow_two := by
        unfold Y_of_t Y
        rw [(v_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)]
        rw [(u_η_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1)]
        change (χ_of_r_of_s_pow_two  * r_of_s^2) ^ ((q + 1) / 4) * χ_of_r_of_s_pow_two * (LegendreSymbol.χ (1 ^ 2 + 1 / c_of_s ^ 2) q field_cardinality q_prime_power q_mod_4_congruent_3) = (r_of_s ^ 2) ^ ((q + 1) / 4) * χ_of_one_add_one_div_c_of_s_pow_two
        have h1 : r_of_s^2 ≠ 0 := by
          rw [pow_two]
          apply mul_ne_zero
          · exact r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
          · exact r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
        have h2 : IsSquare (r_of_s^2) := by apply IsSquare.sq
        unfold χ_of_r_of_s_pow_two 
        rw [LegendreSymbol.χ_a_eq_one (r_of_s^2) h1 h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
        nth_rw 2 [pow_two] 
        rw [mul_one, one_mul, mul_one]
      _ = χ_of_r_of_s * r_of_s * χ_of_r_of_s_div_c_of_s := by
        -- TODO understand
        sorry
      _ = r_of_s * χ_of_c_of_s := by
        -- TODO same square root argument as above (χ(r)r = r ?) ... understand
        sorry

theorem point_in_ϕ_over_F_with_prop3_main_case
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

-- Implicated by main case of Theorem 3 proof part B. Saved for later usage in TODO
theorem y_η_h1
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (η_h1 : 
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    η_of_point * r_of_s = -2
  )
  :
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y_of_t := y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  y_of_t = (r_of_s - 4) / (r_of_s + 4) := by
    intro r_of_s y_of_t
    unfold y_of_t y
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    change (r_of_s * X_of_t - (1 + X_of_t) ^ 2) / (r_of_s * X_of_t + (1 + X_of_t) ^ 2) = (r_of_s - 4) / (r_of_s + 4)
    unfold X_of_t
    rw [X_η_h2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 η_h1]
    ring_nf

-- Original: Theorem 3.3 Proof B prop 3 argumentation
theorem point_in_ϕ_over_F_with_prop3
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

lemma zero_h1
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  (0 : F) ≠ 1 ∧ (0 : F) ≠ -1 := by
    constructor
    · symm
      exact FiniteFieldBasic.one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    · symm
      exact FiniteFieldBasic.neg_one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3

lemma u_of_zero
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  have h1 : (0 : F) ≠ 1 ∧ (0 : F) ≠ -1 := by exact zero_h1 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let u_of_t := u ⟨(0 : F), h1⟩ q field_cardinality q_prime_power q_mod_4_congruent_3;
  u_of_t = 1 := by 
    intro h1 u_of_t
    unfold u_of_t u
    simp

lemma v_of_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  have h1 : (0 : F) ≠ 1 ∧ (0 : F) ≠ -1 := by exact zero_h1 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let v_of_t := v ⟨(0 : F), h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  v_of_t = r_of_s^2 := by
    intro h1 v_of_t r_of_s
    unfold v_of_t v
    rw [u_of_zero q field_cardinality q_prime_power q_mod_4_congruent_3]
    unfold r_of_s
    ring_nf

lemma X_of_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  have h1 : (0 : F) ≠ 1 ∧ (0 : F) ≠ -1 := by exact zero_h1 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let X_of_t := X ⟨(0 : F), h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  X_of_t = 1 := by
    intro h1 X_of_t
    unfold X_of_t X
    let v_of_t := v ⟨(0 : F), h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let χ_of_v_of_t := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [u_of_zero q field_cardinality q_prime_power q_mod_4_congruent_3]
    change χ_of_v_of_t * 1 = 1
    unfold χ_of_v_of_t v_of_t
    rw [v_of_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    change (LegendreSymbol.χ (r_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3) * 1 = 1
    rw [LegendreSymbol.χ_of_a_pow_two_eq_one r_of_s (r_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp

lemma y_of_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  have h1 : (0 : F) ≠ 1 ∧ (0 : F) ≠ -1 := by exact zero_h1 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let y_of_t := y ⟨(0 : F), h1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  y_of_t = (r_of_s - 4) / (r_of_s + 4) := by
    intro h1 y_of_t r_of_s
    unfold y_of_t y
    rw [X_of_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    change (r_of_s * 1 - (1 + 1) ^ 2) / (r_of_s * 1 + (1 + 1) ^ 2) = (r_of_s - 4) / (r_of_s + 4)
    ring_nf

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
    let h1 := zero_h1 q field_cardinality q_prime_power q_mod_4_congruent_3
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
theorem point_in_E_over_F_with_props_iff_point_in_ϕ_over_F_mp
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
theorem point_in_E_over_F_with_props_iff_point_in_ϕ_over_F_mpr
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
theorem point_in_E_over_F_with_props_iff_point_in_ϕ_over_F
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
theorem E_over_F_subset_ϕ_over_F
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

theorem point_in_E_over_F
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

noncomputable def X2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  -- TODO decide if defs should already require everything to guarantee well definedness
  -- PRO: always well defined; CON: hard calling convention, not as general
  --(point : {p : (F) × (F) // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  --(h : point.val ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
  : F :=
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  (-(1 + η_of_point * r_of_s) + ((1 + η_of_point * r_of_s)^2 - 1)^((q + 1) / 4))

lemma X2_h1
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  :
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  (1 + η_of_point * r_of_s + X2_of_t)^2 = (1 + η_of_point *r_of_s)^2 - 1 := by
    ring_nf
    sorry

lemma X2_h2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  :
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  X2_of_t^2 + 2 * (1 + η_of_point *r_of_s) * X2_of_t + 1 = 0 := by
    sorry

lemma X2_h3
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X ⟨t, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X'_of_t := X ⟨-t, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  (X2_of_t - X_of_t) * (X2_of_t - X'_of_t) = 0 := by
    intro point X_of_t X'_of_t X2_of_t 
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      (X2_of_t - X_of_t) * (X2_of_t - X'_of_t) = X2_of_t^2 - (X_of_t + X'_of_t) * X2_of_t + X_of_t * X'_of_t := by ring_nf
      _ = X2_of_t^2 + 2 * (1 + η_of_point * r_of_s) * X2_of_t + 1 := by
        rw [X_comparison_implication t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
        change X2_of_t ^ 2 - -2 * (1 + η_of_point * r_of_s) * X2_of_t + X_of_t * X'_of_t = X2_of_t ^ 2 + 2 * (1 + η_of_point * r_of_s) * X2_of_t + 1
        rw [mul_add, mul_comm X_of_t _, X_comparison_implication2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
        ring_nf
      _ = 0 := by exact X2_h2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point

-- TODO usage? best possible statement?
lemma X2_h4
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X ⟨t, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X'_of_t := X ⟨-t, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  X2_of_t = X_of_t ∨ X2_of_t = X'_of_t := by
    intro point X_of_t X'_of_t X2_of_t 
    have h1 : (X2_of_t - X_of_t) * (X2_of_t - X'_of_t) = 0 := by exact X2_h3 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2
    rw [mul_eq_zero] at h1
    nth_rw 1 [← add_left_inj (-X_of_t)]
    nth_rw 2 [← add_left_inj (-X'_of_t)]
    ring_nf
    exact h1

lemma X2_h4
  (t : F)
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X ⟨t, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X'_of_t := X ⟨-t, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  X2_of_t = X_of_t := by
    intro point X_of_t X'_of_t X2_of_t 
    let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point
    let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    calc
      (X2_of_t - X_of_t) * (X2_of_t - X'_of_t) = X2_of_t^2 - (X_of_t + X'_of_t) * X2_of_t + X_of_t * X'_of_t := by ring_nf
      _ = X2_of_t^2 + 2 * (1 + η_of_point * r_of_s) * X2_of_t + 1 := by
        rw [X_comparison_implication t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
        change X2_of_t ^ 2 - -2 * (1 + η_of_point * r_of_s) * X2_of_t + X_of_t * X'_of_t = X2_of_t ^ 2 + 2 * (1 + η_of_point * r_of_s) * X2_of_t + 1
        rw [mul_add, mul_comm X_of_t _, X_comparison_implication2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2]
        ring_nf
      _ = 0 := by exact X2_h2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point

noncomputable def z
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : F
  :=
  let x := point.fst
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let a := (c_of_s - 1) * s * X2_of_point * (1 + X2_of_point) * x * (X2_of_point^2 + 1 / c_of_s^2)
  LegendreSymbol.χ a q field_cardinality q_prime_power q_mod_4_congruent_3

noncomputable def u2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : F
  :=
  let X2_of_point := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let z_of_point := z s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  z_of_point * X2_of_point

noncomputable def t2
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : F
  :=
  let u2_of_point := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  (1 - u2_of_point) / (1 + u2_of_point)

theorem X2_defined
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

theorem z_defined
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

theorem t2_defined
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

/-- `invmap_representative` is ...

Paper definition at chapter 3.3 Theorem 3.3.
-/
theorem invmap_representative_base_case
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
theorem invmap_representative_main_case
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

