import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
import Elligator.Elligator1.sProperties
import Elligator.Elligator1.cProperties
import Elligator.Elligator1.dProperties
import Elligator.Elligator1.uProperties
import Elligator.Elligator1.vProperties
import Elligator.Elligator1.XProperties
import Elligator.Elligator1.YProperties
import Elligator.Elligator1.xProperties
import Elligator.Elligator1.yProperties
import Elligator.Elligator1.etaProperties
import Elligator.Elligator1.X2Properties
import Elligator.Elligator1.zProperties
import Elligator.Elligator1.u2Properties

namespace Elligator.Elligator1

section t2Properties

variable {F : Type*} [Field F] [Fintype F]

lemma t2_eq_one
  (t : { t : F // t = 1 ∨ t = -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let t2_of_point := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  t2_of_point = 1 := by
    intro point t2_of_point
    unfold t2_of_point t2
    let u2_of_point := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    change (1 - u2_of_point) / (1 + u2_of_point) = 1
    unfold u2_of_point
    rw [u2_eq_zero t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    simp

lemma t2_eq_t
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (X_h :
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    X2_of_t = X_of_t
  )
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let t2_of_point := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  t2_of_point = t := by
    intro point t2_of_point
    let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
    let u2_of_t := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    have h1 : u2_of_t = u_of_t := by exact u2_eq_u t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 X_h
    unfold u_of_t u at h1
    unfold t2_of_point t2
    change (1 - u2_of_t) / (1 + u2_of_t) = t.val
    change u2_of_t = (1 - t.val) / (1 + t.val) at h1
    rw [h1]
    rw [sub_div' (FiniteFieldBasic.one_add_t_ne_zero t)]
    rw [add_div' (1 - t.val) 1 (1 + t.val) (FiniteFieldBasic.one_add_t_ne_zero t)]
    simp
    rw [div_div_div_eq]
    norm_num
    have h2 : ((1 + t.val) * 2) ≠ 0 := by
      apply mul_ne_zero
      · exact FiniteFieldBasic.one_add_t_ne_zero t
      · exact FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [← two_mul t.val, mul_comm 2 t.val, mul_assoc, mul_comm 2, mul_div_assoc, div_self h2]
    simp

lemma t2_eq_t'
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (X_h :
    let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    have h2_2 : (-t.val ≠ 1 ∧ -t.val ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
    let X'_of_t := X ⟨-t.val, h2_2⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let X2_of_t := X2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    X2_of_t = X'_of_t
  )
  :
  let point := ϕ t.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let t2_of_point := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let t' := -t.val
  t2_of_point = t' := by
    intro point t2_of_point t'
    have h2_2 : (-t.val ≠ 1 ∧ -t.val ≠ -1) := by exact FiniteFieldBasic.neg_t_ne_one_and_neg_t_ne_neg_one t q field_cardinality q_prime_power q_mod_4_congruent_3
    let u'_of_t := u ⟨t', h2_2⟩ q field_cardinality q_prime_power q_mod_4_congruent_3
    let u2_of_t := u2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    have h1 : u2_of_t = u'_of_t := by exact u2_eq_u' t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 X_h
    unfold u'_of_t u at h1
    unfold t2_of_point t2
    change (1 - u2_of_t) / (1 + u2_of_t) = t'
    change u2_of_t = (1 - t') / (1 + t') at h1
    rw [h1]
    rw [sub_div' (FiniteFieldBasic.one_add_t_ne_zero ⟨t', h2_2⟩)]
    rw [add_div' (1 - t') 1 (1 + t') (FiniteFieldBasic.one_add_t_ne_zero ⟨t', h2_2⟩)]
    simp
    rw [div_div_div_eq]
    norm_num
    have h2 : ((1 + t') * 2) ≠ 0 := by
      apply mul_ne_zero
      · exact FiniteFieldBasic.one_add_t_ne_zero ⟨t', h2_2⟩
      · exact FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [← two_mul t', mul_comm 2 t', mul_assoc, mul_comm 2, mul_div_assoc, div_self h2]
    simp

lemma t2_in_t_or_neg_t
  (t s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let t' := -t
  let t2_of_point := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  t2_of_point = t ∨ t2_of_point = t' := by
    intro point t' t2_of_point
    by_cases h : t ≠ 1 ∧ t ≠ -1
    · rcases (X2_h4 ⟨t, h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) with h1 | h1
      · left
        exact t2_eq_t ⟨t, h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h1
      · right
        exact t2_eq_t' ⟨t, h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h1
    · have h' : t = 1 ∨ t = -1 := by
        rw [← not_ne_iff, ← not_ne_iff, ← Lean.Grind.not_and]
        exact h
      unfold t2_of_point t'
      rw [t2_eq_one ⟨t, h'⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
      have h'' : 1 = t ∨ 1 = -t := by
        nth_rw 2 [← mul_left_inj' (FiniteFieldBasic.neg_one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)]
        simp
        nth_rw 1 [eq_comm]
        nth_rw 2 [eq_comm]
        exact h'
      exact h''
