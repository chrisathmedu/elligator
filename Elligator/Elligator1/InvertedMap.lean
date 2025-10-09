import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
import Elligator.Elligator1.Sets
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
import Elligator.Elligator1.X2Properties
import Elligator.Elligator1.u2Properties
import Elligator.Elligator1.zProperties
import Elligator.Elligator1.t2Properties

namespace Elligator.Elligator1

-- Original-Reference: Theorem 3
section InvertedMap

variable {F : Type*} [Field F] [Fintype F]

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
  ↔ ¬ (∃ (p : { n : F // n ≠ t ∧ n ≠ -t}), ϕ p.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 = ϕ_of_t) := by
    intro ϕ_of_t ϕ_of_neg_t
    constructor
    · intro h1 h2
      cases h2
      rename_i p h3
      have h4 : p.val = t ∨ p.val = -t := by
        have h4_1 : -p.val ≠ 1 ∧ -p.val ≠ -1 := by sorry
        have h4_2 : p.val ≠ 1 ∧ p.val ≠ -1 := by sorry
        have TODO1 : t ≠ 1 ∧ t ≠ -1 := by sorry
        have TODO2 : -t ≠ 1 ∧ -t ≠ -1 := by sorry
        let point := ϕ p.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
        let t' := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
        rcases (t2_h1 p.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h4_2 h4_1) with h | h
        · change t' = p.val at h
          rw [← h]
          unfold ϕ at h3
          -- TODO unsure about current API being able to handle this
          --exact t2_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 TODO1 TODO2
          --exact (t2_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 TODO1 TODO2)
          sorry
        · change t' = -p.val at h
          rw [← mul_left_inj' (FiniteFieldBasic.neg_one_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)] at h
          simp at h
          rw [← h]
          sorry
      have h5 : ¬(p.val = t ∨ p.val = -t) := by 
        rw [not_or]
        exact p.prop
      contradiction
    · intro h
      exact ϕ_of_t_eq_ϕ_of_neg_t t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

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

-- TODO get 3.2 bundled into one?
-- Original: Theorem 3.2 Proof B (3.2 forward statement)
theorem point_props_of_point_in_ϕ_over_F
  (t s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  point ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 
  → (ϕ_over_F_prop1 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    ∧ ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
    ∧ ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  := by
    intro point h1
    constructor
    · exact point_in_ϕ_over_F_with_prop1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · constructor
      · exact point_in_ϕ_over_F_with_prop2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      · exact point_in_ϕ_over_F_with_prop3 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

-- Original: Theorem 3.2 Proof C (3.2 reverse statement)
theorem point_in_ϕ_over_F_of_point_props
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  :
  (ϕ_over_F_prop1 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  ∧ ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  ∧ ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val)
  → point.val ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 
  := by
    intro h1 h2
    -- TODO why is this enough instead of the proof C? Statement error?
    -- Will solve this as soon as part c is formalized
    exact h1
    --sorry

-- TODO combinable with above theorems?
-- Chapter 3.3 Theorem 3.2
theorem point_props_iff_point_in_ϕ_over_F_of_point
  (t s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (pointE : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  :
  -- This theorem has to distinguish between two different kinds of points.
  -- pointE : a point which is just assumed to fulfill the curve equation of E_over_F
  -- pointϕ : a point which is generated through ϕ using a custom t without further restrictions
  let pointϕ := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  (ϕ_over_F_prop1 q field_cardinality q_prime_power q_mod_4_congruent_3 pointE
  ∧ ϕ_over_F_prop2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 pointE
  ∧ ϕ_over_F_prop3 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 pointE)
  ↔ pointϕ ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 := by
    intro pointϕ 
    constructor
    · --intro h1
      --intro h2
      -- TODO could just paste part B proof in here and solve... API too liberal?
      --constructor
      --· exact point_in_ϕ_over_F_with_prop1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      --· constructor
      --  · exact point_in_ϕ_over_F_with_prop2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      --  · exact point_in_ϕ_over_F_with_prop3 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      --exact point_in_ϕ_over_F_of_point_of_point_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point, h2⟩
      sorry
    · sorry
      --exact point_props_of_point_in_ϕ_over_F_of_point t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

/-- `invmap_representative` is ...

Paper definition at chapter 3.3 Theorem 3.3.
-/
theorem invmap_representatives
  (t s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  -- TODO not relevant? Perhaps already implicitly given by usage of helper theorems? => API minimal?
  --(point : {p : F × F // p ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (h2_1 : t ≠ 1 ∧ t ≠ -1)
  (h2_2 : -t ≠ 1 ∧ -t ≠ -1)
  :
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let t' := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let ϕ_of_t' := ϕ t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x_of_t := x ⟨t, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let y_of_t := y ⟨t, h2_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_of_t' = (x_of_t, y_of_t) := by
    intro point t' ϕ_of_t' x_of_t y_of_t
    unfold ϕ_of_t' ϕ
    rcases (t2_h1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2) with h | h
    · change t' = t at h
      rw [h]
      rw [dif_pos h2_1]
    · change t' = -t at h
      rw [h]
      rw [dif_pos h2_2]
      unfold x_of_t y_of_t
      symm
      exact point_comparison t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 h2_1 h2_2
