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
import Elligator.Elligator1.phiProperties

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
        let point := ϕ p.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
        let t' := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
        by_cases p.val = 1 ∨ p.val = -1
        · rename_i h4_1 
          have h4_1_1 : t = 1 := by
             
            sorry
          rw [← h4_1_1] at h4_1
          exact h4_1
        · rename_i h4_1 
          rw [not_or, ← ne_eq, ← ne_eq] at h4_1
          have h4_1_1 : t' = p.val ∨ t' = -p.val := by
            exact (t2_h1 ⟨p.val, h4_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3)
          have h4_1_2 : p.val = t' ∨ p.val = -t' := by
            rcases h4_1_1 with h4_1_3 | h4_1_3 
            · rw [h4_1_3]
              left
              rfl
            · rw [h4_1_3]
              right
              simp
          -- TODO unsure if theorem statement is properly provable like this
          -- - there is no connection from p to t to be established
          -- - building the statement in another way without altering 3.1 is non trivial if at all possible
          have h4_1_3 : t' = t := by
            unfold t' point
            rw [h3]
            by_cases t = 1 ∨ t = -1
            · rename_i h4_1_3_1
              rw [t2_eq_one ⟨t, h4_1_3_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
               
              sorry
            · rename_i h4_1_3_1
              rw [not_or, ← ne_eq, ← ne_eq] at h4_1_3_1 
              --rw [t2_eq_t ⟨t, h4_1_3_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 (X_comparison)]
               
              sorry
          rw [h4_1_3] at h4_1_2
          exact h4_1_2
      have h5 : ¬(p.val = t ∨ p.val = -t) := by 
        rw [not_or]
        exact p.prop
      contradiction
    · intro h
      exact ϕ_of_t_eq_ϕ_of_neg_t t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

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
  → ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
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
  ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
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
  ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 pointE
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

-- Original: Theorem 3.3 Proof B
theorem ϕ_of_t2_eq_x_y
  -- Fix t ∈ F_q
  (t s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  -- Define (x, y) = ϕ(t)
  let point := ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let x_of_t := point.1
  let y_of_t := point.2
  -- t2 defined (and used to build ϕ(t2))
  let t' := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let ϕ_of_t' := ϕ t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_of_t' = (x_of_t, y_of_t) := by
    intro point x_of_point y_of_point t' ϕ_of_t'
    unfold x_of_point y_of_point point ϕ 
    split
    · rename_i h
      exact ϕ_of_t2_eq_x_y_main_case ⟨t, h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · rename_i h
      have h1_1 : t = 1 ∨ t = -1 := by
        rw [← not_ne_iff, ← not_ne_iff, ← Lean.Grind.not_and]
        exact h
      simp
      exact ϕ_of_t2_eq_x_y_base_case ⟨t, h1_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 

