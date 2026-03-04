import Mathlib
import Mathlib.Data.Set.Basic
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
theorem ϕ_of_t_eq_ϕ_of_neg_t_iff_ϕ_preimages
  (t s : F)
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
    · intro h
      exact ϕ_preimages t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
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

-- TODO move into separate file?
lemma point_in_ϕ_over_F_main_case
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ↑point)
  (x_ne_zero : point.val.1 ≠ 0)
  :
  let ϕ_over_F := ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  point.val ∈ ϕ_over_F := by
    intro ϕ_over_F
    let x := point.val.1
    let y := point.val.2
    by_cases y = 1
    · rename_i h3
      have h4_1 := point.prop;
      unfold E_over_F at h4_1
      rw [Set.mem_setOf_eq] at h4_1
      let d_of_s := d s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
      change x ^ 2 + y ^ 2 = 1 + d_of_s * x ^ 2 * y ^ 2  at h4_1
      rw [h3] at h4_1
      rw [← add_right_inj (-1)] at h4_1
      rw [← div_left_inj' x_ne_zero, ← div_left_inj' x_ne_zero] at h4_1
      ring_nf at h4_1
      have h5 : x^2 ≠ 0 := by grind
      rw [inv_pow, mul_inv_cancel₀ h5, one_mul] at h4_1
      let h6 := d_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      symm at h4_1
      contradiction
    · rename_i h3
      let η_ne_zero := η_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero

      sorry

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
    intro h1
    -- TODO why is this enough instead of the proof C? Statement error?
    -- Will solve this as soon as part c is formalized
    --intro h1 h2
    --exact h1
    let x := point.val.1
    let y := point.val.2
    by_cases x = 0
    · rename_i h2
      rw [x_y_eq_zero_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point h1 h2]
      rw [← ϕ_of_one_eq_zero_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
      exact ϕ_of_one_in_ϕ_of_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · rename_i h2
      rw [← not_ne_iff, not_not] at h2
      exact point_in_ϕ_over_F_main_case s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point h1 h2

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
