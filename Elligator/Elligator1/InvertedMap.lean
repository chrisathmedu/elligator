import Mathlib
import Mathlib.Data.Set.Basic
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
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
  let ϕ_of_t := (ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let ϕ_of_neg_t := (ϕ (-t) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  ϕ_of_t = ϕ_of_neg_t
  ↔ ¬ (∃ (p : { n : F // n ≠ t ∧ n ≠ -t}), ϕ p.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 = ϕ_of_t) := by
    intro ϕ_of_t ϕ_of_neg_t
    constructor
    · intro h
      exact ϕ_preimages t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · intro h
      exact ϕ_of_t_eq_ϕ_of_neg_t t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

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
  let point := (ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  point ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  → ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  := by
    intro point h1
    constructor
    · exact point_in_ϕ_over_F_with_prop1 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · constructor
      · exact point_in_ϕ_over_F_with_prop2 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      · exact point_in_ϕ_over_F_with_prop3 t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

lemma point_in_ϕ_over_F_base_case
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_eq_zero : point.val.1 = 0)
  :
  let ϕ_over_F := ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  point.val ∈ ϕ_over_F := by
    rw [x_y_eq_zero_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_eq_zero]
    rw [← ϕ_of_one_eq_zero_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3]
    exact ϕ_of_one_in_ϕ_of_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

---START--- TODO
lemma η_ne_zero
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : {p : F × F // p ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3})
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  :
  let η_of_point := η q field_cardinality q_prime_power q_mod_4_congruent_3 point.val
  η_of_point ≠ 0 := by
    intro η_of_point
    let x := point.val.1
    let y := point.val.2
    unfold η_of_point η
    change (y - 1) / (2 * (y + 1)) ≠ 0
    apply div_ne_zero
    · intro h1
      have h2 : y ≠ 1 := by exact y_ne_one s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero
      have h3: y = 1 := by
        rw [← add_left_inj 1] at h1
        simp at h1
        exact h1
      contradiction
    · unfold ϕ_over_F_props at point_props
      apply mul_ne_zero
      · exact FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
      · exact point_props.1

---END--- TODO

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
  (point_props : ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point)
  (x_ne_zero : point.val.1 ≠ 0)
  :
  let ϕ_over_F := ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3;
  point.val ∈ ϕ_over_F := by
    intro ϕ_over_F
    let x := point.val.1
    let y := point.val.2
    by_cases y = 1
    · rename_i h3
      -- TODO this differs from original proof, which claims that this implies x = 0, contra
      -- I was not able to see that
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
      -- Showing that we can come back to the t def of theorem 1 with such point = (x, y)
      -- i.e. (x, y) = phi(t) => ... implies that is elem of phi_of_F???
      let η_ne_zero := η_ne_zero s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point point_props x_ne_zero
      unfold ϕ_over_F Elligator1.ϕ_over_F
      -- HERE do all the 'Define' somehow elegant
      -- If this proof goes through, we have to organzie the big picture of Theorem 3.2 => done with Theorem 3 then
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
    let x := point.val.1
    let y := point.val.2
    by_cases h2 : x = 0
    · exact point_in_ϕ_over_F_base_case s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point h1 h2
    · rw [← not_ne_iff, not_not] at h2
      exact point_in_ϕ_over_F_main_case s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point h1 h2

-- Chapter 3.3 Theorem 3.2
theorem point_props_iff_point_in_ϕ_over_F_of_point
  (t s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let point := (ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  ϕ_over_F_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  ↔ point ∈ ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 := by
    intro point
    constructor
    · have point_in_E_over_F : point ∈ (E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3) := by sorry
      exact point_in_ϕ_over_F_of_point_props s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 ⟨point, point_in_E_over_F⟩
    · exact point_props_of_point_in_ϕ_over_F t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

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
  let point := (ϕ t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  let x_of_t := point.1
  let y_of_t := point.2
  -- t2 defined (and used to build ϕ(t2))
  let t' := t2 s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 point
  let ϕ_of_t' := (ϕ t' s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).val
  ϕ_of_t' = (x_of_t, y_of_t) := by
    intro point x_of_point y_of_point t' ϕ_of_t'
    unfold x_of_point y_of_point point ϕ
    simp only []
    split
    · rename_i h
      exact ϕ_of_t2_eq_x_y_main_case ⟨t, h⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    · rename_i h
      have h1_1 : t = 1 ∨ t = -1 := by
        rw [← not_ne_iff, ← not_ne_iff, ← Lean.Grind.not_and]
        exact h
      simp
      exact ϕ_of_t2_eq_x_y_base_case ⟨t, h1_1⟩ s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
