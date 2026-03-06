import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol

namespace Elligator.Elligator1

section Variables

variable {F : Type*} [Field F] [Fintype F]

/-- c(s) is a constant defined in the paper.

Paper definition at chapter 3.2 theorem 1.
-/
noncomputable def c
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
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
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F :=
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  c_of_s + 1 / c_of_s

/-- d(s) is a constant defined in the paper.

Paper definition at chapter 3.2 theorem 1.
-/
noncomputable def d
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F :=
  let c_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  (-(c_s + 1)^2 / (c_s - 1)^2)

/-- u(t) is a function defined in the paper.

Paper definition at chapter 3.2 theorem 1.
-/
noncomputable def u
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
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
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F :=
  let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  (u_of_t)^5 + (r_of_s^2 - 2) * (u_of_t)^3 + u_of_t

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
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F :=
  let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
  let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_v_of_t := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
  χ_of_v_of_t * u_of_t

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
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F :=
  let u_of_t := u t q field_cardinality q_prime_power q_mod_4_congruent_3
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let v_of_t := v t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_v_of_t := LegendreSymbol.χ v_of_t q field_cardinality q_prime_power q_mod_4_congruent_3
  let χ_of_sum := LegendreSymbol.χ ((u_of_t)^2 + 1 / c_of_s^2) q field_cardinality q_prime_power q_mod_4_congruent_3
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
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F :=
  let c_of_s := c s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let Y_of_t := Y t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
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
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : F :=
  let r_of_s := r s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let X_of_t := X t s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  (r_of_s * X_of_t - (1 + X_of_t)^2) / (r_of_s * X_of_t + (1 + X_of_t)^2)

/-- η(s, q, point) is a function defined in the paper.

Paper definition at chapter 3.3 theorem 3.
-/
noncomputable def η
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (point : F × F)
  : F :=
  let y := point.snd
  (y - 1) / (2 * (y + 1))

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

noncomputable def b
  (q : ℕ)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : ℕ := Int.toNat ⌊ Real.logb 2 q ⌋

abbrev Binary := Fin 2
