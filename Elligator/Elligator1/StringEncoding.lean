import Mathlib
import Elligator.FiniteFieldBasic
import Elligator.LegendreSymbol
import Elligator.Elligator1.Variables
import Elligator.Elligator1.Map
import Elligator.Elligator1.phiProperties
import Elligator.Elligator1.InvertedMap
import Elligator.Elligator1.bProperties
import Elligator.Elligator1.bitsToNatProperties
import Elligator.Elligator1.SProperties

namespace Elligator.Elligator1

-- Original-Reference: Theorem 4
section StringEncoding

variable {F : Type*} [Field F] [Fintype F]
variable {q : ℕ} (field_cardinality : Fintype.card F = q) (q_prime_power : IsPrimePow q) (q_mod_4_congruent_3 : q % 4 = 3)

-- `ι` maps an element of `S` to `E_over_F` via `ι(τ) = ϕ(σ(τ))`.
noncomputable def ι
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  (τ : (@S q))
  : {P : F × F // P ∈ E_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3}
  :=
  ϕ (σ τ.1) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3

noncomputable def ι_over_S
  (s : F)
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  Set (F × F) :=
  { P | ∃ (τ : (@S q)), P = ι s s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3 τ }

-- 1. statement of Theorem 4:
-- Then #S = (q + 1) / 2;
theorem S_card (q_mod_4_congruent_3 : q % 4 = 3)
  : (@S q).card = (q + 1) / 2 := by
    exact S_card_eq_q_add_one_over_two q_mod_4_congruent_3

theorem ι_injective
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (field_cardinality : Fintype.card F = q)
  (q_prime : Prime q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  have q_prime_power := by grind
  let ι := ι s s_h1 s_h2 field_cardinality q_prime_power q_mod_4_congruent_3
  Function.Injective ι := by
    unfold Function.Injective
    intro q_prime_power ι τ τ' h1
    unfold ι Elligator1.ι at h1
    let σ_injective := σ_injective field_cardinality q_prime q_mod_4_congruent_3
    let ϕ_of_τ := ϕ (σ τ.1) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let ϕ_of_τ' := ϕ (σ τ'.1) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    let ϕ_of_neg_τ := ϕ (-σ τ.1) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
    change ϕ_of_τ = ϕ_of_τ' at h1
    have h2 : ϕ_of_τ = ϕ_of_neg_τ  := by
      unfold ϕ_of_τ ϕ_of_neg_τ
      let h2_1 := ϕ_of_t_eq_ϕ_of_neg_t (σ τ.1) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
      grind
    have h3 : ϕ_of_neg_τ = ϕ_of_τ' := by grind
    have h4 : ¬ (∃ (p : { n : F // n ≠ (σ τ.1) ∧ n ≠ -(σ τ.1)}), ϕ p.val s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3 = ϕ_of_τ) := by
        let h4_1 := (ϕ_of_t_eq_ϕ_of_neg_t_iff_ϕ_preimages (σ τ.1) s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3).mp
        unfold ϕ_of_τ ϕ_of_neg_τ at h2
        convert h4_1 ( congr_arg Subtype.val h2 ) using 1
        simp +decide [ Subtype.ext_iff ]
        rfl
    have h5 : (@σ F _ q τ.1) = (@σ F _ q τ'.1) ∨ (@σ F _ q τ.1) = -(@σ F _ q τ'.1) := by
      simp_all
      grind
    -- Since τ and τ ∈ {0, ..., (q-1)/2}
    have h6 : (@σ F _ q τ.1) = (@σ F _ q τ'.1) := by
      cases' h5 with h6_1 h6_1 <;> simp_all +decide [ σ ];
      have h6_2 : bitsToNat τ.val = bitsToNat τ'.val := by
        have h6_2_1 : bitsToNat τ.val ≤ (q - 1) / 2 ∧ bitsToNat τ'.val ≤ (q - 1) / 2 := by exact ⟨bitsToNat_le_q_sub_one_over_two τ , bitsToNat_le_q_sub_one_over_two τ'⟩
        have h6_2_2 : (bitsToNat τ.val : F) = -((bitsToNat τ'.val) : F) := by grind
        let h6_2_3 := lower_half_neg_eq field_cardinality q_prime h6_2_1.1 h6_2_1.2 h6_2_2
        grind
      grind
    grind

lemma ϕ_over_F_eq_ι_over_S
  (s_h1 : s ≠ 0)
  (s_h2 : (s^2 - 2) * (s^2 + 2) ≠ 0)
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let ϕ_over_F := ϕ_over_F s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  let ι_over_S := ι_over_S s s_h1 s_h2 q field_cardinality q_prime_power q_mod_4_congruent_3
  ϕ_over_F = ι_over_S := by
    intro ϕ_over_F ι_over_S
    unfold ϕ_over_F Elligator1.ϕ_over_F
    -- TODO do original:
    --
    -- Each element of ι(S) has the form φ(σ(τ )) and is therefore
    --in φ(Fq ). Conversely, if P ∈ φ(Fq ) then P = φ(t) for some
    -- t ∈ Fq , so also P = φ(−t) by Theorem 3. At least one
    -- of t, −t is in {0, 1, . . . , (q − 1)/2}, i.e., in σ(S), so P is in
    -- φ(σ(S)) = ι(S)
    sorry
