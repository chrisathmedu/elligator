import Mathlib

variable {F : Type*} [Field F] [Fintype F]

namespace FiniteFieldBasic

lemma q_ne_two
  (q : ℕ)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : q ≠ 2 := by
    intro h
    have mod_two : 2 % 4 = 2 := by norm_num
    nth_rw 1 [← h] at mod_two
    rw [q_mod_4_congruent_3] at mod_two
    norm_num at mod_two

lemma q_mod_2_congruent_1
  (q : ℕ)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  q % 2 = 1 := by
    exact Nat.odd_of_mod_four_eq_three q_mod_4_congruent_3

lemma q_odd
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  Odd (Fintype.card F) := by
    rw [field_cardinality]
    rw [IsPrimePow] at q_prime_power
    have hq: q % 2 = 1 := by apply q_mod_2_congruent_1 q q_mod_4_congruent_3
    have hq1: ∃ k, q = 2 * k + 1 := by
      apply Nat.mod_eq_iff.1 at hq
      cases hq
      · simp_all
      · simp_all
    rw [Odd]
    exact hq1

lemma q_add_one_even
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  Even (q + 1) := by
    refine Nat.even_add_one.mpr ?_
    have h0: Odd (Fintype.card F) := by
      apply q_odd q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [field_cardinality] at h0
    exact Nat.not_even_iff_odd.mpr h0

lemma q_sub_one_even
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  Even (Fintype.card F - 1) := by
    rw [field_cardinality]
    --apply Nat.Prime.even_sub_one q_prime_power (q_ne_two q q_prime_power q_mod_4_congruent_3)
    -- TODO use:
    --apply Odd.mul
    have hq: Odd q := by
      rw [<- field_cardinality]
      apply q_odd q field_cardinality q_prime_power q_mod_4_congruent_3
    rw [Odd] at hq
    rw [Even]
    cases hq
    rename_i k hk
    use k
    simp_all
    linarith

lemma q_sub_one_dvd_two
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : 2 ∣ Fintype.card F - 1 := by
    apply Even.two_dvd (q_sub_one_even q field_cardinality q_prime_power q_mod_4_congruent_3)

lemma q_not_dvd_two
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  : ¬(2 ∣ q) := by
    intro h
    -- Since q is prime and (q % 4 = 3 => q ≠ 2), it cannot divide 2.
    -- So in this assumption, q must be 2.
    --rw [Nat.prime_dvd_prime_iff_eq q_prime_power (Nat.prime_two)] at h
    --apply q_ne_two q q_prime_power q_mod_4_congruent_3 at h
    --have h1 : q ≠ 2 := q_ne_two q q_prime_power q_mod_4_congruent_3
    --contradiction
    have hq: Odd q := by
      rw [<- field_cardinality]
      apply q_odd q field_cardinality q_prime_power q_mod_4_congruent_3
    have hq': Even q := by
      exact (even_iff_exists_two_nsmul q).mpr h
    have hq'': Odd q → ¬ Even q := by
      intro h1
      exact Nat.not_even_iff_odd.mpr hq
    simp_all

lemma power_odd_p_odd
  (p k : ℕ)
  (hk: 0 < k)
  (hp: Odd (p^k))
  :
  Odd p := by
    cases k
    · simp_all
    · rename_i k
      have hpn_one: p^(k+1) = p^k * p := by ring
      -- cases hp
      --rename_i k1 hk1
      have h: Odd (p^k * p) → Odd (p^k) ∧ Odd p := by
        exact fun a ↦ (fun {m n} ↦ Nat.odd_mul.mp) a
      rw [hpn_one] at hp
      have h': Odd (p^k) ∧ Odd p := by apply h hp
      simp_all

lemma odd_prime_power_gt_two
  (q : ℕ)
  (q_prime_power : IsPrimePow q)
  (hq: Odd q)
  :
  q > 2 := by
    rw [IsPrimePow] at q_prime_power
    cases q_prime_power
    rename_i p hk
    cases hk
    rename_i k hp
    cases hp
    rename_i right
    cases right
    rename_i hprime k_gt_zero q_p_power
    have odd_p_pow_k: Odd (p^k) := by
      rw [<- q_p_power] at hq
      exact hq
    have hp: Odd p := by apply power_odd_p_odd p k k_gt_zero odd_p_pow_k
    have hp1: p > 2 := by
      refine Nat.two_lt_of_ne ?_ ?_ ?_
      · intro h_zero
        simp_all
      · intro h_one
        simp_all
      · intro p_two
        rw [p_two] at hp
        have even_two: Even 2 := by
          exact Nat.even_iff.mpr rfl
        have not_odd_two: ¬ Odd 2 := by exact Nat.not_odd_iff_even.mpr even_two
        contradiction
    have h_p_pow_gt_two: p^k > 2 := by
      cases k
      · simp_all
      · rename_i k
        have p_k_p_one: p^(k+1) = p^k * p := by ring
        rw [p_k_p_one]
        have p_k_gt_zero: p^k > 0 := by
          refine Nat.pow_pos ?_
          linarith
        exact lt_mul_of_one_le_of_lt p_k_gt_zero hp1
    simp_all

lemma one_ne_zero
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  (1 : F) ≠ 0 := by
    have he: Odd (-1 : F) := by
      rw [Odd]
      use (-1)
      ring
    have hne: Even (0 : F) := by
      rw [Even]
      use 0
      simp
    simp_all

lemma q_add_one_over_four_ne_zero
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  (1 + q) / 4 ≠ 0 := by
    apply Nat.div_ne_zero_iff.2
    constructor
    · norm_num
    · sorry

lemma two_ne_zero
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  (2 : F) ≠ 0 := by
    intro h
    have hq0: Odd q := by
      rw [<- field_cardinality]
      apply q_odd q field_cardinality q_prime_power q_mod_4_congruent_3
    have hq: q > 2 := by apply odd_prime_power_gt_two q q_prime_power hq0
    simp_all
    have h1 : (2 : F) = 0 ↔ 2 ∣ q := by
      constructor
      · intro h1
        sorry
      · intro h2
        exact h
    rw [h1] at h
    --apply prime_two_or_dvd_of_dvd_two_mul_pow_self_two q_prime_power h
    --apply h1.2
    -- Because q prime and does not divide 2, 2 cannot be zero since q is
    -- 0 in a field with q elements!
    have h2 : ¬(2 ∣ q) := by
      apply q_not_dvd_two q field_cardinality q_prime_power q_mod_4_congruent_3
    contradiction

lemma three_ne_zero
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  (3 : F) ≠ 0 := by
    have he: Odd (3 : F) := by
      rw [Odd]
      use (1)
      ring_nf
    have hne: Even (0 : F) := by
      rw [Even]
      use 0
      simp
    simp_all
    sorry

lemma four_ne_zero
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  (4 : F) ≠ 0 := by
    have h1 : (4 : F) = 2 * 2 := by norm_num
    rw [h1]
    apply mul_ne_zero
    · exact (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)
    · exact (FiniteFieldBasic.two_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3)

lemma neg_one_ne_zero
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  (-1 : F) ≠ 0 := by
    have he: Odd (-1 : F) := by
      rw [Odd]
      use (-1)
      ring
    have hne: Even (0 : F) := by
      rw [Even]
      use 0
      simp
    simp_all

lemma neg_one_non_square
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ¬IsSquare (-1 : F) :=
    sorry

lemma three_nonsquare
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  ¬IsSquare (3 : F) := by
    apply Prime.not_isSquare
    unfold Prime
    constructor
    · exact three_ne_zero q field_cardinality q_prime_power q_mod_4_congruent_3
    · constructor
      · unfold IsUnit
        intro u
        sorry
      · sorry

lemma p_odd_power_odd
  (p k : ℕ)
  (hp: Odd p)
  :
  Odd (p^k) := by
    induction' k
    · simp
    · rename_i n hn
      rw [Odd] at hn
      cases hn
      rename_i k hyp
      have hpn_one: p^(n+1) = p^n * p := by ring
      rw [Odd, hpn_one]
      rw [Odd] at hp
      cases hp
      rename_i k1 hp
      rw [hyp] at hpn_one
      nth_rw 2 [hp] at hpn_one
      have h0: (2*k+1)*(2*k1 + 1) = 4*k*k1 + 2*k + 2*k1 + 1 := by ring
      have h1: 4*k*k1 + 2*k + 2*k1 + 1 = 2*(2*k*k1 + k + k1) + 1:= by ring
      use 2*k*k1 + k + k1
      simp_all

lemma q_sub_one_over_two_ne_zero
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  (q - 1) / 2 ≠ 0 := by
    have q_odd: Odd q := by
        rw [<- field_cardinality]
        apply q_odd q field_cardinality q_prime_power q_mod_4_congruent_3
    apply Nat.div_ne_zero_iff.2
    constructor
    · norm_num
    · rw [IsPrimePow] at q_prime_power
      cases q_prime_power
      rename_i p hp
      cases hp
      rename_i k hk
      cases hk
      rename_i hp hpk
      cases hpk
      rename_i hk hpk
      have p_power_odd: Odd (p^k) := by
        rw [<- hpk] at q_odd
        exact q_odd

      have p_odd: Odd p := by
        apply power_odd_p_odd p k hk p_power_odd

      have q_gte_q: q ≥ p := by
        simp_all
        rw [<- hpk]
        exact Nat.le_pow hk
      have p_gt_2: p > 2 := by
        simp_all
        refine odd_prime_power_gt_two p ?_ p_odd
        rw [IsPrimePow]
        use p, 1
        simp_all
      simp_all
      refine (Nat.le_sub_one_iff_lt ?_).mpr ?_
      · refine Nat.zero_lt_of_ne_zero ?_
        intro hq
        simp_all
      · exact Nat.lt_of_lt_of_le p_gt_2 q_gte_q

lemma pow_two_ne_zero
  {a : F}
  (a_ne_zero : a ≠ 0)
  :
  a^2 ≠ 0 := by
    rw [pow_two]
    apply mul_ne_zero
    · exact a_ne_zero
    · exact a_ne_zero

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
      rw [← add_left_inj (-1 : F)] at h
      ring_nf at h
      exact h
    have h2 : t.val ≠ -1 := by
      apply And.right
      exact t.property
    contradiction

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

lemma neg_t_ne_one_and_neg_t_ne_neg_one
  (t : { t : F // t ≠ 1 ∧ t ≠ -1})
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_prime_power : IsPrimePow q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let t1 := t.val
  let t2 := -t1
  t2 ≠ 1 ∧ t2 ≠ -1 := by
    intro t1 t2
    rw [ne_eq, ne_eq]
    constructor
    · intro h2_2_1
      have h2_2_1_1 : t1 = -1 := by
        rw [← neg_one_mul]
        nth_rw 2 [← h2_2_1]
        unfold t2
        simp
      have h2_2_1_2 : t1 ≠ -1 := by exact t.property.right
      contradiction
    · intro h2_2_2
      have h2_2_1_1 : t1 = 1 := by
        unfold t2 at h2_2_2
        simp at h2_2_2
        exact h2_2_2
      have h2_2_1_2 : t1 ≠ 1 := by exact t.property.left
      contradiction

lemma one_add_card_mod_four_eq_zero
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  (1 + Fintype.card F) % 4 = 0 := by
    omega

lemma four_dvd_one_add_card
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  4 ∣ (1 + Fintype.card F) := by
    exact Nat.dvd_of_mod_eq_zero (one_add_card_mod_four_eq_zero q field_cardinality q_mod_4_congruent_3)

lemma one_add_card_over_four_mul_two_eq_one_add_card_over_two
  (q : ℕ)
  (field_cardinality : Fintype.card F = q)
  (q_mod_4_congruent_3 : q % 4 = 3)
  :
  let card := Fintype.card F
  ((1 + card) / 4 * 2) = (1 + card) / 2 := by
    intro card
    obtain ⟨k, hk⟩ := four_dvd_one_add_card q field_cardinality q_mod_4_congruent_3
    rw [hk]
    nth_rw 3 [mul_comm]
    simp_all
    rw [Nat.mul_div_assoc]
    simp_all

lemma card_sub_one_over_four_mul_two_eq_one_add_card_over_two
  {q : ℕ}
  :
  (q - 1) / 2 = (q + 1) / 2 - 1 := by
    omega
