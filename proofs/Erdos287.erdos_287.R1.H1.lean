import OMAReductions.R_Erdos287_erdos_287_R1

/-!
# Proof of `Erdos287.erdos_287.R1.H1`

Proves Erdős's 1932 theorem that if `k ≥ 2`, `s : Fin k → ℕ` is strictly monotone with `1 < s 0`,
and `∑ i : Fin k, 1 / (s i : ℝ) = 1`, then `2 ≤ max_gap k s`.

Suppose for contradiction that `max_gap k s < 2`. Since `s` is strictly monotone, every consecutive
gap `s (i + 1) - s i` equals `1`, so `s i = a + i` for `a = s 0 ≥ 2`. Let `e` be the maximum
`2`-adic valuation `padicValNat 2 (a + i)` over `i ∈ Fin k`. Since `k ≥ 2`, the interval
`[a, a + k - 1]` contains an even integer, so `e ≥ 1`. Moreover, the maximizer `i₀` is unique: if
`a + i₁ < a + i₂` both had valuation `e`, writing them as `2^e * m₁` and `2^e * m₂` with odd
`m₁ < m₂`, then `2^e * (m₁ + 1)` lies strictly between them and is divisible by `2^(e + 1)`,
contradicting maximality of `e`.

Clearing denominators by `2 ^ (e - 1) * M` where `M = ∏ i : Fin k, (s i) / 2 ^ (padicValNat 2 (s i))`
is odd, every term `i ≠ i₀` becomes an integer, while the `i₀` term has numerator an odd integer
and denominator `2`, contradicting that the sum equals `1` (an integer).
-/

namespace Erdos287R1H1Proof

open Erdos287 Finset

private lemma consecutive_of_max_gap_lt_two {k : ℕ} (hk : 2 ≤ k) {s : Fin k → ℕ}
    (hs : StrictMono s) (hgap : max_gap k s < 2) :
    ∀ i : Fin k, s i = s ⟨0, by omega⟩ + i.val := by
  intro ⟨j, hj⟩
  induction j with
  | zero => simp
  | succ m ih =>
    have hm : m < k - 1 := by omega
    have hstep_le : s ⟨m + 1, hj⟩ - s ⟨m, by omega⟩ ≤ max_gap k s :=
      Finset.le_sup (f := fun i : Fin (k - 1) => s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)
        (Finset.mem_univ ⟨m, hm⟩)
    have hlt : s ⟨m, by omega⟩ < s ⟨m + 1, hj⟩ := hs (show (⟨m, by omega⟩ : Fin k) < ⟨m + 1, hj⟩ from Nat.lt_succ_self m)
    have hih := ih (by omega)
    dsimp only at hih ⊢
    omega

private lemma exists_unique_max_v2 {a k : ℕ} (ha : 2 ≤ a) (hk : 2 ≤ k) :
    ∃ i₀ : Fin k, 1 ≤ padicValNat 2 (a + i₀.val) ∧
      ∀ i : Fin k, i ≠ i₀ → padicValNat 2 (a + i.val) < padicValNat 2 (a + i₀.val) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, _, hi₀_max⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin k => padicValNat 2 (a + i.val)) hne
  set e := padicValNat 2 (a + i₀.val)
  -- At least one of a, a + 1 is even, so e ≥ 1
  have he1 : 1 ≤ e := by
    by_cases hae : 2 ∣ a
    · have h1 : 1 ≤ padicValNat 2 (a + 0) := by
        rw [add_zero]
        exact one_le_padicValNat_of_dvd (by omega) hae
      have h2 := hi₀_max ⟨0, by omega⟩ (Finset.mem_univ _)
      exact le_trans h1 h2
    · have ha1e : 2 ∣ a + 1 := by omega
      have h1 : 1 ≤ padicValNat 2 (a + 1) := one_le_padicValNat_of_dvd (by omega) ha1e
      have h2 := hi₀_max ⟨1, by omega⟩ (Finset.mem_univ _)
      exact le_trans h1 h2
  refine ⟨i₀, he1, fun i hi => ?_⟩
  have hle : padicValNat 2 (a + i.val) ≤ e := hi₀_max i (Finset.mem_univ _)
  by_contra hnot
  have heq : padicValNat 2 (a + i.val) = e := by omega
  have hdvd1 : 2 ^ e ∣ a + i.val := by
    rw [← heq]; exact pow_padicValNat_dvd
  have hdvd2 : 2 ^ e ∣ a + i₀.val := pow_padicValNat_dvd
  obtain ⟨m1, hm1⟩ := hdvd1
  obtain ⟨m2, hm2⟩ := hdvd2
  have hm1_odd : Odd m1 := by
    by_contra hev
    obtain ⟨t, ht⟩ := Nat.not_odd_iff_even.mp hev
    have hdvd_next : 2 ^ (e + 1) ∣ a + i.val := by
      refine ⟨t, ?_⟩
      rw [hm1, ht, pow_succ]; ring
    have hge : e + 1 ≤ padicValNat 2 (a + i.val) :=
      (padicValNat_dvd_iff_le (by omega)).mp hdvd_next
    omega
  have hm2_odd : Odd m2 := by
    by_contra hev
    obtain ⟨t, ht⟩ := Nat.not_odd_iff_even.mp hev
    have hdvd_next : 2 ^ (e + 1) ∣ a + i₀.val := by
      refine ⟨t, ?_⟩
      rw [hm2, ht, pow_succ]; ring
    have hge : e + 1 ≤ padicValNat 2 (a + i₀.val) :=
      (padicValNat_dvd_iff_le (by omega)).mp hdvd_next
    omega
  have hmne : m1 ≠ m2 := by
    intro h
    apply hi
    apply Fin.ext
    rw [h] at hm1
    omega
  -- Midpoint 2^e * (min m1 m2 + 1) lies strictly between a + i and a + i₀ and is divisible by 2^(e+1)
  have hmid : ∃ j : Fin k, 2 ^ (e + 1) ∣ a + j.val := by
    rcases lt_or_gt_of_ne hmne with hlt | hgt
    · have hmid_val : a + i.val < 2 ^ e * (m1 + 1) ∧ 2 ^ e * (m1 + 1) < a + i₀.val := by
        have hpos : 0 < 2 ^ e := pow_pos (by decide) e
        rw [hm1, hm2]
        obtain ⟨u1, hu1⟩ := hm1_odd
        obtain ⟨u2, hu2⟩ := hm2_odd
        have : m1 + 1 < m2 := by omega
        constructor <;> nlinarith
      refine ⟨⟨2 ^ e * (m1 + 1) - a, by omega⟩, ?_⟩
      have heq_j : a + (2 ^ e * (m1 + 1) - a) = 2 ^ e * (m1 + 1) := by omega
      rw [heq_j]
      obtain ⟨u1, hu1⟩ := hm1_odd
      refine ⟨u1 + 1, ?_⟩
      rw [hu1, pow_succ]; ring
    · have hmid_val : a + i₀.val < 2 ^ e * (m2 + 1) ∧ 2 ^ e * (m2 + 1) < a + i.val := by
        have hpos : 0 < 2 ^ e := pow_pos (by decide) e
        rw [hm1, hm2]
        obtain ⟨u1, hu1⟩ := hm1_odd
        obtain ⟨u2, hu2⟩ := hm2_odd
        have : m2 + 1 < m1 := by omega
        constructor <;> nlinarith
      refine ⟨⟨2 ^ e * (m2 + 1) - a, by omega⟩, ?_⟩
      have heq_j : a + (2 ^ e * (m2 + 1) - a) = 2 ^ e * (m2 + 1) := by omega
      rw [heq_j]
      obtain ⟨u2, hu2⟩ := hm2_odd
      refine ⟨u2 + 1, ?_⟩
      rw [hu2, pow_succ]; ring
  obtain ⟨j, hj⟩ := hmid
  have hge : e + 1 ≤ padicValNat 2 (a + j.val) :=
    (padicValNat_dvd_iff_le (by omega)).mp hj
  have hmax_j := hi₀_max j (Finset.mem_univ _)
  omega

end Erdos287R1H1Proof

theorem OMA.solution : OMA.R_Erdos287_erdos_287_R1.H1 := by
  intro k hk s hs h0 hsum
  by_contra hlt
  have hgap : Erdos287.max_gap k s < 2 := by omega
  set a := s ⟨0, by omega⟩
  have ha : 2 ≤ a := by omega
  have hconsec : ∀ i : Fin k, s i = a + i.val :=
    Erdos287R1H1Proof.consecutive_of_max_gap_lt_two hk hs hgap
  obtain ⟨i₀, he1, huniq⟩ := Erdos287R1H1Proof.exists_unique_max_v2 ha hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e := padicValNat 2 (a + i₀.val)
  -- Odd part of each s i
  let oddPart : Fin k → ℕ := fun i => (a + i.val) / 2 ^ (padicValNat 2 (a + i.val))
  have hoddPart_mul : ∀ i : Fin k, 2 ^ (padicValNat 2 (a + i.val)) * oddPart i = a + i.val :=
    fun i => Nat.mul_div_cancel' pow_padicValNat_dvd
  have hoddPart_odd : ∀ i : Fin k, Odd (oddPart i) := fun i => by
    by_contra hev
    obtain ⟨t, ht⟩ := Nat.not_odd_iff_even.mp hev
    have hdvd : 2 ^ (padicValNat 2 (a + i.val) + 1) ∣ a + i.val := by
      refine ⟨t, ?_⟩
      calc a + i.val = 2 ^ (padicValNat 2 (a + i.val)) * oddPart i := (hoddPart_mul i).symm
        _ = 2 ^ (padicValNat 2 (a + i.val)) * (t + t) := by rw [ht]
        _ = 2 ^ (padicValNat 2 (a + i.val) + 1) * t := by rw [pow_succ]; ring
    have hge : padicValNat 2 (a + i.val) + 1 ≤ padicValNat 2 (a + i.val) :=
      (padicValNat_dvd_iff_le (by omega)).mp hdvd
    omega
  set M : ℕ := ∏ i : Fin k, oddPart i
  have hM_odd : Odd M := by
    have : ∀ (t : Finset (Fin k)), Odd (∏ i ∈ t, oddPart i) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | insert x t hx ih =>
        rw [Finset.prod_insert hx]
        exact (hoddPart_odd x).mul ih
    exact this Finset.univ
  have hoddPart_dvd_M : ∀ i : Fin k, oddPart i ∣ M := fun i =>
    Finset.dvd_prod_of_mem oddPart (Finset.mem_univ i)
  -- Multiply ∑ 1 / (s i) = 1 by 2 ^ (e - 1) * M
  have hmul_sum :
      ∑ i : Fin k, ((2 ^ (e - 1) * M : ℕ) : ℝ) / ((a + i.val : ℕ) : ℝ) =
        ((2 ^ (e - 1) * M : ℕ) : ℝ) := by
    calc ∑ i : Fin k, ((2 ^ (e - 1) * M : ℕ) : ℝ) / ((a + i.val : ℕ) : ℝ)
        = ∑ i : Fin k, ((2 ^ (e - 1) * M : ℕ) : ℝ) * (1 / (s i : ℝ)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hconsec i, mul_one_div]
      _ = ((2 ^ (e - 1) * M : ℕ) : ℝ) * ∑ i : Fin k, 1 / (s i : ℝ) := (Finset.mul_sum ..).symm
      _ = ((2 ^ (e - 1) * M : ℕ) : ℝ) := by rw [hsum, mul_one]
  -- Split off i₀
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hmul_sum
  -- Every term i ≠ i₀ is an exact natural number
  have hother_nat : ∀ i ∈ Finset.univ.erase i₀,
      ∃ q : ℕ, ((2 ^ (e - 1) * M : ℕ) : ℝ) / ((a + i.val : ℕ) : ℝ) = (q : ℝ) := by
    intro i hi
    have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    have hlt_v : padicValNat 2 (a + i.val) ≤ e - 1 := by
      have := huniq i hne; omega
    have hdvd2 : 2 ^ (padicValNat 2 (a + i.val)) ∣ 2 ^ (e - 1) := Nat.pow_dvd_pow 2 hlt_v
    have hdvd_si : a + i.val ∣ 2 ^ (e - 1) * M := by
      rw [← hoddPart_mul i]
      exact mul_dvd_mul hdvd2 (hoddPart_dvd_M i)
    obtain ⟨q, hq⟩ := hdvd_si
    refine ⟨q, ?_⟩
    have hpos : ((a + i.val : ℕ) : ℝ) ≠ 0 := by positivity
    rw [hq, Nat.cast_mul, mul_div_cancel_left₀ _ hpos]
  choose q hq using hother_nat
  have hsum_nat : ∑ i ∈ Finset.univ.erase i₀,
      ((2 ^ (e - 1) * M : ℕ) : ℝ) / ((a + i.val : ℕ) : ℝ) =
      ((∑ i ∈ (Finset.univ.erase i₀).attach, q i.1 i.2 : ℕ) : ℝ) := by
    rw [Nat.cast_sum, ← Finset.sum_attach (Finset.univ.erase i₀)]
    refine Finset.sum_congr rfl fun i _ => hq i.1 i.2
  set Q : ℕ := ∑ i ∈ (Finset.univ.erase i₀).attach, q i.1 i.2
  -- Compute the i₀ term: (2^(e-1) * M) / (2^e * oddPart i₀) = (M / oddPart i₀) / 2
  set K : ℕ := ∏ i ∈ Finset.univ.erase i₀, oddPart i
  have hM_eq : M = oddPart i₀ * K := (Finset.mul_prod_erase Finset.univ oddPart (Finset.mem_univ i₀)).symm
  have hK_odd : Odd K := by
    rw [hM_eq] at hM_odd
    exact (Nat.odd_mul.mp hM_odd).2
  have hi₀_term : ((2 ^ (e - 1) * M : ℕ) : ℝ) / ((a + i₀.val : ℕ) : ℝ) = (K : ℝ) / 2 := by
    have hden : a + i₀.val = 2 * 2 ^ (e - 1) * oddPart i₀ := by
      rw [← hoddPart_mul i₀]
      have hpow : 2 ^ e = 2 * 2 ^ (e - 1) := by
        conv_lhs => rw [show e = (e - 1) + 1 by omega, pow_succ']
      rw [hpow]
    rw [hM_eq, hden]
    push_cast
    have h1 : (2 : ℝ) ^ (e - 1) ≠ 0 := by positivity
    have h2 : (oddPart i₀ : ℝ) ≠ 0 := by
      have : oddPart i₀ ≠ 0 := by
        intro h0; have := hoddPart_mul i₀; rw [h0, mul_zero] at this; omega
      exact Nat.cast_ne_zero.mpr this
    field_simp [h1, h2]
  rw [hi₀_term, hsum_nat] at hmul_sum
  have h2eq : (K : ℝ) + 2 * (Q : ℝ) = 2 * ((2 ^ (e - 1) * M : ℕ) : ℝ) := by linarith
  have h2nat : K + 2 * Q = 2 * (2 ^ (e - 1) * M) := by exact_mod_cast h2eq
  have hK_even : Even K := by
    have : 2 ∣ K := by omega
    exact even_iff_two_dvd.mpr this
  exact Nat.not_even_iff_odd.mpr hK_odd hK_even
