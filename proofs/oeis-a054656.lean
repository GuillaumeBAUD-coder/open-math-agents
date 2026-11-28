import OMAStatements.S_oeis_a054656
import Mathlib

-- Problem: A054656: Number of primes <= n which do not appear in any partitions of n into distinct primes.
-- Upstream: formal-conjectures :0 (declaration OMA.S_oeis_a054656.main)
-- Credit: @avivorly (the owner of the agent is credited as the solver)

/-!
Proof of Bottomley's A054656 classification (n ≥ 23).

Plan.
* `two_primes_large`: for n ≥ 512 there are two primes in (n, 2n]. This is Mathlib's Erdős-style
  Bertrand argument with one allowed prime in (n, 2n]: the extra factor 2n it contributes is paid
  for by counting the small primes in [2, sqrt (2n)] instead of [1, sqrt (2n)].
* `p2_small`: the same for 6 ≤ n < 547 from an explicit chain of primes.
* `cov_step` (Richert's step) and `chain`: every x ≥ 13 is a sum of distinct primes avoiding any
  given p, starting from explicit bases (`base`, checked by the Boolean subset-sum checker `ss`).
* Assembly: for n ≥ 23 a prime p ≤ n is missing iff n - p ∈ {1, 4, 6}.
-/

namespace A054656Proof

section TwoPrimes

open Nat

theorem prod_small_le (n : ℕ) (n_large : 2 < n) :
    ∏ p ∈ Finset.range (2 * n / 3 + 1), p ^ (centralBinom n).factorization p ≤
      (2 * n) ^ (sqrt (2 * n) - 1) * 4 ^ (2 * n / 3) := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  let f x := x ^ n.centralBinom.factorization x
  have : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
  rw [← this, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ sqrt (2 * n))]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
    · exact pow_factorization_choose_le (mul_pos two_pos n_pos)
    have : (Finset.Icc 2 (sqrt (2 * n))).card = sqrt (2 * n) - 1 := by
      rw [card_Icc]; omega
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.two_le, h2⟩
  · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

theorem cb_le_one_prime (n : ℕ) (n_large : 2 < n) (p0 : ℕ)
    (only : ∀ p : ℕ, p.Prime → n < p → p ≤ 2 * n → p = p0) :
    centralBinom n ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have hsub : Finset.range (2 * n / 3 + 1) ⊆ Finset.range (2 * n + 1) :=
    Finset.range_subset_range.2 (by omega)
  have hsplit : (∏ x ∈ Finset.range (2 * n + 1) \ Finset.range (2 * n / 3 + 1),
        x ^ (centralBinom n).factorization x) *
      (∏ x ∈ Finset.range (2 * n / 3 + 1), x ^ (centralBinom n).factorization x) =
      centralBinom n := by
    rw [Finset.prod_sdiff hsub]
    exact prod_pow_factorization_centralBinom n
  have h1 : ∀ x ∈ Finset.range (2 * n + 1) \ Finset.range (2 * n / 3 + 1), x ≠ p0 →
      x ^ (centralBinom n).factorization x = 1 := by
    intro x hx hne
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hx
    by_cases hxp : x.Prime
    · by_cases hxn : x ≤ n
      · rw [factorization_centralBinom_of_two_mul_self_lt_three_mul n_large hxn (by omega),
          _root_.pow_zero]
      · exact absurd (only x hxp (by omega) (by omega)) hne
    · rw [factorization_eq_zero_of_not_prime _ hxp, _root_.pow_zero]
  have hrest : (∏ x ∈ Finset.range (2 * n + 1) \ Finset.range (2 * n / 3 + 1),
      x ^ (centralBinom n).factorization x) ≤ 2 * n := by
    by_cases hp0 : p0 ∈ Finset.range (2 * n + 1) \ Finset.range (2 * n / 3 + 1)
    · rw [Finset.prod_eq_single_of_mem p0 hp0 h1]
      exact pow_factorization_choose_le (by omega)
    · rw [Finset.prod_eq_one (fun x hx => h1 x hx (fun h => hp0 (h ▸ hx)))]
      omega
  have hsmall := prod_small_le n n_large
  have hs1 : sqrt (2 * n) ≠ 0 := by
    have : 1 ≤ sqrt (2 * n) := le_sqrt.2 (by omega)
    omega
  calc centralBinom n = _ := hsplit.symm
    _ ≤ (2 * n) * ((2 * n) ^ (sqrt (2 * n) - 1) * 4 ^ (2 * n / 3)) :=
        Nat.mul_le_mul hrest hsmall
    _ = (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) := by
        rw [← _root_.pow_sub_one_mul hs1 (2 * n)]
        ring

theorem two_primes_large (n : ℕ) (hn : 512 ≤ n) (p0 : ℕ) :
    ∃ q, q.Prime ∧ n < q ∧ q ≤ 2 * n ∧ q ≠ p0 := by
  by_contra hcon
  push_neg at hcon
  have h1 : 4 ^ n < n * centralBinom n := four_pow_lt_mul_centralBinom n (by omega)
  have h2 := cb_le_one_prime n (by omega) p0 hcon
  have h3 := bertrand_main_inequality hn
  have h4 : n * centralBinom n ≤ n * ((2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3)) :=
    Nat.mul_le_mul_left n h2
  rw [← mul_assoc] at h4
  exact absurd (h1.trans_le (h4.trans h3)) (lt_irrefl _)

end TwoPrimes

abbrev P2 (n : ℕ) : Prop := ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ n < a ∧ a < b ∧ b ≤ 2 * n

theorem p2_succ {n : ℕ} (q a b : ℕ) (ha : a.Prime) (hb : b.Prime) (hab : a < b)
    (hcov : b ≤ 2 * q) (H : n < q → P2 n) (hn : n < a) : P2 n := by
  by_cases h : n < q
  · exact H h
  · exact ⟨a, b, ha, hb, hn, hab, by omega⟩

theorem p2_small (n : ℕ) (h6 : 6 ≤ n) (h : n < 547) : P2 n := by
  refine p2_succ 316 547 631 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ h
  intro h
  refine p2_succ 274 317 547 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by omega)
  intro h
  refine p2_succ 159 277 317 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by omega)
  intro h
  refine p2_succ 139 163 277 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by omega)
  intro h
  refine p2_succ 82 139 163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by omega)
  intro h
  refine p2_succ 70 83 139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by omega)
  intro h
  refine p2_succ 42 73 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by omega)
  intro h
  refine p2_succ 37 43 73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by omega)
  intro h
  refine p2_succ 22 37 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by omega)
  intro h
  refine p2_succ 19 23 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by omega)
  intro h
  refine p2_succ 12 19 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by omega)
  intro h
  refine p2_succ 10 13 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by omega)
  intro h
  refine p2_succ 7 11 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by omega)
  intro h
  refine p2_succ 6 7 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by omega)
  intro h
  exact absurd h6 (by omega)

theorem exists_prime_ne (n p0 : ℕ) (hn : 6 ≤ n) :
    ∃ q, q.Prime ∧ n < q ∧ q ≤ 2 * n ∧ q ≠ p0 := by
  by_cases h : 512 ≤ n
  · exact two_primes_large n h p0
  · obtain ⟨a, b, ha, hb, hna, hab, hb2⟩ := p2_small n hn (by omega)
    by_cases hap : a = p0
    · exact ⟨b, hb, by omega, hb2, by omega⟩
    · exact ⟨a, ha, hna, by omega, hap⟩

/-- Every x in [13, M] is a sum of distinct primes, all at most B, avoiding p. -/
abbrev Cov (p B M : ℕ) : Prop :=
  ∀ x, 13 ≤ x → x ≤ M → ∃ s : Finset ℕ, (∀ q ∈ s, q.Prime ∧ q ≤ B) ∧ p ∉ s ∧ ∑ q ∈ s, q = x

theorem cov_step {p B M q : ℕ} (h : Cov p B M) (hq : q.Prime) (hBq : B < q) (hqM : q + 12 ≤ M)
    (hqp : q ≠ p) : Cov p q (M + q) := by
  intro x hx1 hx2
  by_cases hxM : x ≤ M
  · obtain ⟨s, hs, hps, hsum⟩ := h x hx1 hxM
    exact ⟨s, fun r hr => ⟨(hs r hr).1, (hs r hr).2.trans hBq.le⟩, hps, hsum⟩
  · obtain ⟨s, hs, hps, hsum⟩ := h (x - q) (by omega) (by omega)
    have hqs : q ∉ s := fun hm => by have := (hs q hm).2; omega
    refine ⟨insert q s, ?_, ?_, ?_⟩
    · intro r hr
      rw [Finset.mem_insert] at hr
      rcases hr with hr | hr
      · rw [hr]; exact ⟨hq, le_rfl⟩
      · exact ⟨(hs r hr).1, (hs r hr).2.trans hBq.le⟩
    · rw [Finset.mem_insert, not_or]
      exact ⟨fun h => hqp h.symm, hps⟩
    · rw [Finset.sum_insert hqs, hsum]
      omega

theorem chain (p B0 M0 : ℕ) (h0 : Cov p B0 M0) (hB0 : 6 ≤ B0) (hM0 : 2 * B0 + 12 ≤ M0) :
    ∀ k : ℕ, ∃ B M : ℕ, Cov p B M ∧ 6 ≤ B ∧ 2 * B + 12 ≤ M ∧ k ≤ M := by
  intro k
  induction k with
  | zero => exact ⟨B0, M0, h0, hB0, hM0, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨B, M, h, hB, hM, hk⟩ := ih
    obtain ⟨q, hq, hBq, hq2, hqp⟩ := exists_prime_ne B p hB
    exact ⟨q, M + q, cov_step h hq hBq (by omega) hqp, by omega, by omega, by omega⟩

/-- Boolean subset-sum checker: is x a sum of distinct entries of the list? -/
def ss : List ℕ → ℕ → Bool
  | [], x => x == 0
  | a :: L, x => (decide (a ≤ x) && ss L (x - a)) || ss L x

theorem ss_sound (L : List ℕ) : ∀ x : ℕ, L.Nodup → ss L x = true →
    ∃ s : Finset ℕ, (∀ q ∈ s, q ∈ L) ∧ ∑ q ∈ s, q = x := by
  induction L with
  | nil =>
    intro x _ h
    have hx : x = 0 := by simpa [ss] using h
    exact ⟨∅, by simp, by simp [hx]⟩
  | cons a L ih =>
    intro x hnd h
    rw [List.nodup_cons] at hnd
    simp only [ss, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨hax, h⟩ | h
    · obtain ⟨s, hs, hsum⟩ := ih (x - a) hnd.2 h
      have has : a ∉ s := fun ha => hnd.1 (hs a ha)
      refine ⟨insert a s, ?_, ?_⟩
      · intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with hq | hq
        · exact List.mem_cons.2 (Or.inl hq)
        · exact List.mem_cons.2 (Or.inr (hs q hq))
      · rw [Finset.sum_insert has, hsum]
        omega
    · obtain ⟨s, hs, hsum⟩ := ih x hnd.2 h
      exact ⟨s, fun q hq => List.mem_cons.2 (Or.inr (hs q hq)), hsum⟩

theorem cov_of_list (p B M : ℕ) (L : List ℕ) (hnd : L.Nodup) (hL : ∀ q ∈ L, q.Prime ∧ q ≤ B)
    (hp : p ∉ L) (hc : (List.range' 13 (M - 12)).all (ss L) = true) : Cov p B M := by
  intro x hx1 hx2
  rw [List.all_eq_true] at hc
  have hx : ss L x = true := hc x (List.mem_range'_1.2 ⟨hx1, by omega⟩)
  obtain ⟨s, hs, hsum⟩ := ss_sound L x hnd hx
  exact ⟨s, fun q hq => hL q (hs q hq), fun h => hp (hs p h), hsum⟩

theorem base (p : ℕ) : ∃ B M : ℕ, Cov p B M ∧ 6 ≤ B ∧ 2 * B + 12 ≤ M := by
  by_cases hp : p ∈ [17, 13, 11, 7, 5, 3, 2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨19, 50, cov_of_list 17 19 50 [19, 13, 11, 7, 5, 3, 2] (by decide) (by norm_num)
        (by decide) (by decide), by norm_num, by norm_num⟩
    · exact ⟨19, 50, cov_of_list 13 19 50 [19, 17, 11, 7, 5, 3, 2] (by decide) (by norm_num)
        (by decide) (by decide), by norm_num, by norm_num⟩
    · exact ⟨19, 50, cov_of_list 11 19 50 [19, 17, 13, 7, 5, 3, 2] (by decide) (by norm_num)
        (by decide) (by decide), by norm_num, by norm_num⟩
    · exact ⟨19, 50, cov_of_list 7 19 50 [19, 17, 13, 11, 5, 3, 2] (by decide) (by norm_num)
        (by decide) (by decide), by norm_num, by norm_num⟩
    · exact ⟨19, 50, cov_of_list 5 19 50 [19, 17, 13, 11, 7, 3, 2] (by decide) (by norm_num)
        (by decide) (by decide), by norm_num, by norm_num⟩
    · exact ⟨19, 50, cov_of_list 3 19 50 [19, 17, 13, 11, 7, 5, 2] (by decide) (by norm_num)
        (by decide) (by decide), by norm_num, by norm_num⟩
    · exact ⟨17, 46, cov_of_list 2 17 46 [17, 13, 11, 7, 5, 3] (by decide) (by norm_num)
        (by decide) (by decide), by norm_num, by norm_num⟩
  · exact ⟨17, 46, cov_of_list p 17 46 [17, 13, 11, 7, 5, 3, 2] (by decide) (by norm_num) hp
      (by decide), by norm_num, by norm_num⟩

/-- Key lemma: every x ≥ 13 is a sum of distinct primes avoiding p. -/
theorem key (p x : ℕ) (hx : 13 ≤ x) :
    ∃ s : Finset ℕ, (∀ q ∈ s, q.Prime) ∧ p ∉ s ∧ ∑ q ∈ s, q = x := by
  obtain ⟨B0, M0, h0, hB0, hM0⟩ := base p
  obtain ⟨B, M, h, -, -, hk⟩ := chain p B0 M0 h0 hB0 hM0 x
  obtain ⟨s, hs, hps, hsum⟩ := h x hx hk
  exact ⟨s, fun q hq => (hs q hq).1, hps, hsum⟩

theorem no_small_sum (t : Finset ℕ) (ht : ∀ q ∈ t, q.Prime)
    (h : ∑ q ∈ t, q = 1 ∨ ∑ q ∈ t, q = 4 ∨ ∑ q ∈ t, q = 6) : False := by
  have hsub : t ⊆ {2, 3, 5} := by
    intro q hq
    have h1 : q ≤ ∑ q ∈ t, q :=
      Finset.single_le_sum (f := fun q => q) (fun i _ => Nat.zero_le i) hq
    have h2 := ht q hq
    have h3 : q ≤ 6 := by omega
    have h4 := h2.two_le
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases q <;> first | omega | (exfalso; norm_num at h2)
  have hk : ∀ u ∈ ({2, 3, 5} : Finset ℕ).powerset,
      ¬ (∑ q ∈ u, q = 1 ∨ ∑ q ∈ u, q = 4 ∨ ∑ q ∈ u, q = 6) := by decide
  exact hk t (Finset.mem_powerset.2 hsub) h

theorem rep_avoid (n p : ℕ) (hn : 23 ≤ n) (hpn : p ≤ n) (h1 : n - p ≠ 1) (h4 : n - p ≠ 4)
    (h6 : n - p ≠ 6) : ∃ t : Finset ℕ, (∀ q ∈ t, q.Prime) ∧ p ∉ t ∧ ∑ q ∈ t, q = n - p := by
  by_cases hr : 13 ≤ n - p
  · exact key p (n - p) hr
  · obtain ⟨r, hr'⟩ : ∃ r, r = n - p := ⟨_, rfl⟩
    rw [← hr'] at h1 h4 h6 hr ⊢
    have hp11 : 11 ≤ p := by omega
    interval_cases r
    · exact ⟨∅, by simp, by simp, by simp⟩
    · exact (h1 rfl).elim
    · exact ⟨{2}, by norm_num, by simp; omega, by simp⟩
    · exact ⟨{3}, by norm_num, by simp; omega, by simp⟩
    · exact (h4 rfl).elim
    · exact ⟨{5}, by norm_num, by simp; omega, by simp⟩
    · exact (h6 rfl).elim
    · exact ⟨{7}, by norm_num, by simp; omega, by simp⟩
    · exact ⟨{3, 5}, by norm_num, by simp; omega, by decide⟩
    · exact ⟨{2, 7}, by norm_num, by simp; omega, by decide⟩
    · exact ⟨{3, 7}, by norm_num, by simp; omega, by decide⟩
    · exact ⟨{11}, by norm_num, by simp; omega, by simp⟩
    · exact ⟨{5, 7}, by norm_num, by simp; omega, by decide⟩

theorem appears_iff (n p : ℕ) (hn : 23 ≤ n) (hp : p.Prime) (hpn : p ≤ n) :
    OMA.S_oeis_a054656.Appears n p ↔ (n - p ≠ 1 ∧ n - p ≠ 4 ∧ n - p ≠ 6) := by
  unfold OMA.S_oeis_a054656.Appears
  constructor
  · rintro ⟨s, hs, hps, hsum⟩
    have he : ∑ q ∈ s.erase p, q + p = ∑ q ∈ s, q := Finset.sum_erase_add s (fun q => q) hps
    have ht : ∀ q ∈ s.erase p, q.Prime := fun q hq => hs q (Finset.mem_of_mem_erase hq)
    refine ⟨fun h => no_small_sum _ ht (by omega), fun h => no_small_sum _ ht (by omega),
      fun h => no_small_sum _ ht (by omega)⟩
  · rintro ⟨h1, h4, h6⟩
    obtain ⟨t, ht, hpt, htsum⟩ := rep_avoid n p hn hpn h1 h4 h6
    refine ⟨insert p t, ?_, Finset.mem_insert_self p t, ?_⟩
    · intro q hq
      rw [Finset.mem_insert] at hq
      rcases hq with hq | hq
      · rw [hq]; exact hp
      · exact ht q hq
    · rw [Finset.sum_insert hpt, htsum]
      omega

theorem even_not_prime (m : ℕ) (hm : 4 ≤ m) (he : m % 2 = 0) : ¬ m.Prime := by
  intro hp
  have := hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero he)
  omega

end A054656Proof

open A054656Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a054656.main := by
  intro n hn
  have hset : {p : ℕ | p.Prime ∧ p ≤ n ∧ ¬ OMA.S_oeis_a054656.Appears n p} =
      {p : ℕ | p.Prime ∧ (p = n - 6 ∨ p = n - 4 ∨ p = n - 1)} := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hp, hpn, hna⟩
      rw [appears_iff n p hn hp hpn] at hna
      exact ⟨hp, by omega⟩
    · rintro ⟨hp, hpe⟩
      have hpn : p ≤ n := by omega
      refine ⟨hp, hpn, ?_⟩
      rw [appears_iff n p hn hp hpn]
      omega
  rw [OMA.S_oeis_a054656.a, hset]
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have h6 : ¬ (n - 6).Prime := even_not_prime _ (by omega) (by omega)
    have h4 : ¬ (n - 4).Prime := even_not_prime _ (by omega) (by omega)
    by_cases h1 : (n - 1).Prime
    · have hs : {p : ℕ | p.Prime ∧ (p = n - 6 ∨ p = n - 4 ∨ p = n - 1)} = {n - 1} := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hp, hpe | hpe | hpe⟩
          · rw [hpe] at hp; exact absurd hp h6
          · rw [hpe] at hp; exact absurd hp h4
          · exact hpe
        · intro hpe
          rw [hpe]
          exact ⟨h1, Or.inr (Or.inr rfl)⟩
      rw [hs, Set.ncard_singleton]
      simp [h6, h4, h1]
    · have hs : {p : ℕ | p.Prime ∧ (p = n - 6 ∨ p = n - 4 ∨ p = n - 1)} = ∅ := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hp, hpe | hpe | hpe⟩
        · rw [hpe] at hp; exact h6 hp
        · rw [hpe] at hp; exact h4 hp
        · rw [hpe] at hp; exact h1 hp
      rw [hs, Set.ncard_empty]
      simp [h6, h4, h1]
  · have h1 : ¬ (n - 1).Prime := even_not_prime _ (by omega) (by omega)
    by_cases h6 : (n - 6).Prime <;> by_cases h4 : (n - 4).Prime
    · have hs : {p : ℕ | p.Prime ∧ (p = n - 6 ∨ p = n - 4 ∨ p = n - 1)} = {n - 6, n - 4} := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hp, hpe | hpe | hpe⟩
          · exact Or.inl hpe
          · exact Or.inr hpe
          · rw [hpe] at hp; exact absurd hp h1
        · rintro (hpe | hpe)
          · rw [hpe]; exact ⟨h6, Or.inl rfl⟩
          · rw [hpe]; exact ⟨h4, Or.inr (Or.inl rfl)⟩
      rw [hs, Set.ncard_pair (show n - 6 ≠ n - 4 by omega)]
      simp [h6, h4]
    · have hs : {p : ℕ | p.Prime ∧ (p = n - 6 ∨ p = n - 4 ∨ p = n - 1)} = {n - 6} := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hp, hpe | hpe | hpe⟩
          · exact hpe
          · rw [hpe] at hp; exact absurd hp h4
          · rw [hpe] at hp; exact absurd hp h1
        · intro hpe
          rw [hpe]
          exact ⟨h6, Or.inl rfl⟩
      rw [hs, Set.ncard_singleton]
      simp [h6, h4]
    · have hs : {p : ℕ | p.Prime ∧ (p = n - 6 ∨ p = n - 4 ∨ p = n - 1)} = {n - 4} := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hp, hpe | hpe | hpe⟩
          · rw [hpe] at hp; exact absurd hp h6
          · exact hpe
          · rw [hpe] at hp; exact absurd hp h1
        · intro hpe
          rw [hpe]
          exact ⟨h4, Or.inr (Or.inl rfl)⟩
      rw [hs, Set.ncard_singleton]
      simp [h6, h4]
    · have hs : {p : ℕ | p.Prime ∧ (p = n - 6 ∨ p = n - 4 ∨ p = n - 1)} = ∅ := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hp, hpe | hpe | hpe⟩
        · rw [hpe] at hp; exact h6 hp
        · rw [hpe] at hp; exact h4 hp
        · rw [hpe] at hp; exact h1 hp
      rw [hs, Set.ncard_empty]
      simp [h6, h4, h1]
