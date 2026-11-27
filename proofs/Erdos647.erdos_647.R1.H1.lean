import OMAReductions.R_Erdos647_erdos_647_R1
import Mathlib

-- Step Erdos647.erdos_647.R1.H1: hypothesis H1 of reduction Erdos647.erdos_647
-- Credit: @Errnolink

/-!
# The divisor count satisfies `τ m ^ 6 ≤ 139 ^ 6 * m`

Write `m = ∏ p ^ a`. Then `τ m = ∏ (a + 1)`, so `τ m ^ 6 / m = ∏ (a + 1) ^ 6 / p ^ a`.
For a fixed `p` the factor `(a + 1) ^ 6 / p ^ a` decreases once `a ≥ 8` (`mono6`), so its
maximum is taken at some `a ≤ 8`, and the factor is at most `1` when `p ≥ 64`. Maximising prime
by prime over the eighteen primes below `64` (`T`) gives a product `3 %` below `139 ^ 6`.
-/

namespace OMA647

open ArithmeticFunction.sigma

/-- Multiplication by a constant on the left preserves `≤`. -/
lemma mml {a b : ℕ} (h : a ≤ b) (c : ℕ) : c * a ≤ c * b := Nat.mul_le_mul (le_refl c) h

/-- Multiplication by a constant on the right preserves `≤`. -/
lemma mmr {a b : ℕ} (h : a ≤ b) (c : ℕ) : a * c ≤ b * c := Nat.mul_le_mul h (le_refl c)

/-- The exponent where `(a + 1) ^ 6 / p ^ a` is largest, for the primes below `64`. -/
def A (p : ℕ) : ℕ :=
  if p = 2 then 8 else if p = 3 then 4 else if p = 5 then 3 else if p = 7 then 2 else
    if p = 11 then 2 else 1

/-- The primes below `64`. -/
def T : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61}

/-- The credit carried by a prime below `64`. -/
def c (p : ℕ) : ℕ := p ^ A p

/-- The allowance granted to a prime below `64`. -/
def u (p : ℕ) : ℕ := A p + 1

/-- Membership in `T` as an explicit disjunction. -/
lemma T_eq (p : ℕ) (hp : p ∈ T) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨
      p = 31 ∨ p = 37 ∨ p = 41 ∨ p = 43 ∨ p = 47 ∨ p = 53 ∨ p = 59 ∨ p = 61 := by
  simpa only [T, Finset.mem_insert, Finset.mem_singleton] using hp

lemma mem_T (p : ℕ) (hp : p ∈ T) : p.Prime ∧ 2 ≤ p ∧ p < 64 := by
  rcases T_eq p hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by omega, by omega⟩

lemma not_mem_T (p : ℕ) (hp : p.Prime) (hT : p ∉ T) : 64 ≤ p := by
  by_contra h
  have hlt : p < 64 := by omega
  interval_cases p <;> simp [T] at hT <;> exact absurd hp (by decide)

lemma A_of_not_mem_T {p : ℕ} (h : 64 ≤ p) : A p = 1 := by
  unfold A
  split_ifs <;> omega

/-- The finitely many cases `a ≤ 8` for the primes below `64`. -/
lemma check_T : ∀ p ∈ T, ∀ k, 1 ≤ k → k ≤ 8 → (k + 1) ^ 6 * c p ≤ (u p) ^ 6 * p ^ k := by
  intro p hp k hk1 hk8
  rcases T_eq p hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals interval_cases k <;> simp only [c, u, A, reduceIte] <;> decide

lemma c_le_u : ∀ q ∈ T, c q ≤ (u q) ^ 6 := by
  intro q hq
  rcases T_eq q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals simp only [c, u, A, reduceIte] <;> decide

/-- `(n + 1) ^ 6 / n ^ 6 ≤ 2` for `8 ≤ n`. -/
lemma ratio6 {n : ℕ} (hn : 8 ≤ n) : (n + 2) ^ 6 ≤ 2 * (n + 1) ^ 6 := by
  have h1 : 9 * (n + 2) ≤ 10 * (n + 1) := by omega
  have h5 : 10 ^ 6 ≤ 2 * 9 ^ 6 := by decide
  have h6 : (9 * (n + 2)) ^ 6 ≤ (10 * (n + 1)) ^ 6 := Nat.pow_le_pow_left h1 6
  have h7 : 9 ^ 6 * (n + 2) ^ 6 ≤ 9 ^ 6 * (2 * (n + 1) ^ 6) := by
    calc 9 ^ 6 * (n + 2) ^ 6 = (9 * (n + 2)) ^ 6 := by ring
      _ ≤ (10 * (n + 1)) ^ 6 := h6
      _ = 10 ^ 6 * (n + 1) ^ 6 := by ring
      _ ≤ 2 * 9 ^ 6 * (n + 1) ^ 6 := mmr h5 _
      _ = 9 ^ 6 * (2 * (n + 1) ^ 6) := by ring
  exact Nat.le_of_mul_le_mul_left h7 (by decide : 0 < 9 ^ 6)

/-- The factor `(a + 1) ^ 6 / p ^ a` decreases for `a ≥ 8`. -/
lemma mono6 (p : ℕ) (hp : 2 ≤ p) : ∀ j : ℕ, (j + 9) ^ 6 * p ^ 8 ≤ 9 ^ 6 * p ^ (j + 8) := by
  intro j
  induction j with
  | zero => simp
  | succ n ih =>
    have hr0 := ratio6 (n := n + 8) (by omega)
    have hr1 : (n + 9 + 1) ^ 6 ≤ 2 * (n + 9) ^ 6 := by
      convert hr0 using 1 <;> ring
    have hr : (n + 9 + 1) ^ 6 ≤ p * (n + 9) ^ 6 := hr1.trans (mmr (by omega) _)
    calc (n + 9 + 1) ^ 6 * p ^ 8 ≤ (p * (n + 9) ^ 6) * p ^ 8 := mmr hr _
      _ = p * ((n + 9) ^ 6 * p ^ 8) := by ring
      _ ≤ p * (9 ^ 6 * p ^ (n + 8)) := mml ih _
      _ = 9 ^ 6 * p ^ (n + 8 + 1) := by rw [pow_succ]; ring

lemma pow6_le : ∀ k, 0 < k → (k + 1) ^ 6 ≤ 64 ^ k := by
  intro k hk
  by_cases hk8 : 8 ≤ k
  · obtain h := mono6 64 (by omega) (k - 8)
    rw [show k - 8 + 8 = k from by omega, show k - 8 + 9 = k + 1 from by omega] at h
    have e : 9 ^ 6 ≤ 64 ^ 8 := by decide
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < 64 ^ 8 from Nat.pow_pos (by omega))
    calc (k + 1) ^ 6 * 64 ^ 8 ≤ 9 ^ 6 * 64 ^ k := h
      _ ≤ 64 ^ 8 * 64 ^ k := mmr e _
      _ = 64 ^ k * 64 ^ 8 := by ring
  · interval_cases k <;> decide

/-- The per-prime inequality, in the form used by the induction. -/
lemma prime_step (p : ℕ) (hp : p.Prime) {k : ℕ} (hk : 0 < k) :
    (k + 1) ^ 6 * c p ≤ (u p) ^ 6 * p ^ k := by
  by_cases hT : p ∈ T
  · by_cases hk8 : 8 ≤ k
    · have h1 : (k + 1) ^ 6 * p ^ 8 ≤ 9 ^ 6 * p ^ k := by
        obtain h := mono6 p hp.two_le (k - 8)
        rwa [show k - 8 + 8 = k from by omega, show k - 8 + 9 = k + 1 from by omega] at h
      have hbase : 9 ^ 6 * c p ≤ (u p) ^ 6 * p ^ 8 := by
        simpa using check_T p hT 8 (by omega) (by omega)
      refine Nat.le_of_mul_le_mul_right ?_ (show 0 < p ^ 8 from Nat.pow_pos hp.pos)
      calc (k + 1) ^ 6 * c p * p ^ 8 = ((k + 1) ^ 6 * p ^ 8) * c p := by ring
        _ ≤ (9 ^ 6 * p ^ k) * c p := Nat.mul_le_mul h1 (le_refl _)
        _ = (9 ^ 6 * c p) * p ^ k := by ring
        _ ≤ ((u p) ^ 6 * p ^ 8) * p ^ k := Nat.mul_le_mul hbase (le_refl _)
        _ = (u p) ^ 6 * p ^ k * p ^ 8 := by ring
    · exact check_T p hT k hk (by omega)
  · have h64 : 64 ≤ p := not_mem_T p hp hT
    have hA : A p = 1 := A_of_not_mem_T h64
    have hc : c p = p := by
      rw [c, hA, pow_one]
    have hu : u p = 2 := by
      rw [u, hA]
    have hgen := pow6_le k hk
    have e1 : p ^ k = p ^ (k - 1) * p := by
      have hk1 : k - 1 + 1 = k := by omega
      calc p ^ k = p ^ (k - 1 + 1) := by rw [hk1]
        _ = p ^ (k - 1) * p := pow_succ _ _
    have e2 : 64 ^ k = 64 * 64 ^ (k - 1) := by
      have hk1 : k - 1 + 1 = k := by omega
      calc 64 ^ k = 64 ^ (k - 1 + 1) := by rw [hk1]
        _ = 64 ^ (k - 1) * 64 := pow_succ _ _
        _ = 64 * 64 ^ (k - 1) := by ring
    rw [hc, hu]
    calc (k + 1) ^ 6 * p ≤ 64 ^ k * p := mmr hgen _
      _ = 64 * (64 ^ (k - 1) * p) := by rw [e2]; ring
      _ ≤ 64 * (p ^ (k - 1) * p) := mml (mmr (Nat.pow_le_pow_left h64 (k - 1)) _) _
      _ = 2 ^ 6 * p ^ k := by rw [e1]; ring

/-- Induction core: the credit of the primes below `64` that divide `m` pays for `τ m ^ 6`. -/
theorem key (m : ℕ) (hm : 0 < m) : ∃ S : Finset ℕ,
    S ⊆ T ∧ (∀ q ∈ S, q ∣ m) ∧
    (σ 0 m) ^ 6 * ∏ q ∈ S, c q ≤ (∏ q ∈ S, u q) ^ 6 * m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h1 : m = 1
    · subst h1
      refine ⟨∅, by simp, by simp, ?_⟩
      simp [ArithmeticFunction.sigma_one]
    · obtain ⟨p, hp, hpd⟩ := m.exists_prime_and_dvd h1
      have heq := Nat.pow_padicValNat_mul_divMaxPow p m
      have hex : ∃ k m', p ^ k * m' = m ∧ 0 < k ∧ 0 < m' ∧ ¬ p ∣ m' := by
        refine ⟨padicValNat p m, Nat.divMaxPow m p, heq,
          (Nat.pow_dvd_iff_le_padicValNat (k := 1) hp.ne_one hm.ne').mp (by simpa using hpd), ?_,
          Nat.not_dvd_divMaxPow hp.two_le hm.ne'⟩
        rcases Nat.eq_zero_or_pos (Nat.divMaxPow m p) with h0 | h0
        · rw [h0, mul_zero] at heq
          omega
        · exact h0
      obtain ⟨k, m', hsplit, hkpos, hm'pos, hpnd⟩ := hex
      have hm'lt : m' < m := by
        have hpp : 1 < p ^ k := Nat.one_lt_pow hkpos.ne' hp.one_lt
        have hlt : m' * 1 < m' * p ^ k := Nat.mul_lt_mul_of_pos_left hpp hm'pos
        rw [mul_one, mul_comm (m' : ℕ) (p ^ k), hsplit] at hlt
        exact hlt
      have hdvd : m' ∣ m := ⟨p ^ k, hsplit.symm.trans (mul_comm _ _)⟩
      obtain ⟨S', hS'T, hS', hineq⟩ := ih m' hm'lt hm'pos
      have hc : σ 0 m = (k + 1) * σ 0 m' := by
        rw [← hsplit, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
          ((Nat.coprime_pow_left_iff hkpos p m').mpr (hp.coprime_iff_not_dvd.mpr hpnd)),
          ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      by_cases hT : p ∈ T
      · have hpS : p ∉ S' := fun hmem => hpnd (hS' p hmem)
        refine ⟨insert p S', Finset.insert_subset hT hS'T, ?_, ?_⟩
        · intro q hq
          rcases Finset.mem_insert.mp hq with rfl | h'
          · exact hpd
          · exact (hS' q h').trans hdvd
        · rw [Finset.prod_insert hpS (f := c), Finset.prod_insert hpS (f := u), hc]
          have hmul := Nat.mul_le_mul (prime_step p hp hkpos) hineq
          calc ((k + 1) * σ 0 m') ^ 6 * (c p * ∏ q ∈ S', c q)
              = ((k + 1) ^ 6 * c p) * ((σ 0 m') ^ 6 * ∏ q ∈ S', c q) := by rw [mul_pow]; ring
            _ ≤ ((u p) ^ 6 * p ^ k) * ((∏ q ∈ S', u q) ^ 6 * m') := hmul
            _ = (u p * ∏ q ∈ S', u q) ^ 6 * m := by rw [mul_pow, ← hsplit]; ring
      · refine ⟨S', hS'T, fun q hq => (hS' q hq).trans hdvd, ?_⟩
        have h64 : 64 ≤ p := not_mem_T p hp hT
        have hstep : (k + 1) ^ 6 ≤ p ^ k :=
          (pow6_le k hkpos).trans (Nat.pow_le_pow_left h64 k)
        rw [hc]
        calc ((k + 1) * σ 0 m') ^ 6 * ∏ q ∈ S', c q
              = (k + 1) ^ 6 * ((σ 0 m') ^ 6 * ∏ q ∈ S', c q) := by rw [mul_pow]; ring
          _ ≤ p ^ k * ((∏ q ∈ S', u q) ^ 6 * m') := Nat.mul_le_mul hstep hineq
          _ = (∏ q ∈ S', u q) ^ 6 * m := by rw [← hsplit]; ring

/-- The total allowance over the primes below `64` stays below `139 ^ 6` times the total credit. -/
lemma total : (∏ q ∈ T, u q) ^ 6 ≤ 139 ^ 6 * ∏ q ∈ T, c q := by
  simp only [T, c, u, A, reduceIte]
  decide

/-- The divisor count satisfies `τ m ^ 6 ≤ 139 ^ 6 * m`. -/
theorem final (m : ℕ) : (σ 0 m) ^ 6 ≤ 139 ^ 6 * m := by
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0
    rw [ArithmeticFunction.sigma_eq_zero.mpr rfl]
    simp
  · obtain ⟨S, hST, hS, hineq⟩ := key m hm
    have hcu : ∏ q ∈ T \ S, c q ≤ ∏ q ∈ T \ S, (u q) ^ 6 :=
      Finset.prod_le_prod (fun q hq => Nat.zero_le _) fun q hq => c_le_u q (Finset.mem_sdiff.mp hq).1
    have huu : ∏ q ∈ T \ S, (u q) ^ 6 = (∏ q ∈ T \ S, u q) ^ 6 := Finset.prod_pow _ 6 _
    have h1 : (σ 0 m) ^ 6 * ∏ q ∈ T, c q ≤ (∏ q ∈ T, u q) ^ 6 * m := by
      rw [← Finset.prod_sdiff (f := c) hST, ← Finset.prod_sdiff (f := u) hST]
      calc (σ 0 m) ^ 6 * ((∏ q ∈ T \ S, c q) * ∏ q ∈ S, c q)
          = (∏ q ∈ T \ S, c q) * ((σ 0 m) ^ 6 * ∏ q ∈ S, c q) := by ring
        _ ≤ (∏ q ∈ T \ S, (u q) ^ 6) * ((σ 0 m) ^ 6 * ∏ q ∈ S, c q) := mmr hcu _
        _ = (∏ q ∈ T \ S, u q) ^ 6 * ((σ 0 m) ^ 6 * ∏ q ∈ S, c q) := by rw [huu]
        _ ≤ (∏ q ∈ T \ S, u q) ^ 6 * ((∏ q ∈ S, u q) ^ 6 * m) := mml hineq _
        _ = ((∏ q ∈ T \ S, u q) * ∏ q ∈ S, u q) ^ 6 * m := by rw [mul_pow]; ring
    have h2 : (∏ q ∈ T, u q) ^ 6 * m ≤ (139 ^ 6 * m) * ∏ q ∈ T, c q := by
      have h := mmr total m
      convert h using 1 <;> ring
    have hpos : 0 < ∏ q ∈ T, c q := by
      apply Finset.prod_pos
      intro q hq
      unfold c
      exact Nat.pow_pos ((mem_T q hq).1).pos
    exact Nat.le_of_mul_le_mul_right (h1.trans h2) hpos

end OMA647

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R1.H1 := OMA647.final
