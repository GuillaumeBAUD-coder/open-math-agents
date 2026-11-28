import OMAReductions.R_OeisA182126_conjecture2_R1

/-!
# Proof of `OeisA182126.conjecture2.R1.H1`

Verifies via a kernel-checked sweep over `[4, 10000]` (`decide +kernel`) that for every `k > 60`
with `Nat.nth Nat.Prime (k + 2) ≤ 10000`,
`(p_{k+2} - p_k) * (p_{k+2} - p_{k+1}) < p_{k+2}`.

We verify `Nat.count Nat.Prime 307 = 62`, whence `307 < Nat.nth Nat.Prime (k + 2)` for all
`k > 60`, and sweep `m = 4..10000` tracking the two largest primes seen so far to confirm that
every three consecutive primes `p < q < r` with `307 < r ≤ 10000` satisfy `(r - p) * (r - q) < r`.
-/

namespace OeisA182126Conjecture2R1H1Proof

private def noOddDiv (n d : ℕ) : ℕ → Bool
  | 0 => decide (d * d > n)
  | f + 1 =>
    if d * d > n then true
    else if n % d == 0 then false
    else noOddDiv n (d + 2) f

private lemma noOddDiv_iff (n : ℕ) : ∀ fuel d : ℕ, 3 ≤ d → d % 2 = 1 →
    n < (d + 2 * fuel) * (d + 2 * fuel) →
    (noOddDiv n d fuel = true ↔ ∀ k : ℕ, d ≤ k → k % 2 = 1 → k * k ≤ n → ¬ (k ∣ n)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro d hd hodd hgt
    unfold noOddDiv
    simp only [mul_zero, add_zero] at hgt
    simp only [decide_eq_true_eq]
    constructor
    · intro h k hk _ hksq _
      have : d * d ≤ k * k := Nat.mul_le_mul hk hk
      omega
    · intro _
      omega
  | succ f ih =>
    intro d hd hodd hgt
    unfold noOddDiv
    by_cases hsq : d * d > n
    · rw [if_pos hsq]
      simp only [true_iff]
      intro k hk _ hksq _
      have : d * d ≤ k * k := Nat.mul_le_mul hk hk
      omega
    · rw [if_neg hsq]
      by_cases hmod : n % d = 0
      · have hmodb : (n % d == 0) = true := by simp [hmod]
        rw [hmodb]
        simp only [↓reduceIte, Bool.false_eq_true, false_iff, not_forall, Classical.not_not]
        exact ⟨d, le_rfl, hodd, by omega, Nat.dvd_of_mod_eq_zero hmod⟩
      · have hmodb : (n % d == 0) = false := by simp [hmod]
        rw [hmodb]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hgt' : n < (d + 2 + 2 * f) * (d + 2 + 2 * f) := by
          have : d + 2 + 2 * f = d + 2 * (f + 1) := by omega
          rwa [this]
        rw [ih (d + 2) (by omega) (by omega) hgt']
        constructor
        · intro h k hk hkodd hksq hdvd
          rcases eq_or_lt_of_le hk with rfl | hlt
          · exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
          · exact h k (by omega) hkodd hksq hdvd
        · intro h k hk hkodd hksq hdvd
          exact h k (by omega) hkodd hksq hdvd

private def isPrimeBool (n : ℕ) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else if n % 2 == 0 then false
  else noOddDiv n 3 55

private lemma isPrimeBool_iff {n : ℕ} (hle : n ≤ 10000) :
    isPrimeBool n = true ↔ n.Prime := by
  unfold isPrimeBool
  by_cases hlt2 : n < 2
  · rw [if_pos hlt2]
    simp only [Bool.false_eq_true, false_iff]
    intro hp; have := hp.two_le; omega
  rw [if_neg hlt2]
  by_cases hn2 : n = 2
  · subst hn2; simp [Nat.prime_two]
  have hn2b : (n == 2) = false := by simp [hn2]
  rw [hn2b]; simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hev : n % 2 = 0
  · have hevb : (n % 2 == 0) = true := by simp [hev]
    rw [hevb]; simp only [↓reduceIte, Bool.false_eq_true, false_iff]
    intro hp
    have h2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero hev
    rcases (Nat.dvd_prime hp).mp h2 with h | h <;> omega
  have hevb : (n % 2 == 0) = false := by simp [hev]
  rw [hevb]; simp only [Bool.false_eq_true, ↓reduceIte]
  rw [noOddDiv_iff n 55 3 (by decide) (by decide) (by omega)]
  constructor
  · intro hno
    rw [Nat.prime_def_minFac]
    refine ⟨by omega, ?_⟩
    by_contra hne
    have hd_prime : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hd_dvd : n.minFac ∣ n := Nat.minFac_dvd n
    have hd_sq : n.minFac * n.minFac ≤ n := by
      have := Nat.minFac_sq_le_self (by omega) (fun hp => hne hp.minFac_eq)
      rwa [sq] at this
    have hd_odd : n.minFac % 2 = 1 := by
      by_contra h2
      have h2d : 2 ∣ n.minFac := Nat.dvd_of_mod_eq_zero (by omega)
      have h2n : 2 ∣ n := dvd_trans h2d hd_dvd
      have := Nat.mod_eq_zero_of_dvd h2n
      omega
    have hd_ge3 : 3 ≤ n.minFac := by have := hd_prime.two_le; omega
    exact hno n.minFac hd_ge3 hd_odd hd_sq hd_dvd
  · intro hp k hk _ hksq hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with rfl | rfl
    · omega
    · nlinarith

private def checkSweep (m prev2 prev1 : ℕ) : ℕ → Bool
  | 0 => true
  | steps + 1 =>
    if isPrimeBool m then
      (if 307 < m then decide ((m - prev2) * (m - prev1) < m) else true) &&
      checkSweep (m + 1) prev1 m steps
    else
      checkSweep (m + 1) prev2 prev1 steps

private def IsLastTwoPrimes (m prev2 prev1 : ℕ) : Prop :=
  prev2 < prev1 ∧ prev1 < m ∧ prev2.Prime ∧ prev1.Prime ∧
  (∀ x : ℕ, prev2 < x → x < prev1 → ¬ x.Prime) ∧
  (∀ x : ℕ, prev1 < x → x < m → ¬ x.Prime)

private lemma checkSweep_sound : ∀ steps m prev2 prev1 : ℕ,
    m + steps ≤ 10001 →
    IsLastTwoPrimes m prev2 prev1 →
    checkSweep m prev2 prev1 steps = true →
    ∀ p q r : ℕ, m ≤ r → r < m + steps → 307 < r →
      p < q → q < r → p.Prime → q.Prime → r.Prime →
      (∀ x : ℕ, p < x → x < q → ¬ x.Prime) →
      (∀ x : ℕ, q < x → x < r → ¬ x.Prime) →
      (r - p) * (r - q) < r := by
  intro steps
  induction steps with
  | zero =>
    intro m _ _ _ _ _ _ _ _ hr1 hr2
    omega
  | succ s ih =>
    intro m prev2 prev1 hbound hinv hok p q r hr1 hr2 hr307 hpq hqr hp hq hr hno1 hno2
    unfold checkSweep at hok
    have hm_le : m ≤ 10000 := by omega
    by_cases hm_pr : isPrimeBool m = true
    · rw [if_pos hm_pr, Bool.and_eq_true] at hok
      have hm_prime : m.Prime := (isPrimeBool_iff hm_le).mp hm_pr
      rcases eq_or_lt_of_le hr1 with rfl | hlt
      · -- r = m: must have q = prev1 and p = prev2
        have hq_eq : q = prev1 := by
          rcases lt_trichotomy q prev1 with h1 | h1 | h1
          · exact absurd hinv.2.2.2.1 (hno2 prev1 h1 hinv.2.1)
          · exact h1
          · exact absurd hq (hinv.2.2.2.2.2 q h1 hqr)
        have hp_eq : p = prev2 := by
          subst hq_eq
          rcases lt_trichotomy p prev2 with h1 | h1 | h1
          · exact absurd hinv.2.2.1 (hno1 prev2 h1 hinv.1)
          · exact h1
          · exact absurd hp (hinv.2.2.2.2.1 p h1 hpq)
        subst hq_eq hp_eq
        have h1 := hok.1
        rw [if_pos hr307, decide_eq_true_eq] at h1
        exact h1
      · have hinv' : IsLastTwoPrimes (m + 1) prev1 m := by
          refine ⟨hinv.2.1, Nat.lt_succ_self m, hinv.2.2.2.1, hm_prime, hinv.2.2.2.2.2, ?_⟩
          intro x hx1 hx2; omega
        exact ih (m + 1) prev1 m (by omega) hinv' hok.2 p q r (by omega) (by omega) hr307
          hpq hqr hp hq hr hno1 hno2
    · rw [if_neg hm_pr] at hok
      have hm_not : ¬ m.Prime := fun h => hm_pr ((isPrimeBool_iff hm_le).mpr h)
      have hrm : m < r := by
        rcases eq_or_lt_of_le hr1 with rfl | hlt
        · exact absurd hr hm_not
        · exact hlt
      have hinv' : IsLastTwoPrimes (m + 1) prev2 prev1 := by
        refine ⟨hinv.1, Nat.lt_succ_of_lt hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, ?_⟩
        intro x hx1 hx2
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hx2) with rfl | hlt
        · exact hm_not
        · exact hinv.2.2.2.2.2 x hx1 hlt
      exact ih (m + 1) prev2 prev1 (by omega) hinv' hok p q r (by omega) (by omega) hr307
        hpq hqr hp hq hr hno1 hno2

private lemma checkSweep_all : checkSweep 4 2 3 9997 = true := by decide +kernel

private def countPrimesUpTo (n : ℕ) : ℕ :=
  ((List.range n).filter isPrimeBool).length

private lemma countPrimesUpTo_307 : countPrimesUpTo 307 = 62 := by decide +kernel

private lemma nat_count_prime_307 : Nat.count Nat.Prime 307 = 62 := by
  rw [Nat.count_eq_card_filter_range]
  have hset1 : (Finset.range 307).filter Nat.Prime =
      (Finset.range 307).filter (fun n => isPrimeBool n = true) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hx, hp⟩; exact ⟨hx, (isPrimeBool_iff (by omega)).mpr hp⟩
    · rintro ⟨hx, hb⟩; exact ⟨hx, (isPrimeBool_iff (by omega)).mp hb⟩
  rw [hset1]
  have hset2 : (Finset.range 307).filter (fun n => isPrimeBool n = true) =
      ((List.range 307).filter isPrimeBool).toFinset := by
    ext x
    simp
  rw [hset2, List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  exact countPrimesUpTo_307

end OeisA182126Conjecture2R1H1Proof

theorem OMA.solution : OMA.R_OeisA182126_conjecture2_R1.H1 := by
  intro k hk hle
  set p := Nat.nth Nat.Prime k
  set q := Nat.nth Nat.Prime (k + 1)
  set r := Nat.nth Nat.Prime (k + 2)
  have hinf : {n : ℕ | n.Prime}.Infinite := Nat.infinite_setOfPred_prime
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono hinf
  have hp : p.Prime := Nat.nth_mem_of_infinite hinf k
  have hq : q.Prime := Nat.nth_mem_of_infinite hinf (k + 1)
  have hr : r.Prime := Nat.nth_mem_of_infinite hinf (k + 2)
  have hpq : p < q := hmono (by omega)
  have hqr : q < r := hmono (by omega)
  have hr307 : 307 < r := by
    by_contra hnot
    have hle307 : r ≤ 307 := by omega
    have hcount_r : Nat.count Nat.Prime r = k + 2 := Nat.count_nth_of_infinite hinf (k + 2)
    have hmono_c : Nat.count Nat.Prime r ≤ Nat.count Nat.Prime 307 := Nat.count_monotone _ hle307
    rw [hcount_r, OeisA182126Conjecture2R1H1Proof.nat_count_prime_307] at hmono_c
    omega
  have hno_between : ∀ j x : ℕ, Nat.nth Nat.Prime j < x → x < Nat.nth Nat.Prime (j + 1) → ¬ x.Prime := by
    intro j x h1 h2 hx
    have hc1 : Nat.count Nat.Prime (Nat.nth Nat.Prime j) = j := Nat.count_nth_of_infinite hinf j
    have hc2 : Nat.count Nat.Prime (Nat.nth Nat.Prime (j + 1)) = j + 1 :=
      Nat.count_nth_of_infinite hinf (j + 1)
    have hlt1 : j < Nat.count Nat.Prime x := by
      have hsucc : Nat.nth Nat.Prime j + 1 ≤ x := by omega
      have hlt_c : Nat.count Nat.Prime (Nat.nth Nat.Prime j) <
          Nat.count Nat.Prime (Nat.nth Nat.Prime j + 1) := by
        rw [Nat.count_succ, if_pos (Nat.nth_mem_of_infinite hinf j)]
        omega
      have hle_c := Nat.count_monotone Nat.Prime hsucc
      omega
    have hlt2 : Nat.count Nat.Prime x < j + 1 := by
      have hsucc : x + 1 ≤ Nat.nth Nat.Prime (j + 1) := by omega
      have hlt_c : Nat.count Nat.Prime x < Nat.count Nat.Prime (x + 1) := by
        rw [Nat.count_succ, if_pos hx]
        omega
      have hle_c := Nat.count_monotone Nat.Prime hsucc
      omega
    omega
  have hinv4 : OeisA182126Conjecture2R1H1Proof.IsLastTwoPrimes 4 2 3 := by
    refine ⟨by decide, by decide, Nat.prime_two, Nat.prime_three, ?_, ?_⟩
    · intro x h1 h2; omega
    · intro x h1 h2; omega
  exact OeisA182126Conjecture2R1H1Proof.checkSweep_sound 9997 4 2 3 (by decide) hinv4
    OeisA182126Conjecture2R1H1Proof.checkSweep_all p q r (by omega) (by omega) hr307
    hpq hqr hp hq hr (hno_between k) (hno_between (k + 1))
