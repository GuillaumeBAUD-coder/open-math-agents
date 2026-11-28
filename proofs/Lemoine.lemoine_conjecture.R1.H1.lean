import OMAReductions.R_Lemoine_lemoine_conjecture_R1

/-!
Proof of `Lemoine.lemoine_conjecture.R1.H1`:
every odd `n` with `6 < n <= 10001` can be written as `p + 2 * q` with `p` and `q` prime.
Verified in the Lean kernel using trial division by the 25 primes `<= 97` (sufficient up to
`101 ^ 2 = 10201 > 10001`).
-/

namespace LemoineR1H1

private def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

private def isPrimeB (n : ℕ) : Bool :=
  decide (2 ≤ n) && smallPrimes.all (fun p => decide (n ≤ p) || decide (n % p ≠ 0))

private lemma smallPrimes_complete : ∀ q ≤ 100, q.Prime → q ∈ smallPrimes := by decide

private lemma isPrimeB_sound {n : ℕ} (hn : n ≤ 10001) (h : isPrimeB n = true) : n.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨hn2, hall⟩ := h
  by_contra hnot
  set q := n.minFac
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqsq : q * q ≤ n := by simpa [q, sq] using Nat.minFac_sq_le_self (by omega) hnot
  have hq100 : q ≤ 100 := by nlinarith
  have hqmem : q ∈ smallPrimes := smallPrimes_complete q hq100 hq
  have hqlt : q < n := by
    have hqle : q ≤ n := Nat.le_of_dvd (by omega) (Nat.minFac_dvd n)
    exact lt_of_le_of_ne hqle (fun heq => hnot (heq ▸ hq))
  have hdiv : n % q = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n)
  rcases hall q hqmem with hle | hne
  · omega
  · exact hne hdiv

private def findWitness (n q : ℕ) : Bool :=
  if 2 * q < n then
    (isPrimeB q && isPrimeB (n - 2 * q)) || findWitness n (q + 1)
  else false
termination_by n - 2 * q

private lemma findWitness_sound {n q : ℕ} (hn : n ≤ 10001) (h : findWitness n q = true) :
    ∃ p q' : ℕ, p.Prime ∧ q'.Prime ∧ p + 2 * q' = n := by
  induction hfuel : n - 2 * q using Nat.strong_induction_on generalizing q with
  | h m ih =>
    unfold findWitness at h
    split_ifs at h with hlt
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨hq, hp⟩ | hnext
    · exact ⟨n - 2 * q, q, isPrimeB_sound (by omega) hp, isPrimeB_sound (by omega) hq, by omega⟩
    · exact ih (n - 2 * (q + 1)) (by omega) hnext rfl

private def checkOddRange (start : ℕ) : ℕ → Bool
  | 0 => true
  | cnt + 1 => findWitness start 2 && checkOddRange (start + 2) cnt

private lemma checkOddRange_sound {start cnt : ℕ} (hhi : start + 2 * cnt ≤ 10003)
    (hodd : start % 2 = 1) (h : checkOddRange start cnt = true) :
    ∀ n : ℕ, start ≤ n → n < start + 2 * cnt → n % 2 = 1 →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + 2 * q = n := by
  induction cnt generalizing start with
  | zero => intro n h1 h2; omega
  | succ c ih =>
    simp only [checkOddRange, Bool.and_eq_true] at h
    intro n h1 h2 hn_odd
    by_cases heq : n = start
    · subst heq
      exact findWitness_sound (by omega) h.1
    · exact ih (by omega) (by omega) h.2 n (by omega) (by omega) hn_odd

set_option maxHeartbeats 8000000 in
private lemma chk_0 : checkOddRange 7 1000 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private lemma chk_1 : checkOddRange 2007 1000 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private lemma chk_2 : checkOddRange 4007 1000 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private lemma chk_3 : checkOddRange 6007 1000 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
private lemma chk_4 : checkOddRange 8007 998 = true := by decide +kernel

theorem main_proof : OMA.R_Lemoine_lemoine_conjecture_R1.H1 := by
  intro n hn hodd hle
  have hn_odd : n % 2 = 1 := by
    obtain ⟨k, rfl⟩ := hodd
    omega
  by_cases h0 : n < 2007
  · exact checkOddRange_sound (by decide) (by decide) chk_0 n (by omega) h0 hn_odd
  by_cases h1 : n < 4007
  · exact checkOddRange_sound (by decide) (by decide) chk_1 n (by omega) h1 hn_odd
  by_cases h2 : n < 6007
  · exact checkOddRange_sound (by decide) (by decide) chk_2 n (by omega) h2 hn_odd
  by_cases h3 : n < 8007
  · exact checkOddRange_sound (by decide) (by decide) chk_3 n (by omega) h3 hn_odd
  exact checkOddRange_sound (by decide) (by decide) chk_4 n (by omega) (by omega) hn_odd

end LemoineR1H1

theorem OMA.solution : OMA.R_Lemoine_lemoine_conjecture_R1.H1 :=
  LemoineR1H1.main_proof
