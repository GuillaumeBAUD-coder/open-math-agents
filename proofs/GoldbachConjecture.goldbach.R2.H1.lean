import OMAReductions.R_GoldbachConjecture_goldbach_R2

/-!
# Proof of `GoldbachConjecture.goldbach.R2.H1`

Verifies Goldbach's conjecture for every even integer `n` with `2 < n ≤ 50000`.

For any `m ≤ 50000`, `m` is prime if `2 ≤ m` and `m` has no proper divisor among the 48 primes
`≤ 223` (since `227 ^ 2 = 51529 > 50000`). A binary-tree checker `checkPow2` searches the 47
primes `p ≤ 211` for each even `n = 2 * k` (`2 ≤ k ≤ 25000`) and verifies by kernel reduction
(`decide +kernel`) that `n - p` passes the fast primality test.
-/

namespace GoldbachR2H1Proof

private def trialPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
   193, 197, 199, 211, 223]

private def witnessPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
   193, 197, 199, 211]

private def isPrimeFast (m : ℕ) : Bool :=
  2 ≤ m && trialPrimes.all (fun d => m == d || m % d != 0)

private lemma mem_trialPrimes_of_prime_le_224 {d : ℕ} (hd : d.Prime) (hle : d ≤ 224) :
    d ∈ trialPrimes := by
  have hall : ∀ n : Fin 225, n.val.Prime → n.val ∈ trialPrimes := by decide +kernel
  exact hall ⟨d, by omega⟩ hd

private lemma prime_of_isPrimeFast {m : ℕ} (hm : m ≤ 50000) (h : isPrimeFast m = true) :
    m.Prime := by
  unfold isPrimeFast at h
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hm2, hdiv⟩ := h
  by_contra hnp
  set d := m.minFac
  have hd_prime : d.Prime := Nat.minFac_prime (by omega)
  have hd_dvd : d ∣ m := Nat.minFac_dvd m
  have hd_ne : d ≠ m := fun heq => hnp (heq ▸ hd_prime)
  have hd_sq : d ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hnp
  have hd_le : d ≤ 224 := by nlinarith
  have hd_mem : d ∈ trialPrimes := mem_trialPrimes_of_prime_le_224 hd_prime hd_le
  have hcheck := hdiv d hd_mem
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at hcheck
  rcases hcheck with heq | hmod
  · exact hd_ne heq.symm
  · exact hmod (Nat.mod_eq_zero_of_dvd hd_dvd)

private lemma witnessPrimes_all_prime : ∀ p ∈ witnessPrimes, p.Prime := by
  decide +kernel

private def hasGoldbach (n : ℕ) : Bool :=
  witnessPrimes.any (fun p => p < n && isPrimeFast (n - p))

private def checkPow2 (lo : ℕ) : ℕ → Bool
  | 0 => hasGoldbach (2 * lo)
  | d + 1 => checkPow2 lo d && checkPow2 (lo + 2 ^ d) d

private lemma checkPow2_sound :
    ∀ (d lo : ℕ), checkPow2 lo d = true →
      ∀ k, lo ≤ k → k < lo + 2 ^ d → hasGoldbach (2 * k) = true := by
  intro d
  induction d with
  | zero =>
    intro lo h k h1 h2
    have hk : k = lo := by simp at h2; omega
    subst hk; exact h
  | succ d ih =>
    intro lo h k h1 h2
    simp only [checkPow2, Bool.and_eq_true] at h
    by_cases hlt : k < lo + 2 ^ d
    · exact ih lo h.1 k h1 hlt
    · exact ih (lo + 2 ^ d) h.2 k (by omega) (by rw [pow_succ] at h2; omega)

private lemma check_0 : checkPow2 2 12 = true := by decide +kernel
private lemma check_1 : checkPow2 4098 12 = true := by decide +kernel
private lemma check_2 : checkPow2 8194 12 = true := by decide +kernel
private lemma check_3 : checkPow2 12290 12 = true := by decide +kernel
private lemma check_4 : checkPow2 16386 12 = true := by decide +kernel
private lemma check_5 : checkPow2 20482 12 = true := by decide +kernel
private lemma check_6 : checkPow2 24578 9 = true := by decide +kernel

private lemma hasGoldbach_all_even {k : ℕ} (hk2 : 2 ≤ k) (hk25000 : k ≤ 25000) :
    hasGoldbach (2 * k) = true := by
  by_cases h0 : k < 4098
  · exact checkPow2_sound 12 2 check_0 k hk2 (by norm_num; omega)
  · by_cases h1 : k < 8194
    · exact checkPow2_sound 12 4098 check_1 k (by omega) (by norm_num; omega)
    · by_cases h2 : k < 12290
      · exact checkPow2_sound 12 8194 check_2 k (by omega) (by norm_num; omega)
      · by_cases h3 : k < 16386
        · exact checkPow2_sound 12 12290 check_3 k (by omega) (by norm_num; omega)
        · by_cases h4 : k < 20482
          · exact checkPow2_sound 12 16386 check_4 k (by omega) (by norm_num; omega)
          · by_cases h5 : k < 24578
            · exact checkPow2_sound 12 20482 check_5 k (by omega) (by norm_num; omega)
            · exact checkPow2_sound 9 24578 check_6 k (by omega) (by norm_num; omega)

end GoldbachR2H1Proof

theorem OMA.solution : OMA.R_GoldbachConjecture_goldbach_R2.H1 := by
  intro n hn2 heven hn50000
  obtain ⟨k, rfl⟩ := heven
  have h2k : k + k = 2 * k := by ring
  rw [h2k] at hn2 hn50000 ⊢
  have hcheck := GoldbachR2H1Proof.hasGoldbach_all_even (by omega : 2 ≤ k) (by omega : k ≤ 25000)
  unfold GoldbachR2H1Proof.hasGoldbach at hcheck
  rw [List.any_eq_true] at hcheck
  obtain ⟨p, hp_mem, hp_cond⟩ := hcheck
  rw [Bool.and_eq_true, decide_eq_true_eq] at hp_cond
  refine ⟨p, 2 * k - p,
    Nat.prime_iff.mp (GoldbachR2H1Proof.witnessPrimes_all_prime p hp_mem),
    Nat.prime_iff.mp (GoldbachR2H1Proof.prime_of_isPrimeFast (by omega) hp_cond.2),
    by omega⟩
