import OMAReductions.R_Oppermann_oppermann_conjecture_parts_ii_R1

/-!
# Proof of `Oppermann.oppermann_conjecture.parts.ii.R1.H1`

Verifies via a kernel-checked trial-division prime search (`decide +kernel`) that for every
`2 ≤ x ≤ 1000`, there exists a prime `p` with `x ^ 2 < p < x * (x + 1)`.
-/

namespace OppermannPartsIIR1H1Proof

private def noOddDiv (n d fuel : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
    if d * d > n then true
    else if n % d == 0 then false
    else noOddDiv n (d + 2) f

private lemma noOddDiv_sound (n : ℕ) : ∀ fuel d : ℕ, 3 ≤ d → d % 2 = 1 →
    noOddDiv n d fuel = true →
    ∀ k : ℕ, d ≤ k → k % 2 = 1 → k * k ≤ n → ¬ (k ∣ n) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; simp [noOddDiv] at h
  | succ f ih =>
    intro d hd hodd hok k hk hkodd hksq hdvd
    unfold noOddDiv at hok
    by_cases hgt : d * d > n
    · have : d * d ≤ k * k := Nat.mul_le_mul hk hk
      omega
    · rw [if_neg hgt] at hok
      by_cases hmod : n % d = 0
      · simp [hmod] at hok
      · have hmodb : (n % d == 0) = false := by simp [hmod]
        rw [hmodb] at hok
        simp only [Bool.false_eq_true, ↓reduceIte] at hok
        rcases eq_or_lt_of_le hk with rfl | hlt
        · exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
        · exact ih (d + 2) (by omega) (by omega) hok k (by omega) hkodd hksq hdvd

private def isPrimeBool (n : ℕ) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else if n % 2 == 0 then false
  else noOddDiv n 3 505

private lemma isPrimeBool_sound {n : ℕ} (h : isPrimeBool n = true) : n.Prime := by
  unfold isPrimeBool at h
  by_cases hlt2 : n < 2
  · simp [hlt2] at h
  rw [if_neg hlt2] at h
  by_cases hn2 : n = 2
  · subst hn2; exact Nat.prime_two
  have hn2b : (n == 2) = false := by simp [hn2]
  rw [hn2b] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases hev : n % 2 = 0
  · simp [hev] at h
  have hevb : (n % 2 == 0) = false := by simp [hev]
  rw [hevb] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
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
  exact noOddDiv_sound n 505 3 (by decide) (by decide) h n.minFac hd_ge3 hd_odd hd_sq hd_dvd

private def findPrime (cur hi fuel : ℕ) : Option ℕ :=
  match fuel with
  | 0 => none
  | f + 1 =>
    if cur ≥ hi then none
    else if isPrimeBool cur then some cur
    else findPrime (cur + 1) hi f

private lemma findPrime_sound : ∀ fuel cur hi p : ℕ,
    findPrime cur hi fuel = some p → cur ≤ p ∧ p < hi ∧ p.Prime := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; simp [findPrime] at h
  | succ f ih =>
    intro cur hi p h
    unfold findPrime at h
    by_cases hge : cur ≥ hi
    · simp [hge] at h
    rw [if_neg hge] at h
    by_cases hp : isPrimeBool cur = true
    · rw [if_pos hp] at h
      cases h
      exact ⟨le_rfl, by omega, isPrimeBool_sound hp⟩
    · rw [if_neg hp] at h
      obtain ⟨h1, h2, h3⟩ := ih (cur + 1) hi p h
      exact ⟨by omega, h2, h3⟩

private def checkOne (x : ℕ) : Bool :=
  if x > 1000 then true else (findPrime (x * x + 1) (x * (x + 1)) 300).isSome

private def checkTree (lo : ℕ) : ℕ → Bool
  | 0 => checkOne lo
  | d + 1 => checkTree lo d && checkTree (lo + 2 ^ d) d

private lemma checkTree_sound : ∀ d lo : ℕ, checkTree lo d = true →
    ∀ x : ℕ, lo ≤ x → x < lo + 2 ^ d → checkOne x = true := by
  intro d
  induction d with
  | zero =>
    intro lo h x h1 h2
    have : x = lo := by omega
    subst this; exact h
  | succ d ih =>
    intro lo h x h1 h2
    unfold checkTree at h
    rw [Bool.and_eq_true] at h
    by_cases hlt : x < lo + 2 ^ d
    · exact ih lo h.1 x h1 hlt
    · exact ih (lo + 2 ^ d) h.2 x (by omega) (by rw [pow_succ] at h2; omega)

private lemma checkTree_all : checkTree 2 10 = true := by decide +kernel

end OppermannPartsIIR1H1Proof

theorem OMA.solution : OMA.R_Oppermann_oppermann_conjecture_parts_ii_R1.H1 := by
  intro x h1 h2
  have hok := OppermannPartsIIR1H1Proof.checkTree_sound 10 2 OppermannPartsIIR1H1Proof.checkTree_all x h1 (by omega)
  unfold OppermannPartsIIR1H1Proof.checkOne at hok
  rw [if_neg (by omega)] at hok
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hok
  obtain ⟨hlo, hhi, hpr⟩ := OppermannPartsIIR1H1Proof.findPrime_sound 300 (x * x + 1) (x * (x + 1)) p hp
  refine ⟨p, Finset.mem_Ioo.mpr ⟨?_, ?_⟩, hpr⟩
  · rw [sq]; omega
  · omega
