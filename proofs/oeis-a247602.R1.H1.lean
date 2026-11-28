import OMAReductions.R_oeis_a247602_R1

/-! The witnesses for 10 and 11 require prime counts at 80410 and 174570.
We count in blocks, testing only prime divisors up to the square root. -/


private def smallPrimes : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,
   73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,
   157,163,167,173,179,181,191,193,197,199,211,223,227,229,
   233,239,241,251,257,263,269,271,277,281,283,293,307,311,
   313,317,331,337,347,349,353,359,367,373,379,383,389,397,
   401,409]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem covers : ∀ p : Fin 418, p.val.Prime → p.val ∈ smallPrimes := by
  decide +kernel

private abbrev trial (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ p ∈ smallPrimes, n < p * p ∨ ¬ p ∣ n

private theorem trial_iff {n : ℕ} (hn : n ≤ 174570) : trial n ↔ n.Prime := by
  constructor
  · rintro ⟨h2, test⟩
    by_contra hc
    have prime := Nat.minFac_prime (by omega : n ≠ 1)
    have sqle : n.minFac * n.minFac ≤ n := by
      simpa only [pow_two] using Nat.minFac_sq_le_self (by omega : 0 < n) hc
    have small : n.minFac < 418 := by
      by_contra! h
      have hmul := Nat.mul_le_mul h h
      omega
    rcases test n.minFac (covers ⟨n.minFac, small⟩ prime) with h | h
    · omega
    · exact h (Nat.minFac_dvd n)
  · intro hn'
    refine ⟨hn'.two_le, ?_⟩
    intro p hp
    by_cases hd : p ∣ n
    · have hall : ∀ d ∈ smallPrimes, Nat.Prime d := by decide +kernel
      have eq : p = n := (Nat.prime_dvd_prime_iff_eq (hall p hp) hn').mp hd
      subst p
      left
      have lo := hn'.two_le
      have hh := Nat.mul_le_mul_right n lo
      nlinarith
    · exact Or.inr hd

private def block (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | length + 1 => block start length + if trial (start + length) then 1 else 0

private theorem count_block (s l : ℕ) (hb : s + l ≤ 174571) :
    Nat.count Nat.Prime (s + l) = Nat.count Nat.Prime s + block s l := by
  induction l with
  | zero => simp [block]
  | succ k ih =>
    have H : trial (s+k) ↔ (s+k).Prime := trial_iff (by omega)
    rw [Nat.add_succ, Nat.count_succ, ih (by omega)]
    simp only [block, H, Nat.add_assoc]

private def blocks (w : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => blocks w k + block (k*w) w

private theorem count_blocks (w k : ℕ) (hb : k*w ≤ 174571) :
    Nat.count Nat.Prime (k*w) = blocks w k := by
  induction k with
  | zero => simp [blocks]
  | succ k ih =>
    rw [Nat.succ_mul] at hb ⊢
    simp only [count_block _ _ hb, ih (by omega), blocks]

private theorem pi_split (k r : ℕ) (hb : k * 512 + r ≤ 174571) :
    Nat.count Nat.Prime (k * 512 + r) =
      blocks 512 k + block (k * 512) r := by
  rw [count_block _ _ hb, count_blocks _ _ (by omega)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem pi10 : Nat.primeCounting 80410 = 7872 := by
  change Nat.count Nat.Prime (157 * 512 + 27) = 7872
  rw [pi_split 157 27 (by decide)] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem pi11 : Nat.primeCounting 174570 = 15880 := by
  change Nat.count Nat.Prime (340 * 512 + 491) = 15880
  rw [pi_split 340 491 (by decide)] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem OMA.solution : OMA.R_oeis_a247602_R1.H1 := by
  intro n hn hN
  interval_cases n
  · exact ⟨3, by decide, by decide +kernel⟩
  · exact ⟨2, by decide, by decide +kernel⟩
  · exact ⟨1, by decide, by decide +kernel⟩
  · exact ⟨91, by decide, by decide +kernel⟩
  · exact ⟨6, by decide, by decide +kernel⟩
  · exact ⟨5, by decide, by decide +kernel⟩
  · exact ⟨1, by decide, by decide +kernel⟩
  · exact ⟨5, by decide, by decide +kernel⟩
  · exact ⟨1, by decide, by decide +kernel⟩
  · refine ⟨8041, by decide, ?_⟩
    change Nat.primeCounting 80410 = Nat.totient (83 * 97)
    rw [pi10, Nat.totient_mul (by decide : Nat.Coprime 83 97),
      Nat.totient_prime (by norm_num : Nat.Prime 83), Nat.totient_prime (by norm_num : Nat.Prime 97)]
  · refine ⟨15870, by decide, ?_⟩
    change Nat.primeCounting 174570 = Nat.totient 15881
    rw [pi11, Nat.totient_prime (by norm_num : Nat.Prime 15881)]

