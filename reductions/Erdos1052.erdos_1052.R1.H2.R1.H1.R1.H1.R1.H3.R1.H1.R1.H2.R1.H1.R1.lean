import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H1.R1.H2.R1.H1.R1 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H1.R1.H2.R1.H1
-- Credit: @ryansolves

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H2_R1_H1_R1

/-- A finite set of primes closed under the prime factors above three of p+1.
The last hypothesis prevents one factor from being consumed by two different primes.
When 5 is missing, a disjoint-chain certificate bounds the product of (p+1)/p. -/
def H1 : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ 7 ≤ p) →
    (∀ c : ℕ, c.Prime → 5 ≤ c → ∀ p ∈ P, c ∣ p+1 → c ∈ P) →
    (∀ c : ℕ, c.Prime → 5 ≤ c → ∀ p ∈ P, ∀ q ∈ P, c ∣ p+1 → c ∣ q+1 → p=q) →
    100 * (∏ p ∈ P, (p+1)) ≤ 187 * (∏ p ∈ P, p)

/-- The remaining prime-support case. -/
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 764 →
    padicValNat 2 n % 2 = 1 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    5 ∣ n → 7 ∣ n → 41 ∣ n → ¬ 13 ∣ n →
    (∃ q : ℕ, q.Prime ∧ q ∣ n ∧ 5 ∣ q+1 ∧ ¬ 25 ∣ q+1) →
    padicValNat 2 n ≤ A

lemma two_odd_excludes_five {m : ℕ} (hm : m % 2 = 1) : ¬ 5 ∣ 2^m+1 := by
  have hx : 2^(4*(m/4)) ≡ 1 [MOD 5] := by
    rw [pow_mul]
    simpa using (show 2^4 ≡ 1 [MOD 5] by decide).pow (m/4)
  have hy : 2^m+1 ≡ 2^(m%4)+1 [MOD 5] := by
    have z := (hx.mul_left (2^(m%4))).add_right 1
    simpa [← pow_add, Nat.mod_add_div] using z
  intro hd
  have hzero := Nat.mod_eq_zero_of_dvd hd
  change (2^m+1)%5=(2^(m%4)+1)%5 at hy
  rcases (show m%4=1 ∨ m%4=3 by omega) with h | h <;> rw [h] at hy <;> norm_num at hy <;> omega

lemma deficit_contradiction {a b T D : ℕ} (ha : 32 ≤ a) (hb : 27 ≤ b)
    (hd : 0 < D) (ht : 100*T ≤ 187*D)
    (equation : (a+1)*(b+1)*T = 2*a*b*D) : False := by
  have small : 187*((a+1)*(b+1)) < 200*a*b := by
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hb
    nlinarith [Nat.zero_le (x*y)]
  have left := Nat.mul_le_mul_left ((a+1)*(b+1)) ht
  have right := Nat.mul_lt_mul_of_pos_right small hd
  nlinarith only [left, right, congrArg (fun k : ℕ => 100*k) equation]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1500000 in
theorem main :  H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H2_R1.H1 := by
  intro hchains hrestricted
  obtain ⟨A, hA⟩ := hrestricted
  refine ⟨max 4 A, ?_⟩
  intro n hn hex he hodd hDA
  by_cases hsmall : padicValNat 2 n ≤ 4
  · exact hsmall.trans (le_max_left _ _)
  have hn0 := hn.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have rp := Nat.prime_of_mem_primeFactors hr
    have hp := rp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have hx : ¬ 2 ≤ n.factorization r := fun k =>
      hr3 ((hex r).mp ⟨rp,hr2,(rp.pow_dvd_iff_le_factorization hn0).mpr k⟩)
    omega
  have h3 : 3 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, Nat.dvd_of_factorization_pos (by omega), hn0⟩
  let P := (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ))
  obtain ⟨hP, E⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.kernel_balance_one hn h3 (by decide) hs
  change ∀ p ∈ P, p.Prime ∧ p ≠ 2 at hP
  change (2^n.factorization 2+1)*(1+3^n.factorization 3)*(∏ p ∈ P, (p+1)) =
    2^(n.factorization 2+1)*3^n.factorization 3*(∏ p ∈ P, p) at E
  rw [Nat.factorization_def n Nat.prime_two, he] at E
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3^764 → c ∈ ({3} : Finset ℕ) :=
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.prime_dvd_prime_pow (by decide)
  have outside : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := by simp
  obtain ⟨S1,S2,S3,S4,S5,S6,S7,S8⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.facts hP hK E
  have hdvd : ∀ p ∈ P, p ∣ n := fun p hp =>
    Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_filter.mp hp).1)
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by decide) (outside (by decide)) (by decide)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by decide) (outside (by decide)) 41 g41 (by decide)
  have not13 : ¬ 13 ∣ n := by
    intro h
    have g13 : 13 ∈ P := Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨by decide,Nat.mem_primeFactors.mpr ⟨by norm_num,h,hn0⟩⟩,by decide⟩
    have eq := S3 7 (by norm_num) (by decide) (outside (by decide)) 13 g13 41 g41 (by decide) (by decide)
    omega
  have g5 : 5 ∈ P := by
    by_contra hab
    have hlow : ∀ p ∈ P, p.Prime ∧ 7 ≤ p := by
      intro p hp
      obtain ⟨pr,ne2⟩ := hP p hp
      have ne3 : p ≠ 3 := fun h => (Finset.mem_filter.mp hp).2 (Finset.mem_singleton.mpr h)
      have ne5 : p ≠ 5 := fun h => hab (h ▸ hp)
      refine ⟨pr, ?_⟩
      by_contra! h
      have smallPrime : ∀ q : ℕ, q ≤ 6 → q.Prime → q=2 ∨ q=3 ∨ q=5 := by
        intro q hq prq
        revert prq
        interval_cases q <;> decide
      rcases smallPrime p (by omega) pr with h | h | h <;> contradiction
    have bound := hchains P hlow
      (fun c pr hc => S1 c pr (by omega) (outside (by omega)))
      (fun c pr hc => S3 c pr (by omega) (outside (by omega)))
    have denom : 0 < ∏ p ∈ P, p := Finset.prod_pos (fun p hp => (hP p hp).1.pos)
    have hpow : 32 ≤ 2^padicValNat 2 n :=
      (show 2^5 ≤ 2^padicValNat 2 n from Nat.pow_le_pow_right (by decide) (by omega))
    apply deficit_contradiction hpow (show 27 ≤ 3^764 by decide) denom bound
    rw [Nat.add_comm 1 (3^764), pow_succ 2 (padicValNat 2 n),
      Nat.mul_comm (2^padicValNat 2 n) 2] at E
    exact E
  have dividesprod : 5 ∣ ∏ p ∈ P, p := Finset.dvd_prod_of_mem (fun p : ℕ => p) g5
  have dvdleft : 5 ∣ (2^padicValNat 2 n+1)*(1+3^764)*(∏ p ∈ P, (p+1)) := by
    rw [E]
    exact dvd_mul_of_dvd_right dividesprod _
  have hp5 : Nat.Prime 5 := by decide
  have d5 := (hp5.dvd_mul.mp dvdleft).resolve_left (by
    intro h
    rcases hp5.dvd_mul.mp h with h | h
    · exact two_odd_excludes_five hodd h
    · exact (by decide : ¬ 5 ∣ 1+3^764) h)
  obtain ⟨q,hq,dq⟩ := hp5.prime.exists_mem_finset_dvd d5
  exact (hA n hn hex he hodd hDA (hdvd 5 g5) (hdvd 7 g7) (hdvd 41 g41) not13
    ⟨q,(hP q hq).1,hdvd q hq,dq,S6 5 hp5 (by decide) (outside (by decide)) q hq⟩).trans
      (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H2_R1_H1_R1
