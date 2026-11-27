import OMAReductions.R_Erdos479_erdos_479_R1

-- Credit: @jagong-cmu

namespace E479

lemma modeq_neg_of_dvd {n c : ℕ} (h : n ∣ 2 ^ n + c) :
    (2 : ℤ) ^ n ≡ -(c : ℤ) [ZMOD (n : ℤ)] := by
  apply Int.modEq_iff_dvd.2
  have h' : ((n : ℤ)) ∣ (((2 ^ n + c : ℕ)) : ℤ) := Int.natCast_dvd_natCast.2 h
  push_cast at h'
  rw [show -(c : ℤ) - 2 ^ n = -(2 ^ n + c) by ring]
  exact (dvd_neg).2 h'

lemma case_zero : { n : ℕ | (2 : ℤ) ^ n ≡ 0 [ZMOD (n : ℤ)] }.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨2 ^ a, ?_, Nat.lt_two_pow_self⟩
  have h : 2 ^ a ∣ 2 ^ (2 ^ a) + 0 := by
    simpa using pow_dvd_pow 2 (Nat.lt_two_pow_self (n := a)).le
  simpa using modeq_neg_of_dvd h

lemma three_pow_dvd (j : ℕ) : 3 ^ (j + 1) ∣ 2 ^ (3 ^ j) + 1 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    obtain ⟨t, ht⟩ := ih
    have h3 : 3 ∣ (2 ^ (3 ^ j)) ^ 2 - 2 ^ (3 ^ j) + 1 := by
      have hpos : 2 ^ (3 ^ j) ≤ (2 ^ (3 ^ j)) ^ 2 := Nat.le_self_pow (by norm_num) _
      have : (2 ^ (3 ^ j)) ^ 2 - 2 ^ (3 ^ j) + 1 + 3 * (2 ^ (3 ^ j) + 1) =
          (2 ^ (3 ^ j) + 1) ^ 2 + 3 := by
        zify [hpos]; ring
      have h1 : 3 ∣ 2 ^ (3 ^ j) + 1 := by
        rw [ht]; exact Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _
      have h2 : 3 ∣ (2 ^ (3 ^ j) + 1) ^ 2 + 3 :=
        dvd_add (dvd_pow h1 (by norm_num)) dvd_rfl
      rw [← this] at h2
      exact (Nat.dvd_add_left (dvd_mul_right 3 _)).1 h2
    have hfac : 2 ^ (3 ^ (j + 1)) + 1 =
        (2 ^ (3 ^ j) + 1) * ((2 ^ (3 ^ j)) ^ 2 - 2 ^ (3 ^ j) + 1) := by
      have hpos : 2 ^ (3 ^ j) ≤ (2 ^ (3 ^ j)) ^ 2 := Nat.le_self_pow (by norm_num) _
      rw [pow_succ, pow_mul]
      zify [hpos]; ring
    rw [hfac, pow_succ]
    exact mul_dvd_mul ⟨t, ht⟩ h3

lemma case_neg_one : { n : ℕ | (2 : ℤ) ^ n ≡ -1 [ZMOD (n : ℤ)] }.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨3 ^ (a + 1), ?_, ?_⟩
  · have h : 3 ^ (a + 1) ∣ 2 ^ (3 ^ (a + 1)) + 1 :=
      (pow_dvd_pow 3 (by omega : a + 1 ≤ a + 1 + 1)).trans
        (three_pow_dvd (a + 1))
    simpa using modeq_neg_of_dvd h
  · calc a < a + 1 := Nat.lt_succ_self a
      _ < 3 ^ (a + 1) := Nat.lt_pow_self (by norm_num : 1 < 3)

/-- invariant for the k = -2 chain n -> 2^n + 2 -/
def P2 (n : ℕ) : Prop := Even n ∧ 2 ≤ n ∧ n ∣ 2 ^ n + 2 ∧ (n - 1) ∣ 2 ^ n + 1

lemma P2_step {n : ℕ} (h : P2 n) : P2 (2 ^ n + 2) := by
  obtain ⟨⟨r, hr⟩, h2, ⟨s, hs⟩, ⟨t, ht⟩⟩ := h
  set m := 2 ^ n + 2 with hm
  have hn1 : n - 1 + 1 = n := by omega
  have hm2 : m = 2 * (2 ^ (n - 1) + 1) := by
    rw [hm, mul_add, ← pow_succ', hn1]
  have hodd1 : Odd (2 ^ (n - 1) + 1) := by
    have : n - 1 ≠ 0 := by omega
    exact Even.add_one ((Nat.even_pow' this).2 even_two)
  have hm1 : m - 1 = 2 ^ n + 1 := by omega
  have hoddt : Odd t := by
    have : Odd (2 ^ n + 1) := Even.add_one ((Nat.even_pow' (by omega)).2 even_two)
    rw [ht] at this
    exact (Nat.odd_mul.1 this).2
  have hodds : Odd s := by
    by_contra hse
    rw [Nat.not_odd_iff_even] at hse
    obtain ⟨q, hq⟩ := hse
    have : 2 * (2 ^ (n - 1) + 1) = 2 * (2 * (r * q)) := by
      rw [← hm2, hs, hr, hq]; ring
    have h' : 2 ^ (n - 1) + 1 = 2 * (r * q) := by omega
    rw [h'] at hodd1
    exact (Nat.not_odd_iff_even.2 (even_two_mul _)) hodd1
  refine ⟨⟨2 ^ (n - 1) + 1, by omega⟩, by omega, ?_, ?_⟩
  · have hdiv : 2 ^ (n - 1) + 1 ∣ 2 ^ (m - 1) + 1 := by
      rw [hm1, ht, pow_mul]
      simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ (n - 1)) 1 hoddt
    have hmm : m - 1 + 1 = m := by omega
    have : 2 ^ m + 2 = 2 * (2 ^ (m - 1) + 1) := by
      rw [mul_add, ← pow_succ', hmm]
    rw [this, hm2]
    exact mul_dvd_mul_left 2 (by rw [← hm2]; exact hdiv)
  · rw [hm1]
    have : m = n * s := hs
    rw [this, pow_mul]
    simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ n) 1 hodds

lemma case_neg_two : { n : ℕ | (2 : ℤ) ^ n ≡ -2 [ZMOD (n : ℤ)] }.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  have key : ∀ a : ℕ, ∃ n, P2 n ∧ a < n := by
    intro a
    induction a with
    | zero => exact ⟨2, ⟨⟨1, rfl⟩, le_rfl, by norm_num, by norm_num⟩, by norm_num⟩
    | succ a ih =>
      obtain ⟨n, hn, han⟩ := ih
      refine ⟨2 ^ n + 2, P2_step hn, ?_⟩
      have := Nat.lt_two_pow_self (n := n)
      omega
  intro a
  obtain ⟨n, hn, han⟩ := key a
  exact ⟨n, by simpa using modeq_neg_of_dvd hn.2.2.1, han⟩

lemma case_two_pow {i : ℕ} (hi : 1 ≤ i) :
    { n : ℕ | (2 : ℤ) ^ n ≡ 2 ^ i [ZMOD (n : ℤ)] }.Infinite := by
  obtain ⟨a, b, hb, hib⟩ := Nat.exists_eq_two_pow_mul_odd (n := i) (by omega)
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have htot : Nat.totient b ≠ 0 := by simpa [Nat.totient_eq_zero] using hb0
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hp, hpN, hp1⟩ := Nat.exists_prime_gt_modEq_one (N + i) htot
  refine ⟨i * p, ?_, ?_⟩
  · show (2 : ℤ) ^ (i * p) ≡ 2 ^ i [ZMOD ((i * p : ℕ) : ℤ)]
    have hcast : ((2 : ℤ) ^ (i * p)) = ((2 ^ (i * p) : ℕ) : ℤ) := by push_cast; rfl
    have hcast2 : ((2 : ℤ) ^ i) = ((2 ^ i : ℕ) : ℤ) := by push_cast; rfl
    rw [hcast, hcast2, Int.natCast_modEq_iff]
    have hcop : Nat.Coprime i p := by
      apply Nat.Coprime.symm
      apply (Nat.Prime.coprime_iff_not_dvd hp).2
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).1
    constructor
    · -- mod i
      have hle : 2 ^ i ≤ 2 ^ (i * p) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right i hp.pos)
      apply Nat.ModEq.symm
      apply (Nat.modEq_iff_dvd' hle).2
      have hp1' : 1 ≤ p := hp.pos
      have hsplit : 2 ^ (i * p) - 2 ^ i = 2 ^ i * (2 ^ (i * (p - 1)) - 1) := by
        have : i * p = i + i * (p - 1) := by
          obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
          simp only [Nat.add_sub_cancel]; ring
        rw [this, pow_add]
        exact (Nat.mul_sub_one _ _).symm
      rw [hsplit, hib]
      apply mul_dvd_mul
      · apply pow_dvd_pow
        have : a < 2 ^ a := Nat.lt_two_pow_self
        have : 2 ^ a ≤ 2 ^ a * b := Nat.le_mul_of_pos_right _ (by omega)
        have : 2 ^ a * b < 2 ^ (2 ^ a * b) := Nat.lt_two_pow_self
        omega
      · have hφ : Nat.totient b ∣ p - 1 := (Nat.modEq_iff_dvd' hp1').1 hp1.symm
        obtain ⟨c, hc⟩ := hφ
        have hpow : 2 ^ (i * (p - 1)) ≡ 1 [MOD b] := by
          rw [hc, show i * (Nat.totient b * c) = Nat.totient b * (i * c) by ring, pow_mul]
          have h1 : 2 ^ Nat.totient b ≡ 1 [MOD b] :=
            Nat.ModEq.pow_totient ((Nat.coprime_two_left).2 hb)
          simpa using h1.pow (i * c)
        have h1le : 1 ≤ 2 ^ (i * (p - 1)) := Nat.one_le_two_pow
        rw [← hib]
        exact (Nat.modEq_iff_dvd' h1le).1 hpow.symm
    · -- mod p : Fermat
      have := Fact.mk hp
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      rw [pow_mul, ZMod.pow_card]
  · have : p ≤ i * p := Nat.le_mul_of_pos_left p (by omega)
    omega

theorem h1 : ∀ k : ℤ, (k = 0 ∨ k = -1 ∨ k = -2 ∨ ∃ i : ℕ, 1 ≤ i ∧ k = 2 ^ i) →
    { n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] }.Infinite := by
  rintro k (rfl | rfl | rfl | ⟨i, hi, rfl⟩)
  · exact case_zero
  · exact case_neg_one
  · exact case_neg_two
  · exact case_two_pow hi

end E479

theorem OMA.solution : OMA.R_Erdos479_erdos_479_R1.H1 := E479.h1
