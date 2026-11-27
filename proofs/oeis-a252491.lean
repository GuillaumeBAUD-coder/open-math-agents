import OMAStatements.S_oeis_a252491
import Mathlib

namespace A252491

/-- The geometric sum `1 + x + ... + x^(m-1)`. -/
def G (x m : ℕ) : ℕ := ∑ i ∈ Finset.range m, x ^ i

lemma G_mul (x m : ℕ) (hx : 1 ≤ x) : G x m * (x - 1) + 1 = x ^ m := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  simpa [G] using geom_sum_mul_add y m

lemma G_succ (x m : ℕ) : G x (m + 1) = x * G x m + 1 := by
  unfold G
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

lemma G_two_le (x m : ℕ) (_hx : 1 ≤ x) (hm : 2 ≤ m) : x + 1 ≤ G x m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [G_succ, G_succ]
  have : 0 ≤ x * G x k := Nat.zero_le _
  nlinarith [Nat.zero_le (x * (x * G x k))]

/-- `G x (a * b) = G x a * G (x ^ a) b`. -/
lemma G_compose (x a b : ℕ) (hx : 2 ≤ x) : G x (a * b) = G x a * G (x ^ a) b := by
  have h1 := G_mul x (a * b) (by omega)
  have h2 := G_mul x a (by omega)
  have h3 := G_mul (x ^ a) b (Nat.one_le_pow _ _ (by omega))
  have hpos : 0 < x - 1 := by omega
  apply Nat.eq_of_mul_eq_mul_right hpos
  have h4 : x ^ a - 1 = G x a * (x - 1) := by omega
  have h5 : G x a * G (x ^ a) b * (x - 1) = G (x ^ a) b * (x ^ a - 1) := by
    rw [h4]; ring
  rw [h5]
  have h6 : x ^ (a * b) = (x ^ a) ^ b := pow_mul x a b
  omega

lemma G_lt (p m : ℕ) (hp : 2 ≤ p) (hm : 2 ≤ m) : G 10 m < G (10 ^ p) m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have h10 : (10 : ℕ) ≤ 10 ^ p := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h10' : (10 : ℕ) < 10 ^ p := by
    calc 10 = 10 ^ 1 := by norm_num
      _ < 10 ^ p := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1 : G 10 (k + 1) ≤ G (10 ^ p) (k + 1) := by
    unfold G
    apply Finset.sum_le_sum
    intro i _
    exact Nat.pow_le_pow_left h10 i
  have h2 : 10 ^ (k + 1) < (10 ^ p) ^ (k + 1) := Nat.pow_lt_pow_left h10' (by omega)
  have e1 : G 10 (k + 2) = G 10 (k + 1) + 10 ^ (k + 1) := by
    unfold G; rw [Finset.sum_range_succ]
  have e2 : G (10 ^ p) (k + 2) = G (10 ^ p) (k + 1) + (10 ^ p) ^ (k + 1) := by
    unfold G; rw [Finset.sum_range_succ]
  omega

/-- Repunits with coprime lengths are coprime. -/
lemma coprime_rep (m p : ℕ) (h : Nat.Coprime m p) : Nat.Coprime (G 10 m) (G 10 p) := by
  have h1 := G_mul 10 m (by norm_num)
  have h2 := G_mul 10 p (by norm_num)
  have h3 := Nat.pow_sub_one_gcd_pow_sub_one 10 m p
  rw [Nat.Coprime] at h
  rw [h] at h3
  have e1 : 10 ^ m - 1 = 9 * G 10 m := by omega
  have e2 : 10 ^ p - 1 = 9 * G 10 p := by omega
  rw [e1, e2, Nat.gcd_mul_left] at h3
  unfold Nat.Coprime
  omega

lemma not_prime_G (p m : ℕ) (hp : p.Prime) (hm : 2 ≤ m) (hne : m ≠ p) :
    ¬ (G (10 ^ p) m).Prime := by
  have hp2 := hp.two_le
  have hx : 2 ≤ 10 ^ p := by
    calc 2 ≤ 10 ^ 1 := by norm_num
      _ ≤ 10 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hd : p ∣ m
  · obtain ⟨j, rfl⟩ := hd
    have hj : 2 ≤ j := by
      rcases j with _ | _ | j
      · omega
      · omega
      · omega
    rw [G_compose _ _ _ hx]
    apply Nat.not_prime_mul
    · have := G_two_le (10 ^ p) p (by omega) hp2
      omega
    · have := G_two_le ((10 ^ p) ^ p) j (Nat.one_le_pow _ _ (by omega)) hj
      have : 1 ≤ (10 ^ p) ^ p := Nat.one_le_pow _ _ (by omega)
      omega
  · have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd).symm
    have hc := coprime_rep m p hcop
    -- `G 10 m ∣ G (10^p) m`
    have h1 := G_mul 10 m (by norm_num)
    have h2 := G_mul 10 p (by norm_num)
    have h3 := G_mul (10 ^ p) m (by omega)
    have h4 := G_mul (10 ^ m) p (Nat.one_le_pow _ _ (by norm_num))
    have e : (10 ^ p) ^ m = (10 ^ m) ^ p := by rw [← pow_mul, ← pow_mul, mul_comm]
    have hdvd : G 10 m ∣ G (10 ^ p) m * G 10 p := by
      refine ⟨G (10 ^ m) p, ?_⟩
      have e1 : 10 ^ m - 1 = G 10 m * 9 := by omega
      have e2 : 10 ^ p - 1 = G 10 p * 9 := by omega
      have h5 : G (10 ^ p) m * (G 10 p * 9) = G (10 ^ m) p * (G 10 m * 9) := by
        rw [← e1, ← e2]; omega
      nlinarith
    have hdvd' : G 10 m ∣ G (10 ^ p) m := hc.dvd_of_dvd_mul_right hdvd
    have hlt := G_lt p m hp2 hm
    have hge := G_two_le 10 m (by norm_num) hm
    exact Nat.not_prime_of_dvd_of_lt hdvd' (by omega) hlt

lemma G_eq_a (p : ℕ) (hp : 1 ≤ p) : G (10 ^ p) p = OMA.S_oeis_a252491.a p := by
  unfold OMA.S_oeis_a252491.a
  have h := G_mul (10 ^ p) p (Nat.one_le_pow _ _ (by norm_num))
  have e : (10 ^ p) ^ p = 10 ^ (p ^ 2) := by rw [← pow_mul, sq]
  have hpos : 0 < 10 ^ p - 1 := by
    have : 10 ^ 1 ≤ 10 ^ p := Nat.pow_le_pow_right (by norm_num) hp
    omega
  symm
  apply Nat.div_eq_of_eq_mul_left hpos
  omega

end A252491

open A252491 in
theorem OMA.solution : type_of% @OMA.S_oeis_a252491.main := by
  intro p hp hnp
  have hp2 := hp.two_le
  unfold OMA.S_oeis_a252491.repetitionCount
  have h0 : (10 : ℕ) ^ (p - 1) ≠ 0 := by positivity
  rw [if_neg h0]
  have hL : (Nat.digits 10 (10 ^ (p - 1))).length = p := by
    rw [Nat.length_digits 10 _ (by norm_num) h0, Nat.log_pow (by norm_num)]
    omega
  rw [hL]
  have hempty : {r : ℕ | 0 < r ∧
      (10 ^ (p - 1) * (∑ i ∈ Finset.range r, (10 ^ p) ^ i) * 10 + 1).Prime} = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro r ⟨hr, hprime⟩
    have e : 10 ^ (p - 1) * (∑ i ∈ Finset.range r, (10 ^ p) ^ i) * 10 + 1 = G (10 ^ p) (r + 1) := by
      rw [G_succ]
      have : (10 : ℕ) ^ p = 10 ^ (p - 1) * 10 := by
        rw [← pow_succ]; congr 1; omega
      unfold G
      rw [this]; ring
    rw [e] at hprime
    by_cases hrp : r + 1 = p
    · rw [hrp, G_eq_a p (by omega)] at hprime
      exact hnp hprime
    · exact not_prime_G p (r + 1) hp (by omega) hrp hprime
  rw [hempty, Nat.sInf_empty]
