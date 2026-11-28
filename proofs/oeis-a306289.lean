import OMAStatements.S_oeis_a306289
import Mathlib

namespace OMA.S_oeis_a306289

lemma key (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (n ≡ k [MOD A091999 (k + 1)] ∨ n ≡ A306277 (k + 1) [MOD A091999 (k + 1)]) ↔
      A007310 (k + 1) ∣ A007310 (n + 1) := by
  obtain ⟨p, hp⟩ : ∃ p, p = A007310 (k + 1) := ⟨_, rfl⟩
  have hp2 : A091999 (k + 1) = 2 * p := by rw [hp]; rfl
  rw [← hp, hp2]
  have hpv : p = 3 * (k + 1) - (if (k + 1) % 2 = 0 then 1 else 2) := by rw [hp]; rfl
  have h6 : A306277 (k + 1) = 5 * (k + 1) - (if (k + 1) % 2 = 0 then 2 else 4) := rfl
  have hx : A007310 (n + 1) = 3 * (n + 1) - (if (n + 1) % 2 = 0 then 1 else 2) := rfl
  rw [h6]
  constructor
  · rintro (h | h)
    · have h' : n % (2 * p) = k % (2 * p) := h
      have hlt : k < 2 * p := by split_ifs at hpv <;> omega
      rw [Nat.mod_eq_of_lt hlt] at h'
      have hq := Nat.mod_add_div n (2 * p)
      obtain ⟨r, hr⟩ : ∃ r, r = p * (n / (2 * p)) := ⟨_, rfl⟩
      have e : 2 * p * (n / (2 * p)) = 2 * r := by rw [hr]; ring
      have hnr : n = k + 2 * r := by omega
      have : A007310 (n + 1) = p + 6 * r := by
        rw [hx]; split_ifs at hpv ⊢ <;> omega
      rw [this]
      exact dvd_add dvd_rfl ⟨6 * (n / (2 * p)), by rw [hr]; ring⟩
    · have h' : n % (2 * p) = (5 * (k + 1) - (if (k + 1) % 2 = 0 then 2 else 4)) % (2 * p) := h
      have hlt : 5 * (k + 1) - (if (k + 1) % 2 = 0 then 2 else 4) < 2 * p := by
        split_ifs at hpv ⊢ <;> omega
      rw [Nat.mod_eq_of_lt hlt] at h'
      have hq := Nat.mod_add_div n (2 * p)
      obtain ⟨r, hr⟩ : ∃ r, r = p * (n / (2 * p)) := ⟨_, rfl⟩
      have e : 2 * p * (n / (2 * p)) = 2 * r := by rw [hr]; ring
      have hnr : n = (5 * (k + 1) - (if (k + 1) % 2 = 0 then 2 else 4)) + 2 * r := by omega
      have : A007310 (n + 1) = 5 * p + 6 * r := by
        rw [hx]; split_ifs at hpv hnr ⊢ <;> omega
      rw [this]
      exact dvd_add (dvd_mul_left _ _) ⟨6 * (n / (2 * p)), by rw [hr]; ring⟩
  · rintro ⟨u, hu⟩
    have hu6 : u % 6 = 1 ∨ u % 6 = 5 := by
      have hm := Nat.mul_mod p u 6
      have hp6 : p % 6 = 1 ∨ p % 6 = 5 := by split_ifs at hpv <;> omega
      have hx6 : A007310 (n + 1) % 6 = 1 ∨ A007310 (n + 1) % 6 = 5 := by
        rw [hx]; split_ifs <;> omega
      rw [hu] at hx6
      have : u % 6 < 6 := Nat.mod_lt _ (by norm_num)
      rcases hp6 with h | h <;> rw [h] at hm <;> rw [hm] at hx6 <;>
        interval_cases (u % 6) <;> simp_all
    obtain ⟨s, hs⟩ : ∃ s, s = p * (u / 6) := ⟨_, rfl⟩
    have hu' : u = 6 * (u / 6) + u % 6 := by omega
    have e : p * u = 6 * s + p * (u % 6) := by
      rw [hs]; conv_lhs => rw [hu']
      ring
    have e2 : 2 * p * (u / 6) = 2 * s := by rw [hs]; ring
    rcases hu6 with h | h
    · left
      rw [h] at e
      have hnn : n = k + 2 * p * (u / 6) := by
        rw [e2]; have := hx; rw [hu] at this; split_ifs at hpv this <;> omega
      show n % (2 * p) = k % (2 * p)
      rw [hnn, show k + 2 * p * (u / 6) = k + (2 * p) * (u / 6) from rfl, Nat.add_mul_mod_self_left]
    · right
      rw [h] at e
      have hnn : n = (5 * (k + 1) - (if (k + 1) % 2 = 0 then 2 else 4)) + 2 * p * (u / 6) := by
        rw [e2]; have := hx; rw [hu] at this; split_ifs at hpv this ⊢ <;> omega
      show n % (2 * p) = _ % (2 * p)
      rw [hnn, Nat.add_mul_mod_self_left]

end OMA.S_oeis_a306289

theorem OMA.solution : type_of% @OMA.S_oeis_a306289.main := by
  intro n m hn hm h hno
  open OMA.S_oeis_a306289 in
  have hxv : A007310 (n + 1) = 3 * (n + 1) - (if (n + 1) % 2 = 0 then 1 else 2) := rfl
  open OMA.S_oeis_a306289 in
  have hpv : A007310 (m + 1) = 3 * (m + 1) - (if (m + 1) % 2 = 0 then 1 else 2) := rfl
  open OMA.S_oeis_a306289 in
  have hdiv : A007310 (m + 1) ∣ A007310 (n + 1) := (key m n hm hn).1 h
  open OMA.S_oeis_a306289 in
  have hx5 : 5 ≤ A007310 (n + 1) := by rw [hxv]; split_ifs <;> omega
  open OMA.S_oeis_a306289 in
  have hp5 : 5 ≤ A007310 (m + 1) := by rw [hpv]; split_ifs <;> omega
  open OMA.S_oeis_a306289 in
  have hx6 : A007310 (n + 1) % 6 = 1 ∨ A007310 (n + 1) % 6 = 5 := by
    rw [hxv]; split_ifs <;> omega
  open OMA.S_oeis_a306289 in
  show Nat.minFac (A007310 (n + 1)) = A007310 (m + 1)
  open OMA.S_oeis_a306289 in
  have hqp : (Nat.minFac (A007310 (n + 1))).Prime := Nat.minFac_prime (by omega)
  open OMA.S_oeis_a306289 in
  obtain ⟨q, hq⟩ : ∃ q, q = Nat.minFac (A007310 (n + 1)) := ⟨_, rfl⟩
  open OMA.S_oeis_a306289 in
  rw [← hq] at hqp ⊢
  open OMA.S_oeis_a306289 in
  have hqd : q ∣ A007310 (n + 1) := by rw [hq]; exact Nat.minFac_dvd _
  open OMA.S_oeis_a306289 in
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : 2 ∣ A007310 (n + 1) := hqd
    omega
  open OMA.S_oeis_a306289 in
  have hq3 : q ≠ 3 := by
    rintro rfl
    have : 3 ∣ A007310 (n + 1) := hqd
    omega
  open OMA.S_oeis_a306289 in
  have hqodd : q % 2 = 1 := by
    by_contra hne2
    rcases hqp.eq_one_or_self_of_dvd 2 (by omega) with h2 | h2 <;> omega
  open OMA.S_oeis_a306289 in
  have hqge : 5 ≤ q := by
    have := hqp.two_le
    omega
  open OMA.S_oeis_a306289 in
  have hq3' : q % 3 ≠ 0 := by
    intro h3
    rcases (Nat.Prime.eq_one_or_self_of_dvd hqp 3 (by omega)) with h | h <;> omega
  open OMA.S_oeis_a306289 in
  obtain ⟨j, hj1, hj⟩ : ∃ j, 1 ≤ j ∧ q = A007310 (j + 1) := by
    have h6 : q % 6 = 1 ∨ q % 6 = 5 := by omega
    rcases h6 with h6 | h6
    · refine ⟨2 * (q / 6), by omega, ?_⟩
      have : (2 * (q / 6) + 1) % 2 = 1 := by omega
      unfold A007310
      rw [if_neg (by omega)]
      omega
    · refine ⟨2 * (q / 6) + 1, by omega, ?_⟩
      have : (2 * (q / 6) + 1 + 1) % 2 = 0 := by omega
      unfold A007310
      rw [if_pos (by omega)]
      omega
  open OMA.S_oeis_a306289 in
  have hhyp : (n ≡ j [MOD A091999 (j + 1)] ∨ n ≡ A306277 (j + 1) [MOD A091999 (j + 1)]) :=
    (key j n hj1 hn).2 (by rw [← hj]; exact hqd)
  open OMA.S_oeis_a306289 in
  have hjm : m ≤ j := by
    by_contra hlt
    exact hno j hj1 (by omega) hhyp
  open OMA.S_oeis_a306289 in
  have hqle : q ≤ A007310 (m + 1) := by
    rw [hq]; exact Nat.minFac_le_of_dvd (by omega) hdiv
  open OMA.S_oeis_a306289 in
  have hpq : A007310 (m + 1) ≤ q := by
    rw [hj, hpv]; unfold A007310; split_ifs <;> omega
  omega
