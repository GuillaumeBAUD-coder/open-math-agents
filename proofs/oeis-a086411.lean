import OMAStatements.S_oeis_a086411
import Mathlib

namespace A086411Aux

lemma two_dvd_pred {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) : 2 ∣ q - 1 := by
  rcases hq.eq_two_or_odd' with h | h
  · exact absurd h h2
  · rcases h with ⟨r, rfl⟩
    exact ⟨r, by omega⟩

lemma L1 {k q : ℕ} (hdiv : Nat.totient k ∣ k) (hq : q.Prime) (h2 : q ≠ 2) (hqk : q ∣ k) :
    2 ∣ k := by
  have h1 : Nat.totient q ∣ Nat.totient k := Nat.totient_dvd_of_dvd hqk
  rw [Nat.totient_prime hq] at h1
  exact (two_dvd_pred hq h2).trans (h1.trans hdiv)

lemma red {a m d : ℕ} (ha : 1 ≤ a) (hd : Odd d) (hdm : d ∣ m)
    (hdiv : Nat.totient (2 ^ a * m) ∣ 2 ^ a * m) : Nat.totient d ∣ 2 * m := by
  have hcop : Nat.Coprime (2 ^ a) d := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hd)
  have h1 : Nat.totient (2 ^ a * d) ∣ Nat.totient (2 ^ a * m) :=
    Nat.totient_dvd_of_dvd (Nat.mul_dvd_mul_left _ hdm)
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two (by omega)] at h1
  have e2 : (2 : ℕ) - 1 = 1 := rfl
  rw [e2, mul_one] at h1
  obtain ⟨c, hc⟩ := h1.trans hdiv
  have e : 2 ^ a = 2 ^ (a - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [e] at hc
  refine ⟨c, ?_⟩
  have hpos : 0 < 2 ^ (a - 1) := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← mul_assoc, hc]
  ring

lemma odd_part {a m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 2 ^ a * m) : p ∣ m := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)) hp2
  · exact h

lemma a_pos {a m : ℕ} (hm : Odd m) (h : 2 ∣ 2 ^ a * m) : 1 ≤ a := by
  by_contra hc
  have h0 : a = 0 := by omega
  subst h0
  rw [pow_zero, one_mul] at h
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)

lemma L2 {k p q : ℕ} (hk : k ≠ 0) (hdiv : Nat.totient k ∣ k) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) (hpk : p ∣ k) (hqk : q ∣ k) : False := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk
  have ha : 1 ≤ a := a_pos hm (L1 hdiv hp hp2 hpk)
  have hpm : p ∣ m := odd_part hp hp2 hpk
  have hqm : q ∣ m := odd_part hq hq2 hqk
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hpqm : p * q ∣ m := hcop.mul_dvd_of_dvd_of_dvd hpm hqm
  have hodd : Odd (p * q) := (hp.odd_of_ne_two hp2).mul (hq.odd_of_ne_two hq2)
  have h3 := red ha hodd hpqm hdiv
  rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.totient_prime hq] at h3
  obtain ⟨r, hr⟩ := two_dvd_pred hp hp2
  obtain ⟨s, hs⟩ := two_dvd_pred hq hq2
  rw [hr, hs] at h3
  obtain ⟨c, hc⟩ := h3
  have h4 : 2 * m = 2 * (2 * (r * s * c)) := by
    rw [hc]
    ring
  rcases hm with ⟨t, ht⟩
  omega

lemma L3 {k q : ℕ} (hk : k ≠ 0) (hdiv : Nat.totient k ∣ k) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqk : q ∣ k) : q = 3 := by
  obtain ⟨a, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hk
  have h2k := L1 hdiv hq hq2 hqk
  rw [hkm] at h2k hqk
  have ha : 1 ≤ a := a_pos hm h2k
  have hqm : q ∣ m := odd_part hq hq2 hqk
  have h3 : Nat.totient q ∣ 2 * m := red ha (hq.odd_of_ne_two hq2) hqm (by rw [← hkm]; exact hdiv)
  rw [Nat.totient_prime hq] at h3
  obtain ⟨r, hr⟩ := two_dvd_pred hq hq2
  rw [hr] at h3
  have hrm : r ∣ m := (Nat.mul_dvd_mul_iff_left (by norm_num)).mp h3
  have hq2le := hq.two_le
  by_contra hne
  have hr1 : r ≠ 1 := by
    intro h
    apply hne
    omega
  obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd hr1
  have hpm : p ∣ m := hpr.trans hrm
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hpm)
  have hr0 : r ≠ 0 := by
    rintro rfl
    omega
  have hple : p ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hpr
  have hpq : p ≠ q := by omega
  exact L2 hk hdiv hp hq hp2 hq2 hpq (by rw [hkm]; exact Dvd.dvd.mul_left hpm _)
    (by rw [hkm]; exact hqk)

lemma char_forward {k : ℕ} (hk : 0 < k) (hdiv : Nat.totient k ∣ k) :
    k = 1 ∨ ∃ i j, k = 2 ^ (i + 1) * 3 ^ j := by
  have hk0 : k ≠ 0 := by omega
  obtain ⟨a, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hk0
  have hnot : ¬ 2 ∣ m := fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hnot (dvd_zero 2)
  have hm3 : m = 3 ^ m.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd hm0 (by
    intro d hd hdm
    have hd2 : d ≠ 2 := by
      rintro rfl
      exact hnot hdm
    exact L3 hk0 hdiv hd hd2 (by rw [hkm]; exact Dvd.dvd.mul_left hdm _))
  rcases Nat.eq_zero_or_pos a with ha | ha
  · left
    subst ha
    rw [pow_zero, one_mul] at hkm
    by_contra hne
    obtain ⟨d, hd, hdk⟩ := Nat.exists_prime_and_dvd hne
    have hd2 : d ≠ 2 := by
      rintro rfl
      rw [hkm] at hdk
      exact hnot hdk
    have h2 := L1 hdiv hd hd2 hdk
    rw [hkm] at h2
    exact hnot h2
  · right
    refine ⟨a - 1, m.primeFactorsList.length, ?_⟩
    rw [hkm, show a - 1 + 1 = a by omega]
    congr 1

lemma tot_val (i j : ℕ) : Nat.totient (2 ^ (i + 1) * 3 ^ (j + 1)) = 2 ^ (i + 1) * 3 ^ j := by
  have hcop : Nat.Coprime (2 ^ (i + 1)) (3 ^ (j + 1)) := Nat.Coprime.pow _ _ (by norm_num)
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two (by omega),
    Nat.totient_prime_pow Nat.prime_three (by omega)]
  simp only [Nat.add_sub_cancel]
  norm_num
  ring

lemma tot_val0 (i : ℕ) : Nat.totient (2 ^ (i + 1)) = 2 ^ i := by
  rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
  simp

lemma char_backward (i j : ℕ) : Nat.totient (2 ^ (i + 1) * 3 ^ j) ∣ 2 ^ (i + 1) * 3 ^ j := by
  rcases j with _ | j
  · rw [pow_zero, mul_one, tot_val0]
    exact pow_dvd_pow 2 (by omega)
  · rw [tot_val]
    exact Nat.mul_dvd_mul_left _ (pow_dvd_pow 3 (by omega))

lemma quot_val (i j : ℕ) :
    2 ^ (i + 1) * 3 ^ j / Nat.totient (2 ^ (i + 1) * 3 ^ j) = if j = 0 then 2 else 3 := by
  rcases j with _ | j
  · rw [pow_zero, mul_one, tot_val0, if_pos rfl, pow_succ]
    exact Nat.mul_div_cancel_left 2 (by positivity)
  · rw [tot_val, if_neg (by omega), pow_succ 3 j, ← mul_assoc]
    exact Nat.mul_div_cancel_left 3 (by positivity)

open OMA.S_oeis_a086411 in
lemma gpf_val (i j : ℕ) (h : 0 < i + j) : gpf (2 ^ i * 3 ^ j) = if j = 0 then 2 else 3 := by
  unfold gpf
  rcases j with _ | j
  · have hi : i ≠ 0 := by omega
    rw [pow_zero, mul_one, Nat.primeFactors_prime_pow hi Nat.prime_two]
    simp
  · rcases i with _ | i
    · rw [pow_zero, one_mul, Nat.primeFactors_prime_pow (by omega) Nat.prime_three]
      simp
    · rw [Nat.primeFactors_mul (by positivity) (by positivity),
        Nat.primeFactors_prime_pow (by omega) Nat.prime_two,
        Nat.primeFactors_prime_pow (by omega) Nat.prime_three]
      simp [Finset.sup_union]

open OMA.S_oeis_a086411 in
lemma smooth_inf : (Set.ofPred Is3Smooth).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun i : ℕ => 2 ^ i)
    (Nat.pow_right_injective (le_refl 2)) (fun i => ⟨i, 0, by simp⟩)

open OMA.S_oeis_a086411 in
lemma phi_iff (k : ℕ) : PhiDvd k ↔ k = 1 ∨ ∃ i j, k = 2 ^ (i + 1) * 3 ^ j := by
  constructor
  · rintro ⟨h1, h2⟩
    exact char_forward h1 h2
  · rintro (rfl | ⟨i, j, rfl⟩)
    · exact ⟨by norm_num, by simp⟩
    · exact ⟨by positivity, char_backward i j⟩

open OMA.S_oeis_a086411 in
lemma phi_inf : (Set.ofPred PhiDvd).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun i : ℕ => 2 ^ (i + 1)) ?_
    (fun i => (phi_iff _).mpr (Or.inr ⟨i, 0, by simp⟩))
  intro x y h
  have h2 := Nat.pow_right_injective (le_refl 2) h
  omega

open OMA.S_oeis_a086411 in
lemma smooth_pos {m : ℕ} (h : Is3Smooth m) : 0 < m := by
  obtain ⟨i, j, rfl⟩ := h
  positivity

open OMA.S_oeis_a086411 in
noncomputable def F (n : ℕ) : ℕ := if n = 0 then 1 else 2 * Nat.nth Is3Smooth (n - 1)

open OMA.S_oeis_a086411 in
lemma F_eq (n : ℕ) : F n = Nat.nth PhiDvd n := by
  have key := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := PhiDvd) F ?_ ?_ ?_
  · exact key (fun hf => absurd hf phi_inf)
  · intro k hk
    rcases (phi_iff k).mp hk with rfl | ⟨i, j, rfl⟩
    · exact ⟨0, fun hf => absurd hf phi_inf, by simp [F]⟩
    · have hs : Is3Smooth (2 ^ i * 3 ^ j) := ⟨i, j, rfl⟩
      obtain ⟨t, _, ht⟩ := Nat.exists_lt_card_nth_eq hs
      refine ⟨t + 1, fun hf => absurd hf phi_inf, ?_⟩
      show F (t + 1) = 2 ^ (i + 1) * 3 ^ j
      unfold F
      rw [if_neg (by omega), Nat.add_sub_cancel, ht]
      ring
  · intro t _
    show PhiDvd (F t)
    unfold F
    split_ifs with h
    · exact (phi_iff 1).mpr (Or.inl rfl)
    · obtain ⟨i, j, hij⟩ := Nat.nth_mem_of_infinite smooth_inf (t - 1)
      rw [hij]
      exact (phi_iff _).mpr (Or.inr ⟨i, j, by ring⟩)
  · intro x _ y _ hxy
    show F x < F y
    unfold F
    by_cases hx : x = 0
    · subst hx
      rw [if_pos rfl, if_neg (by omega)]
      have h1 := smooth_pos (Nat.nth_mem_of_infinite smooth_inf (y - 1))
      omega
    · rw [if_neg hx, if_neg (by omega)]
      have h1 := Nat.nth_strictMono smooth_inf (show x - 1 < y - 1 by omega)
      omega

end A086411Aux

open OMA.S_oeis_a086411 A086411Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a086411.main := by
  intro n hn
  unfold a b smooth3 phiDvdSeq
  rw [show n + 1 - 1 = n by omega, ← F_eq n]
  unfold F
  rw [if_neg (by omega)]
  obtain ⟨i, j, hij⟩ := Nat.nth_mem_of_infinite smooth_inf (n - 1)
  have hgt : 1 < Nat.nth Is3Smooth (n - 1) := by
    have h0 := smooth_pos (Nat.nth_mem_of_infinite smooth_inf 0)
    have h1 := Nat.nth_strictMono smooth_inf (show 0 < n - 1 by omega)
    omega
  rw [hij] at hgt ⊢
  have hpos : 0 < i + j := by
    by_contra h
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst hi
    subst hj
    simp at hgt
  rw [gpf_val i j hpos, show 2 * (2 ^ i * 3 ^ j) = 2 ^ (i + 1) * 3 ^ j by ring, quot_val]
