import OMAStatements.S_oeis_a182936
import Mathlib

namespace OMA.S_oeis_a182936

lemma a_pt (k : ℕ) (hk : 1 ≤ k) :
    (a k : ℤ) = (expMangoldt k : ℤ) - (if k.Prime then (k : ℤ) else 0) - (if k = 1 then 1 else 0) := by
  by_cases h1 : k = 1
  · subst h1
    simp [a, expMangoldt, Nat.not_prime_one]
  have hk2 : 2 ≤ k := by omega
  by_cases hp : k.Prime
  · have : (k.properDivisors.filter (fun d => 1 < d)) = ∅ := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_properDivisors, Finset.notMem_empty, iff_false]
      rintro ⟨⟨hd, hlt⟩, h1d⟩
      rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
    have hpp : IsPrimePow k := hp.isPrimePow
    simp [a, this, expMangoldt, hpp, hp, Nat.Prime.minFac_eq hp, h1]
  by_cases hpp : IsPrimePow k
  · obtain ⟨p, e, hpr, he, rfl⟩ := hpp
    have hpn : p.Prime := Nat.prime_iff.mpr hpr
    have he2 : 2 ≤ e := by
      by_contra hlt
      have : e = 1 := by omega
      subst this
      simp at hp
      exact hp hpn
    have hmin : (p ^ e).minFac = p := by
      rw [Nat.Prime.pow_minFac hpn (by omega)]
    have hgcd : ((p ^ e).properDivisors.filter (fun d => 1 < d)).gcd id = p := by
      apply Nat.dvd_antisymm
      · apply Finset.gcd_dvd
        simp only [Finset.mem_filter, Nat.mem_properDivisors]
        refine ⟨⟨dvd_pow_self p (by omega), ?_⟩, hpn.one_lt⟩
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ e := Nat.pow_lt_pow_right hpn.one_lt (by omega)
      · apply Finset.dvd_gcd
        intro d hd
        simp only [Finset.mem_filter, Nat.mem_properDivisors] at hd
        obtain ⟨⟨hdd, _⟩, h1d⟩ := hd
        obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hpn).mp hdd
        have : i ≠ 0 := by
          rintro rfl
          simp at h1d
        exact dvd_pow_self p this
    have hex : expMangoldt (p ^ e) = p := by
      simp [expMangoldt, (hpn.isPrimePow.pow (by omega : e ≠ 0)), hmin]
    simp only [a, hgcd, hex, if_neg hp, h1]
    simp
  · -- at least two distinct prime factors
    have hne : k ≠ 0 := by omega
    have hmin := Nat.minFac_prime h1
    have hnu : ¬ ∃! q, q.Prime ∧ q ∣ k := fun h => hpp ((isPrimePow_iff_unique_prime_dvd).mpr h)
    have : ∃ q, q.Prime ∧ q ∣ k ∧ q ≠ k.minFac := by
      by_contra hcon
      push_neg at hcon
      exact hnu ⟨k.minFac, ⟨hmin, Nat.minFac_dvd k⟩, fun y hy => hcon y hy.1 hy.2⟩
    obtain ⟨q, hq, hqk, hqne⟩ := this
    have hlt : ∀ r, r.Prime → r ∣ k → r < k := by
      intro r hr hrk
      rcases lt_or_eq_of_le (Nat.le_of_dvd (by omega) hrk) with h | h
      · exact h
      · exfalso; subst h; exact hp hr
    have hg : ((k.properDivisors.filter (fun d => 1 < d)).gcd id) ∣ 1 := by
      have h1' : ((k.properDivisors.filter (fun d => 1 < d)).gcd id) ∣ k.minFac := by
        apply Finset.gcd_dvd
        simp only [Finset.mem_filter, Nat.mem_properDivisors]
        exact ⟨⟨Nat.minFac_dvd k, hlt _ hmin (Nat.minFac_dvd k)⟩, hmin.one_lt⟩
      have h2' : ((k.properDivisors.filter (fun d => 1 < d)).gcd id) ∣ q := by
        apply Finset.gcd_dvd
        simp only [Finset.mem_filter, Nat.mem_properDivisors]
        exact ⟨⟨hqk, hlt _ hq hqk⟩, hq.one_lt⟩
      have hcop : Nat.Coprime k.minFac q := (Nat.coprime_primes hmin hq).mpr (Ne.symm hqne)
      have := Nat.dvd_gcd h1' h2'
      rwa [hcop.gcd_eq_one] at this
    have hg1 : ((k.properDivisors.filter (fun d => 1 < d)).gcd id) = 1 := Nat.dvd_one.mp hg
    simp [a, hg1, expMangoldt, hpp, hp, h1]

end OMA.S_oeis_a182936

open OMA.S_oeis_a182936 in
theorem OMA.solution : type_of% @OMA.S_oeis_a182936.main := by
  intro n hn
  have h : ∀ k ∈ Finset.Icc 1 n, ((a k : ℕ) : ℤ) = (expMangoldt k : ℤ) - (if k.Prime then (k : ℤ) else 0) - (if k = 1 then 1 else 0) :=
    fun k hk => a_pt k (Finset.mem_Icc.mp hk).1
  push_cast
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_filter]
  have : ∑ k ∈ Finset.Icc 1 n, (if k = 1 then (1 : ℤ) else 0) = 1 := by
    rw [Finset.sum_ite_eq']
    simp [hn]
  rw [this]

#print axioms OMA.solution
