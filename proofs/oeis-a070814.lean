import OMAStatements.S_oeis_a070814
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a070814

theorem a070814_gpf_le {n p : ℕ} (hn : n ≠ 1) (hp : p ∈ n.primeFactors) : p ≤ gpf n := by
  unfold gpf
  rw [if_neg hn]
  exact Finset.le_sup (f := id) hp

theorem a070814_gpf_mem {n : ℕ} (hn : 2 ≤ n) : gpf n ∈ n.primeFactors := by
  unfold gpf
  rw [if_neg (by omega)]
  obtain ⟨i, hi, he⟩ :=
    Finset.exists_mem_eq_sup n.primeFactors (Nat.nonempty_primeFactors.mpr (by omega)) id
  rw [he]
  exact hi

theorem a070814_gpf_eq {n q : ℕ} (hn : n ≠ 1) (hq : q ∈ n.primeFactors)
    (h : ∀ p ∈ n.primeFactors, p ≤ q) : gpf n = q := by
  unfold gpf
  rw [if_neg hn]
  exact le_antisymm (Finset.sup_le h) (Finset.le_sup (f := id) hq)

theorem a070814_le_two_of_dvd_pow {p m : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ m) : p ≤ 2 :=
  Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)

theorem a070814_totient_two_pow (k : ℕ) : Nat.totient (2 ^ k) = 2 ^ (k - 1) := by
  rcases k with _ | k
  · simp
  · rw [Nat.totient_prime_pow_succ Nat.prime_two]
    simp

theorem a070814_term_of (k f : ℕ) (hf : f = 1 ∨ f = 3 ∨ f = 5 ∨ f = 15) :
    IsTerm (17 * 2 ^ k * f) := by
  have hf0 : 0 < f := by rcases hf with rfl | rfl | rfl | rfl <;> norm_num
  have hf15 : f ≤ 15 := by rcases hf with rfl | rfl | rfl | rfl <;> norm_num
  have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hpos : 0 < 17 * 2 ^ k * f := by positivity
  have hne1 : 17 * 2 ^ k * f ≠ 1 := by nlinarith
  have hg : gpf (17 * 2 ^ k * f) = 17 := by
    apply a070814_gpf_eq hne1
    · exact Nat.mem_primeFactors.mpr ⟨by norm_num, Dvd.dvd.mul_right (Dvd.intro _ rfl) _, by omega⟩
    · intro p hp
      obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
      rcases (Nat.Prime.dvd_mul hpp).mp hpd with h1 | h1
      · rcases (Nat.Prime.dvd_mul hpp).mp h1 with h2 | h2
        · exact Nat.le_of_dvd (by norm_num) h2
        · have := a070814_le_two_of_dvd_pow hpp h2
          omega
      · have := Nat.le_of_dvd hf0 h1
        omega
  have hcop1 : Nat.Coprime 17 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have hcop2 : Nat.Coprime (17 * 2 ^ k) f := by
    apply Nat.Coprime.mul_left
    · rcases hf with rfl | rfl | rfl | rfl <;> norm_num
    · apply Nat.Coprime.pow_left
      rcases hf with rfl | rfl | rfl | rfl <;> norm_num
  have hfe : ∃ e, Nat.totient f = 2 ^ e := by
    rcases hf with rfl | rfl | rfl | rfl
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨2, by decide⟩
    · exact ⟨3, by decide⟩
  obtain ⟨e, he⟩ := hfe
  have htot : Nat.totient (17 * 2 ^ k * f) = 2 ^ (4 + (k - 1) + e) := by
    rw [Nat.totient_mul hcop2, Nat.totient_mul hcop1, he, a070814_totient_two_pow,
      Nat.totient_prime (by norm_num), pow_add, pow_add]
    norm_num
  have hg2 : gpf (Nat.totient (17 * 2 ^ k * f)) = 2 := by
    rw [htot]
    have hE : 4 + (k - 1) + e ≠ 0 := by omega
    apply a070814_gpf_eq
    · intro h
      have : (2 : ℕ) ^ 4 ∣ 2 ^ (4 + (k - 1) + e) := pow_dvd_pow 2 (by omega)
      rw [h] at this
      norm_num at this
    · rw [Nat.primeFactors_prime_pow hE Nat.prime_two]
      simp
    · rw [Nat.primeFactors_prime_pow hE Nat.prime_two]
      simp
  refine ⟨hpos, ?_⟩
  rw [hg, hg2, Nat.totient_prime (by norm_num)]
  norm_num

theorem a070814_of_term {x : ℕ} (h : IsTerm x) :
    ∃ k f, (f = 1 ∨ f = 3 ∨ f = 5 ∨ f = 15) ∧ x = 17 * 2 ^ k * f := by
  obtain ⟨hx0, heq⟩ := h
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp [gpf] at heq
  have hx2 : 2 ≤ x := by omega
  have hpmem := a070814_gpf_mem hx2
  obtain ⟨hpp, hpx, -⟩ := Nat.mem_primeFactors.mp hpmem
  have hT0 : 0 < Nat.totient x := Nat.totient_pos.mpr hx0
  have hp1 : 1 ≤ gpf x := hpp.one_lt.le
  rw [Nat.totient_prime hpp] at heq
  push_cast [Nat.cast_sub hp1] at heq
  have hT1 : Nat.totient x ≠ 1 := by
    intro h1
    have hg1 : gpf 1 = 1 := by simp [gpf]
    rw [h1, hg1] at heq
    have h16 : gpf x = 16 := by omega
    rw [h16] at hpp
    norm_num at hpp
  have hT2 : 2 ≤ Nat.totient x := by omega
  have hqmem := a070814_gpf_mem hT2
  obtain ⟨hqp, hqT, -⟩ := Nat.mem_primeFactors.mp hqmem
  have hpq : gpf x = gpf (Nat.totient x) + 15 := by omega
  have hdvd : gpf x - 1 ∣ Nat.totient x := by
    have := Nat.totient_dvd_of_dvd hpx
    rwa [Nat.totient_prime hpp] at this
  have hpodd : Odd (gpf x) := hpp.odd_of_ne_two (by omega)
  have h2T : 2 ∣ Nat.totient x := by
    refine dvd_trans ?_ hdvd
    obtain ⟨r, hr⟩ := hpodd
    exact ⟨r, by omega⟩
  have hq2le : 2 ≤ gpf (Nat.totient x) :=
    a070814_gpf_le hT1 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2T, by omega⟩)
  have hqeven : Even (gpf (Nat.totient x)) := by
    obtain ⟨r, hr⟩ := hpodd
    exact ⟨r - 7, by omega⟩
  have hq2 : gpf (Nat.totient x) = 2 := (Nat.Prime.even_iff hqp).mp hqeven
  have hp17 : gpf x = 17 := by omega
  have hsmall : ∀ r, r.Prime → r ∣ Nat.totient x → r ≤ 2 := by
    intro r hr hrd
    rw [← hq2]
    exact a070814_gpf_le hT1 (Nat.mem_primeFactors.mpr ⟨hr, hrd, by omega⟩)
  have hle17 : ∀ r, r.Prime → r ∣ x → r ≤ 17 := by
    intro r hr hrd
    rw [← hp17]
    exact a070814_gpf_le hx1 (Nat.mem_primeFactors.mpr ⟨hr, hrd, by omega⟩)
  have hB : ∀ r, r.Prime → r ∣ x → ∀ s, s.Prime → s ∣ r - 1 → s ≤ 2 := by
    intro r hr hrd s hs hsd
    apply hsmall s hs
    refine dvd_trans hsd ?_
    have := Nat.totient_dvd_of_dvd hrd
    rwa [Nat.totient_prime hr] at this
  have hC : ∀ r, r.Prime → r * r ∣ x → r ≤ 2 := by
    intro r hr hrd
    apply hsmall r hr
    have := Nat.totient_dvd_of_dvd hrd
    have e : r * r = r ^ (1 + 1) := by ring
    rw [e, Nat.totient_prime_pow_succ hr] at this
    exact dvd_trans (Dvd.intro (r - 1) (by ring)) this
  obtain ⟨k, m, hmodd, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : x ≠ 0)
  have h17x : 17 ∣ x := hp17 ▸ hpx
  have h17m : 17 ∣ m := by
    rw [hxm] at h17x
    exact (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 17 2)).dvd_of_dvd_mul_left h17x
  obtain ⟨f, rfl⟩ := h17m
  have hfx : f ∣ x := ⟨2 ^ k * 17, by rw [hxm]; ring⟩
  have hfodd : Odd f := (Nat.odd_mul.mp hmodd).2
  have hpf : ∀ r, r.Prime → r ∣ f → r = 3 ∨ r = 5 := by
    intro r hr hrf
    have hrx : r ∣ x := dvd_trans hrf hfx
    have hr17 := hle17 r hr hrx
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hfodd) (even_iff_two_dvd.mpr hrf)
    have hr17' : r ≠ 17 := by
      rintro rfl
      have h1 : 17 * 17 ∣ 17 * f := Nat.mul_dvd_mul_left 17 hrf
      have h2 : 17 * f ∣ x := ⟨2 ^ k, by rw [hxm]; ring⟩
      have := hC 17 (by norm_num) (dvd_trans h1 h2)
      omega
    have h7 : r ≠ 7 := by
      rintro rfl
      have := hB 7 (by norm_num) hrx 3 (by norm_num) (by norm_num)
      omega
    have h11 : r ≠ 11 := by
      rintro rfl
      have := hB 11 (by norm_num) hrx 5 (by norm_num) (by norm_num)
      omega
    have h13 : r ≠ 13 := by
      rintro rfl
      have := hB 13 (by norm_num) hrx 3 (by norm_num) (by norm_num)
      omega
    interval_cases r <;> first | (left; rfl) | (right; rfl) | omega | (exfalso; norm_num at hr)
  have hsq : Squarefree f := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro r hr hrr
    have hrf : r ∣ f := dvd_trans (Dvd.intro _ rfl) hrr
    have := hC r (hr) (dvd_trans hrr hfx)
    rcases hpf r (hr) hrf with rfl | rfl <;> omega
  have hf15 : f ∣ 15 := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    have hsub : f.primeFactors ⊆ {3, 5} := by
      intro r hr
      obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.mp hr
      rcases hpf r hrp hrd with rfl | rfl <;> simp
    have := Finset.prod_dvd_prod_of_subset _ _ (fun i => i) hsub
    simpa using this
  have hfle : f ≤ 15 := Nat.le_of_dvd (by norm_num) hf15
  suffices hf : f = 1 ∨ f = 3 ∨ f = 5 ∨ f = 15 from ⟨k, f, hf, by rw [hxm]; ring⟩
  interval_cases f <;>
    first
    | (left; rfl)
    | (right; left; rfl)
    | (right; right; left; rfl)
    | (right; right; right; rfl)
    | (exfalso; norm_num at hf15)

def a070814_c (r : ℕ) : ℕ := if r = 0 then 8 else if r = 1 then 10 else if r = 2 then 12 else 15

def a070814_g (j : ℕ) : ℕ :=
  if j < 6 then 17 * (j + 1) else 17 * 2 ^ ((j - 6) / 4) * a070814_c ((j - 6) % 4)

theorem a070814_g_big (m : ℕ) : a070814_g (m + 6) = 17 * 2 ^ (m / 4) * a070814_c (m % 4) := by
  unfold a070814_g
  rw [if_neg (by omega)]
  simp

theorem a070814_g_shift (m : ℕ) : a070814_g (m + 10) = 2 * a070814_g (m + 6) := by
  have e : m + 10 = (m + 4) + 6 := by ring
  rw [e, a070814_g_big, a070814_g_big]
  have h1 : (m + 4) / 4 = m / 4 + 1 := by omega
  have h2 : (m + 4) % 4 = m % 4 := by omega
  rw [h1, h2, pow_succ]
  ring

theorem a070814_g_mono : StrictMono a070814_g := by
  apply strictMono_nat_of_lt_succ
  intro j
  by_cases hj : j < 5
  · unfold a070814_g
    rw [if_pos (by omega), if_pos (by omega)]
    omega
  by_cases hj5 : j = 5
  · subst hj5
    norm_num [a070814_g, a070814_c]
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 6 := ⟨j - 6, by omega⟩
  rw [show m + 6 + 1 = (m + 1) + 6 by ring, a070814_g_big, a070814_g_big]
  have hpos : 0 < 2 ^ (m / 4) := by positivity
  rcases (by omega : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3) with h | h | h | h
  · have e1 : (m + 1) / 4 = m / 4 := by omega
    have e2 : (m + 1) % 4 = 1 := by omega
    rw [e1, e2, h]
    simp only [a070814_c]
    norm_num
  · have e1 : (m + 1) / 4 = m / 4 := by omega
    have e2 : (m + 1) % 4 = 2 := by omega
    rw [e1, e2, h]
    simp only [a070814_c]
    norm_num
  · have e1 : (m + 1) / 4 = m / 4 := by omega
    have e2 : (m + 1) % 4 = 3 := by omega
    rw [e1, e2, h]
    simp only [a070814_c]
    norm_num
  · have e1 : (m + 1) / 4 = m / 4 + 1 := by omega
    have e2 : (m + 1) % 4 = 0 := by omega
    rw [e1, e2, h, pow_succ]
    simp only [a070814_c]
    norm_num
    omega

theorem a070814_term_iff (x : ℕ) : IsTerm x ↔ ∃ j, a070814_g j = x := by
  constructor
  · intro h
    obtain ⟨k, f, hf, rfl⟩ := a070814_of_term h
    rcases hf with rfl | rfl | rfl | rfl
    · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | rfl | hk
      · exact ⟨0, by norm_num [a070814_g]⟩
      · exact ⟨1, by norm_num [a070814_g]⟩
      · exact ⟨3, by norm_num [a070814_g]⟩
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
        refine ⟨4 * k' + 6, ?_⟩
        rw [a070814_g_big]
        have e1 : 4 * k' / 4 = k' := by omega
        have e2 : 4 * k' % 4 = 0 := by omega
        rw [e1, e2]
        simp only [a070814_c, if_pos]
        ring
    · rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | hk
      · exact ⟨2, by norm_num [a070814_g]⟩
      · exact ⟨5, by norm_num [a070814_g]⟩
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
        refine ⟨(4 * k' + 2) + 6, ?_⟩
        rw [a070814_g_big]
        have e1 : (4 * k' + 2) / 4 = k' := by omega
        have e2 : (4 * k' + 2) % 4 = 2 := by omega
        rw [e1, e2]
        simp only [a070814_c]
        norm_num
        ring
    · rcases (by omega : k = 0 ∨ 1 ≤ k) with rfl | hk
      · exact ⟨4, by norm_num [a070814_g]⟩
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        refine ⟨(4 * k' + 1) + 6, ?_⟩
        rw [a070814_g_big]
        have e1 : (4 * k' + 1) / 4 = k' := by omega
        have e2 : (4 * k' + 1) % 4 = 1 := by omega
        rw [e1, e2]
        simp only [a070814_c]
        norm_num
        ring
    · refine ⟨(4 * k + 3) + 6, ?_⟩
      rw [a070814_g_big]
      have e1 : (4 * k + 3) / 4 = k := by omega
      have e2 : (4 * k + 3) % 4 = 3 := by omega
      rw [e1, e2]
      simp only [a070814_c]
      norm_num
  · rintro ⟨j, rfl⟩
    by_cases hj : j < 6
    · interval_cases j
      · have e : a070814_g 0 = 17 * 2 ^ 0 * 1 := by norm_num [a070814_g]
        rw [e]; exact a070814_term_of 0 1 (by simp)
      · have e : a070814_g 1 = 17 * 2 ^ 1 * 1 := by norm_num [a070814_g]
        rw [e]; exact a070814_term_of 1 1 (by simp)
      · have e : a070814_g 2 = 17 * 2 ^ 0 * 3 := by norm_num [a070814_g]
        rw [e]; exact a070814_term_of 0 3 (by simp)
      · have e : a070814_g 3 = 17 * 2 ^ 2 * 1 := by norm_num [a070814_g]
        rw [e]; exact a070814_term_of 2 1 (by simp)
      · have e : a070814_g 4 = 17 * 2 ^ 0 * 5 := by norm_num [a070814_g]
        rw [e]; exact a070814_term_of 0 5 (by simp)
      · have e : a070814_g 5 = 17 * 2 ^ 1 * 3 := by norm_num [a070814_g]
        rw [e]; exact a070814_term_of 1 3 (by simp)
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 6 := ⟨j - 6, by omega⟩
      rw [a070814_g_big]
      rcases (by omega : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3) with h | h | h | h
      · have e : 17 * 2 ^ (m / 4) * a070814_c (m % 4) = 17 * 2 ^ (m / 4 + 3) * 1 := by
          rw [h, pow_add]; simp only [a070814_c]; norm_num; ring
        rw [e]; exact a070814_term_of _ 1 (by simp)
      · have e : 17 * 2 ^ (m / 4) * a070814_c (m % 4) = 17 * 2 ^ (m / 4 + 1) * 5 := by
          rw [h, pow_add]; simp only [a070814_c]; norm_num; ring
        rw [e]; exact a070814_term_of _ 5 (by simp)
      · have e : 17 * 2 ^ (m / 4) * a070814_c (m % 4) = 17 * 2 ^ (m / 4 + 2) * 3 := by
          rw [h, pow_add]; simp only [a070814_c]; norm_num; ring
        rw [e]; exact a070814_term_of _ 3 (by simp)
      · have e : 17 * 2 ^ (m / 4) * a070814_c (m % 4) = 17 * 2 ^ (m / 4) * 15 := by
          rw [h]; simp only [a070814_c]; norm_num
        rw [e]; exact a070814_term_of _ 15 (by simp)

theorem a070814_infinite : (Set.ofPred IsTerm).Infinite :=
  Set.infinite_of_injective_forall_mem a070814_g_mono.injective
    (fun j => (a070814_term_iff _).mpr ⟨j, rfl⟩)

theorem a070814_nth (j : ℕ) : Nat.nth IsTerm j = a070814_g j := by
  have hS : ∀ n, n ∈ {n : ℕ | ∀ hf : (Set.ofPred IsTerm).Finite, n < hf.toFinset.card} :=
    fun n hf => absurd hf a070814_infinite
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn a070814_g ?_ ?_ ?_ (hS j)).symm
  · intro x hx
    obtain ⟨i, hi⟩ := (a070814_term_iff x).mp hx
    exact ⟨i, hS i, hi⟩
  · intro i _
    exact (a070814_term_iff _).mpr ⟨i, rfl⟩
  · exact a070814_g_mono.strictMonoOn _

theorem a070814_main : ∀ n : ℕ, 10 < n → a n = 2 * a (n - 4) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
  unfold a
  rw [show m + 11 - 1 = m + 10 by omega, show m + 11 - 4 - 1 = m + 6 by omega, a070814_nth,
    a070814_nth, a070814_g_shift]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a070814.main := OMA.Helpers.a070814_main
