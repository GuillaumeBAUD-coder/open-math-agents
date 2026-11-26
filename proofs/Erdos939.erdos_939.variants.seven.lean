import FormalConjectures.ErdosProblems.«939»

/-!
The binomial construction from the [Erdős Problem 939 discussion](https://www.erdosproblems.com/forum/thread/939)
gives a witness from the odd terms of the expansion
`(x + y)^7 - (x - y)^7`, with `x = 211^7` and `y = 210^7`.
The base 210 contains every prime in the coefficients 14, 70, 42 and 2.
-/

lemma OMA.full_mul_pow_of_dvd {k a b : ℕ} (hab : a ∣ b) : k.Full (a * b ^ k) := by
  intro p hp
  obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hp
  have hb : p ∣ b := (hprime.dvd_mul.mp hdiv).elim
    (fun ha ↦ ha.trans hab) hprime.dvd_of_dvd_pow
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hb k) a

theorem OMA.solution : type_of% @Erdos939.erdos_939.variants.seven := by
  let a := (211 ^ 7 - 210 ^ 7 : ℕ) ^ 7
  let b := 14 * (211 ^ 6 * 210 : ℕ) ^ 7
  let c := 70 * (211 ^ 4 * 210 ^ 3 : ℕ) ^ 7
  let d := 42 * (211 ^ 2 * 210 ^ 5 : ℕ) ^ 7
  let e := 2 * (210 ^ 7 : ℕ) ^ 7
  let s : Finset ℕ := {a, b, c, d, e}
  have ha : a ∉ ({b, c, d, e} : Finset ℕ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton, a, b, c, d, e]
  have hb : b ∉ ({c, d, e} : Finset ℕ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton, b, c, d, e]
  have hc : c ∉ ({d, e} : Finset ℕ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton, c, d, e]
  have hd : d ∉ ({e} : Finset ℕ) := by
    norm_num [d, e]
  refine ⟨s, ?_⟩
  change s.card = 7 - 2 ∧ s.Coprime ∧ (7 : ℕ).Full (∑ n ∈ s, n) ∧
    ∀ n ∈ s, 0 < n ∧ (7 : ℕ).Full n
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [s, Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb,
      Finset.card_insert_of_notMem hc, Finset.card_insert_of_notMem hd, Finset.card_singleton]
  · have hgcd : Nat.gcd a e = 1 := by norm_num [a, e]
    have hma : a ∈ s := Finset.mem_insert_self _ _
    have hme : e ∈ s := by simp only [s, Finset.mem_insert, Finset.mem_singleton, eq_self, or_true]
    have hda : s.gcd id ∣ a := Finset.gcd_dvd hma
    have hde : s.gcd id ∣ e := Finset.gcd_dvd hme
    change s.gcd id = 1
    exact Nat.dvd_one.mp (hgcd ▸ Nat.dvd_gcd hda hde)
  · have hsum : (∑ n ∈ s, n) = (211 ^ 7 + 210 ^ 7 : ℕ) ^ 7 := by
      simp only [s, Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_insert hc,
        Finset.sum_insert hd, Finset.sum_singleton]
      norm_num [a, b, c, d, e]
    rw [hsum]
    simpa only [one_mul] using OMA.full_mul_pow_of_dvd (k := 7)
      (one_dvd (211 ^ 7 + 210 ^ 7 : ℕ))
  · intro n hn
    have hcases : n = a ∨ n = b ∨ n = c ∨ n = d ∨ n = e := by
      simpa only [s, Finset.mem_insert, Finset.mem_singleton] using hn
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · refine ⟨by norm_num [a], ?_⟩
      simpa only [one_mul] using OMA.full_mul_pow_of_dvd (k := 7)
        (one_dvd (211 ^ 7 - 210 ^ 7 : ℕ))
    · exact ⟨by norm_num [b], OMA.full_mul_pow_of_dvd (by norm_num)⟩
    · exact ⟨by norm_num [c], OMA.full_mul_pow_of_dvd (by norm_num)⟩
    · exact ⟨by norm_num [d], OMA.full_mul_pow_of_dvd (by norm_num)⟩
    · exact ⟨by norm_num [e], OMA.full_mul_pow_of_dvd (by norm_num)⟩
