import FormalConjectures.ErdosProblems.«939»

/-!
The [Erdős Problem 939 discussion](https://www.erdosproblems.com/forum/thread/939)
uses the odd terms of `(x + y)^8 - (x - y)^8`. Here `x = 1681^8` and
`y = 1680^8`. Splitting the coefficient 112 of `x^5 * y^3` into 42 and 70
gives six distinct summands including `(x - y)^8`.
-/

lemma OMA.full_mul_pow_of_dvd {k a b : ℕ} (hab : a ∣ b) : k.Full (a * b ^ k) := by
  intro p hp
  obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hp
  have hb : p ∣ b := (hprime.dvd_mul.mp hdiv).elim
    (fun ha ↦ ha.trans hab) hprime.dvd_of_dvd_pow
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hb k) a

theorem OMA.solution : type_of% @Erdos939.erdos_939.variants.eight := by
  let a := (1681 ^ 8 - 1680 ^ 8 : ℕ) ^ 8
  let b := 16 * (1681 ^ 7 * 1680 : ℕ) ^ 8
  let c := 42 * (1681 ^ 5 * 1680 ^ 3 : ℕ) ^ 8
  let d := 70 * (1681 ^ 5 * 1680 ^ 3 : ℕ) ^ 8
  let e := 112 * (1681 ^ 3 * 1680 ^ 5 : ℕ) ^ 8
  let f := 16 * (1681 * 1680 ^ 7 : ℕ) ^ 8
  let s : Finset ℕ := {a, b, c, d, e, f}
  have ha : a ∉ ({b, c, d, e, f} : Finset ℕ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton, a, b, c, d, e, f]
  have hb : b ∉ ({c, d, e, f} : Finset ℕ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton, b, c, d, e, f]
  have hc : c ∉ ({d, e, f} : Finset ℕ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton, c, d, e, f]
  have hd : d ∉ ({e, f} : Finset ℕ) := by
    norm_num [Finset.mem_insert, Finset.mem_singleton, d, e, f]
  have he : e ∉ ({f} : Finset ℕ) := by
    norm_num [e, f]
  refine ⟨s, ?_⟩
  change s.card = 8 - 2 ∧ s.Coprime ∧ (8 : ℕ).Full (∑ n ∈ s, n) ∧
    ∀ n ∈ s, 0 < n ∧ (8 : ℕ).Full n
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [s, Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb,
      Finset.card_insert_of_notMem hc, Finset.card_insert_of_notMem hd,
      Finset.card_insert_of_notMem he, Finset.card_singleton]
  · have hgcd : Nat.gcd a f = 1 := by norm_num [a, f]
    have hma : a ∈ s := Finset.mem_insert_self _ _
    have hmf : f ∈ s := by simp only [s, Finset.mem_insert, Finset.mem_singleton, eq_self, or_true]
    have hda : s.gcd id ∣ a := Finset.gcd_dvd hma
    have hdf : s.gcd id ∣ f := Finset.gcd_dvd hmf
    change s.gcd id = 1
    exact Nat.dvd_one.mp (hgcd ▸ Nat.dvd_gcd hda hdf)
  · have hsum : (∑ n ∈ s, n) = (1681 ^ 8 + 1680 ^ 8 : ℕ) ^ 8 := by
      simp only [s, Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_insert hc,
        Finset.sum_insert hd, Finset.sum_insert he, Finset.sum_singleton]
      norm_num [a, b, c, d, e, f]
    rw [hsum]
    simpa only [one_mul] using OMA.full_mul_pow_of_dvd (k := 8)
      (one_dvd (1681 ^ 8 + 1680 ^ 8 : ℕ))
  · intro n hn
    have hcases : n = a ∨ n = b ∨ n = c ∨ n = d ∨ n = e ∨ n = f := by
      simpa only [s, Finset.mem_insert, Finset.mem_singleton] using hn
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨by norm_num [a], ?_⟩
      simpa only [one_mul] using OMA.full_mul_pow_of_dvd (k := 8)
        (one_dvd (1681 ^ 8 - 1680 ^ 8 : ℕ))
    · exact ⟨by norm_num [b], OMA.full_mul_pow_of_dvd (by norm_num)⟩
    · exact ⟨by norm_num [c], OMA.full_mul_pow_of_dvd (by norm_num)⟩
    · exact ⟨by norm_num [d], OMA.full_mul_pow_of_dvd (by norm_num)⟩
    · exact ⟨by norm_num [e], OMA.full_mul_pow_of_dvd (by norm_num)⟩
    · exact ⟨by norm_num [f], OMA.full_mul_pow_of_dvd (by norm_num)⟩
