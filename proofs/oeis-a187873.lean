import OMAStatements.S_oeis_a187873

lemma OMA.inf_a187873 (n : ℕ) : {p : ℕ | p.Prime ∧ n ^ 2 < p}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨m, hm⟩
  obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (m + n ^ 2 + 1)
  have := hm (show p ∈ {p : ℕ | p.Prime ∧ n ^ 2 < p} from ⟨hp2, by omega⟩)
  omega

lemma OMA.two_a187873 (n : ℕ) : n ^ 2 < Nat.nth (fun p => p.Prime ∧ n ^ 2 < p) 0 ∧
    Nat.nth (fun p => p.Prime ∧ n ^ 2 < p) 0 < OMA.S_oeis_a187873.a n ∧
    (Nat.nth (fun p => p.Prime ∧ n ^ 2 < p) 0).Prime ∧ (OMA.S_oeis_a187873.a n).Prime := by
  have hi := OMA.inf_a187873 n
  have h0 := Nat.nth_mem_of_infinite hi 0
  have h1 := Nat.nth_mem_of_infinite hi 1
  have hlt := Nat.nth_strictMono hi (show 0 < 1 by norm_num)
  exact ⟨h0.2, hlt, h0.1, h1.1⟩

lemma OMA.par_a187873 {p : ℕ} (hp : p.Prime) (h : 2 < p) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h2 | h2 <;> omega

theorem OMA.solution : type_of% @OMA.S_oeis_a187873.main := by
  have key : ∀ n : ℕ, 1 < n → n ^ 2 + 3 ≤ OMA.S_oeis_a187873.a n := by
    intro n hn
    obtain ⟨h0, h01, hp0, hp1⟩ := OMA.two_a187873 n
    by_contra hc
    have hn2 : 4 ≤ n ^ 2 := by nlinarith
    have e0 : Nat.nth (fun p => p.Prime ∧ n ^ 2 < p) 0 = n ^ 2 + 1 := by omega
    have e1 : OMA.S_oeis_a187873.a n = n ^ 2 + 2 := by omega
    rw [e0] at hp0; rw [e1] at hp1
    have := OMA.par_a187873 hp0 (by omega)
    have := OMA.par_a187873 hp1 (by omega)
    omega
  refine ⟨key, fun n hn => ⟨fun h => ?_, fun ⟨hq1, hq3⟩ => ?_⟩⟩
  · obtain ⟨h0, h01, hp0, hp1⟩ := OMA.two_a187873 n
    have hn2 : 4 ≤ n ^ 2 := by nlinarith
    rw [h] at hp1 h01
    have h3 := OMA.par_a187873 hp1 (by omega)
    refine ⟨?_, hp1⟩
    rcases (show Nat.nth (fun p => p.Prime ∧ n ^ 2 < p) 0 = n ^ 2 + 1 ∨
        Nat.nth (fun p => p.Prime ∧ n ^ 2 < p) 0 = n ^ 2 + 2 by omega) with e | e
    · rwa [e] at hp0
    · rw [e] at hp0
      have := OMA.par_a187873 hp0 (by omega)
      omega
  · have hn2 : 4 ≤ n ^ 2 := by nlinarith
    have h1 := OMA.par_a187873 hq1 (by omega)
    have h2 : ¬ (n ^ 2 + 2).Prime := fun h => by
      have := OMA.par_a187873 h (by omega)
      omega
    have hc : Nat.count (fun p => p.Prime ∧ n ^ 2 < p) (n ^ 2 + 3) = 1 := by
      have hz : Nat.count (fun p => p.Prime ∧ n ^ 2 < p) (n ^ 2 + 1) = 0 := by
        rw [Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x hx
        simp only [Finset.mem_range] at hx
        omega
      rw [show n ^ 2 + 3 = n ^ 2 + 1 + 1 + 1 by ring, Nat.count_succ, Nat.count_succ, hz]
      simp [hq1, h2]
    have := Nat.nth_count (p := fun p => p.Prime ∧ n ^ 2 < p) (n := n ^ 2 + 3) ⟨hq3, by omega⟩
    rw [hc] at this
    exact this
