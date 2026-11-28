import OMAReductions.R_Erdos881_erdos_881_R1

/-! An asymptotic additive basis of order k has all but finitely many naturals in k • A.
For k = 0, 0 • A = {0}, so there is none. For k = 1, A contains every n ≥ N. Take B to be the
multiples of 3 in A, an infinite subset. Every n ≥ 2N + 6 is a + b with a, b ≥ N and
a, b ≢ 0 (mod 3): a ∈ [N + 1, N + 5] in a residue class chosen from n mod 3. So A \ B is an
asymptotic basis of order 2. -/

open scoped Pointwise in
theorem OMA.solution : OMA.R_Erdos881_erdos_881_R1.H1 := by
  intro k A hmin hk
  obtain ⟨hbasis, -⟩ := hmin
  interval_cases k
  · exfalso
    unfold Set.IsAsymptoticAddBasisOfOrder at hbasis
    rw [zero_nsmul, Nat.cofinite_eq_atTop, Filter.eventually_atTop] at hbasis
    obtain ⟨N, hN⟩ := hbasis
    have h := hN (N + 1) (by omega)
    simp at h
  · unfold Set.IsAsymptoticAddBasisOfOrder at hbasis ⊢
    rw [one_nsmul, Nat.cofinite_eq_atTop, Filter.eventually_atTop] at hbasis
    obtain ⟨N, hN⟩ := hbasis
    refine ⟨{n ∈ A | n % 3 = 0}, fun n hn => hn.1, ?_, ?_⟩
    · apply Set.infinite_of_not_bddAbove
      rintro ⟨M, hM⟩
      have hmem : 3 * (M + N + 1) ∈ {n ∈ A | n % 3 = 0} :=
        Set.mem_sep_iff.2 ⟨hN _ (by omega), by omega⟩
      have := hM hmem
      omega
    · rw [show (1 : ℕ) + 1 = 2 from rfl, two_nsmul, Nat.cofinite_eq_atTop,
        Filter.eventually_atTop]
      refine ⟨2 * N + 6, fun n hn => ?_⟩
      rw [Set.mem_add]
      have good : ∀ x, N ≤ x → x % 3 ≠ 0 → x ∈ A \ {n ∈ A | n % 3 = 0} := by
        intro x hx h3
        exact Set.mem_diff_of_mem (hN x hx) (fun h => h3 (Set.mem_sep_iff.1 h).2)
      have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h3 with h | h | h
      · exact ⟨3 * (N / 3 + 1) + 1, good _ (by omega) (by omega),
          n - (3 * (N / 3 + 1) + 1), good _ (by omega) (by omega), by omega⟩
      · exact ⟨3 * (N / 3 + 1) + 2, good _ (by omega) (by omega),
          n - (3 * (N / 3 + 1) + 2), good _ (by omega) (by omega), by omega⟩
      · exact ⟨3 * (N / 3 + 1) + 1, good _ (by omega) (by omega),
          n - (3 * (N / 3 + 1) + 1), good _ (by omega) (by omega), by omega⟩
