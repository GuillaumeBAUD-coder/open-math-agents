import OMAReductions.R_Oppermann_oppermann_conjecture_ferreira_large_x_R1

-- Step Oppermann.oppermann_conjecture.ferreira_large_x.R1.H2
-- Credit: @caa1982

private lemma exists_prime_in_interval {N M x : ℕ}
    (hgap : ∀ n ≥ N, ((n + 1).nth Nat.Prime : ℝ) - (n.nth Nat.Prime : ℝ) <
      Real.sqrt (n.nth Nat.Prime))
    (hM : N.nth Nat.Prime < M) (hMx : M ≤ x ^ 2) :
    ∃ p ∈ Finset.Ioo M (M + x), p.Prime := by
  classical
  have hex : ∃ k : ℕ, M < k.nth Nat.Prime := by
    obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + 1)
    exact ⟨Nat.count Nat.Prime p, by rw [Nat.nth_count hp]; omega⟩
  let k := Nat.find hex
  have hk_gt : M < k.nth Nat.Prime := Nat.find_spec hex
  have hk_pos : 0 < k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0, Nat.nth_prime_zero_eq_two] at hk_gt
    have hpN : 2 ≤ N.nth Nat.Prime := (Nat.prime_nth_prime N).two_le
    omega
  let n := k - 1
  have hn_succ : n + 1 = k := by omega
  have hn_le : n.nth Nat.Prime ≤ M := by
    by_contra! hgt
    have := Nat.find_min hex (show n < k by omega)
    exact this hgt
  have hNn : N ≤ n := by
    by_contra! hlt
    have hkN : k ≤ N := by omega
    have hmono : k.nth Nat.Prime ≤ N.nth Nat.Prime :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hkN
    omega
  have hstep := hgap n hNn
  rw [hn_succ] at hstep
  have hsqrt_le : Real.sqrt (n.nth Nat.Prime : ℝ) ≤ (x : ℝ) := by
    have hle : (n.nth Nat.Prime : ℝ) ≤ (x : ℝ) ^ 2 := by
      have : n.nth Nat.Prime ≤ x ^ 2 := le_trans hn_le hMx
      exact_mod_cast this
    rw [← Real.sqrt_sq (Nat.cast_nonneg x)]
    exact Real.sqrt_le_sqrt hle
  have hk_lt : (k.nth Nat.Prime : ℝ) < (M : ℝ) + (x : ℝ) := by
    have hn_le' : (n.nth Nat.Prime : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn_le
    linarith
  have hk_lt_nat : k.nth Nat.Prime < M + x := by exact_mod_cast hk_lt
  exact ⟨k.nth Nat.Prime, Finset.mem_Ioo.mpr ⟨hk_gt, hk_lt_nat⟩, Nat.prime_nth_prime k⟩

theorem OMA.solution : OMA.R_Oppermann_oppermann_conjecture_ferreira_large_x_R1.H2 := by
  intro N hgap x hx
  have hx2 : 2 ≤ x := by
    have hp2 : 2 ≤ N.nth Nat.Prime := (Nat.prime_nth_prime N).two_le
    by_contra hlt
    interval_cases x <;> omega
  constructor
  · have h1 : x * (x - 1) + x = x ^ 2 := by
      cases x with
      | zero => omega
      | succ m => simp only [Nat.add_sub_cancel]; ring
    rw [← h1]
    exact exists_prime_in_interval hgap hx (by omega)
  · have h2 : x ^ 2 + x = x * (x + 1) := by ring
    have hM : N.nth Nat.Prime < x ^ 2 := by
      have : x * (x - 1) ≤ x ^ 2 := by
        cases x with
        | zero => omega
        | succ m => simp only [Nat.add_sub_cancel]; nlinarith
      omega
    rw [← h2]
    exact exists_prime_in_interval hgap hM le_rfl
