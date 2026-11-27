import OMAStatements.S_oeis_a330904

/-!
Thomas König's no-five conjecture, https://oeis.org/A330904.
Formal statement by @sturdy4days. Proof by @ptlom with OpenAI Codex.
@anmolspace previously recorded the parity obstruction and reported a
checked proof in the public desk notes. Here we use three half-indices.
-/
open OMA.S_oeis_a330904

private theorem trits_parity (n : ℕ) :
    balancedTernaryDigitSum n % 2 = (n : ℤ) % 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [balancedTernaryDigitSum]
    split
    · rfl
    · split
      · have := ih (n / 3 + 1) (by omega)
        omega
      · have := ih (n / 3) (by omega)
        omega

private abbrev ones (n : ℕ) := (Nat.digits 2 n).count 1

private theorem binary_step (n : ℕ) : ones n = ones (n / 2) + n % 2 := by
  by_cases hz : n = 0
  · simp [hz]
  · unfold ones
    rw [Nat.digits_eq_cons_digits_div (by decide) hz]
    by_cases h : n % 2 = 0
    · simp [h]
    · have h' : n % 2 = 1 := by omega
      simp [h']

private theorem even_half {n : ℕ} (h : MatchingDigitSums n) :
    ones (n / 2) % 2 = 0 := by
  change (ones n : ℤ) = balancedTernaryDigitSum n at h
  have ht := trits_parity n
  have hb := binary_step n
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a330904.main := by
  intro n h
  have allEven (i : Fin 5) := even_half (h i)
  let j := (n / 2 + 1) / 2
  have pick (m : ℕ) (hm : n / 2 ≤ m) (hm' : m ≤ n / 2 + 2) :
      ones m % 2 = 0 := by
    let i : Fin 5 := ⟨max n (2*m) - n, by omega⟩
    have hi : (n + i.val) / 2 = m := by dsimp [i]; omega
    simpa only [hi] using allEven i
  have he := pick (2*j) (by dsimp [j]; omega) (by dsimp [j]; omega)
  have ho := pick (2*j+1) (by dsimp [j]; omega) (by dsimp [j]; omega)
  have h0 := binary_step (2*j)
  have h1 := binary_step (2*j+1)
  have d0 : 2*j/2 = j := by omega
  have d1 : (2*j+1)/2 = j := by omega
  rw [d0] at h0
  rw [d1] at h1
  omega
