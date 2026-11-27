import OMAStatements.S_oeis_a001045

-- Problem: A001045, Fossaceca's and Copeland's conjectures for the Jacobsthal numbers.
-- Credit: @ShoQo
-- Proof: 3 a(n) = 2^n - (-1)^n. Fossaceca: the multiples of 3 in (2^n, 2^(n+1)] number
-- 2^(n+1)/3 - 2^n/3, evaluated by the residue of 2^n mod 3. Copeland: by induction,
-- A^n = a(n) J + (-1)^n I, using a(n+1) = 2 a(n) + (-1)^n.

open OMA.S_oeis_a001045

namespace OMA_A001045_Proof

lemma three_a (n : ℕ) : 3 * a n = 2 ^ n - (-1) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [a]
    | 1, _ => simp [a]
    | (m + 2), ih =>
      simp only [a]
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      rw [pow_succ, pow_succ, pow_succ (-1 : ℤ), pow_succ (-1 : ℤ)] at *
      linarith

lemma a_succ (n : ℕ) : a (n + 1) = 2 * a n + (-1) ^ n := by
  have h1 := three_a (n + 1); have h0 := three_a n
  rw [pow_succ, pow_succ (-1 : ℤ)] at h1
  linarith

lemma A_pow (n : ℕ) : A ^ n = Matrix.of fun i j => if i = j then a n + (-1) ^ n else a n := by
  induction n with
  | zero => ext i j; simp [a, Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ, ih, a_succ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, A, pow_succ] <;> ring

end OMA_A001045_Proof

open OMA_A001045_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a001045.main := by
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · -- count multiples of 3 in (2^n, 2^(n+1)) as 2^(n+1)/3 - 2^n/3
    have hndvd : ∀ k : ℕ, ¬ 3 ∣ 2 ^ k := fun k h =>
      absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
    have hIoo : (Finset.Ioo (2 ^ n) (2 ^ (n + 1))).filter (fun m => 3 ∣ m)
        = (Finset.Ioc (2 ^ n) (2 ^ (n + 1))).filter (fun m => 3 ∣ m) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2.le⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, lt_of_le_of_ne h2 ?_⟩, h3⟩
        rintro rfl; exact hndvd _ h3
    have hsplit : ((Finset.Ioc 0 (2 ^ (n + 1))).filter (fun m => 3 ∣ m)).card
        = ((Finset.Ioc 0 (2 ^ n)).filter (fun m => 3 ∣ m)).card
          + ((Finset.Ioc (2 ^ n) (2 ^ (n + 1))).filter (fun m => 3 ∣ m)).card := by
      rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (Nat.pow_le_pow_right (show 2 > 0 by norm_num) (Nat.le_succ n)),
        Finset.filter_union, Finset.card_union_of_disjoint]
      exact Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)
    rw [hIoo]
    rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at hsplit
    have h3a := three_a n
    have hq := Nat.div_add_mod (2 ^ n) 3
    have hq' := Nat.div_add_mod (2 ^ (n + 1)) 3
    have hr := Nat.mod_lt (2 ^ n) (show 3 > 0 by norm_num)
    have hr' := Nat.mod_lt (2 ^ (n + 1)) (show 3 > 0 by norm_num)
    have hr0 : 2 ^ n % 3 ≠ 0 := fun h => hndvd n (Nat.dvd_of_mod_eq_zero h)
    have hr0' : 2 ^ (n + 1) % 3 ≠ 0 := fun h => hndvd (n + 1) (Nat.dvd_of_mod_eq_zero h)
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow] at h3a
      zify at *
      generalize (2 : ℤ) ^ n = P at *
      generalize (2 : ℤ) ^ (n + 1) = P' at *
      omega
    · rw [ho.neg_one_pow] at h3a
      zify at *
      generalize (2 : ℤ) ^ n = P at *
      generalize (2 : ℤ) ^ (n + 1) = P' at *
      omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [A_pow]
    refine ⟨?_, fun i j hij => by simp [hij], fun i => ?_⟩
    · simp [Matrix.trace, a_succ, pow_succ]; ring
    · simp only [Matrix.of_apply, if_true]
      split_ifs with h
      · rw [h.neg_one_pow]
      · rw [(Nat.not_even_iff_odd.mp h).neg_one_pow]; ring

