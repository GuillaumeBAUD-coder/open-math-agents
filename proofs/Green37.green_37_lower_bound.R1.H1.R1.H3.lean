import OMAReductions.R_Green37_green_37_lower_bound_R1_H1_R1

-- Step Green37.green_37_lower_bound.R1.H1.R1.H3: hypothesis H3 of reduction Green37.green_37_lower_bound.R1.H1.R1
-- Credit: @anmolspace
-- Proof: a cover for N2 is a cover for N1 <= N2 (covers exist), so m is monotone in N;
-- the second part is Bertrand's postulate applied to N / 2.

namespace OMA.SG37H1H3

lemma apcard (a d k : ℕ) (hd : 0 < d) :
    ENat.card ({a + n • d | (n : ℕ) (_ : n < ((k : ℕ) : ℕ∞))} : Set ℕ) = k := by
  have hinj : Function.Injective (fun n : ℕ => a + n * d) := by
    intro x y h
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)
  have e : ({a + n • d | (n : ℕ) (_ : n < ((k : ℕ) : ℕ∞))} : Set ℕ)
      = (((Finset.range k).image (fun n : ℕ => a + n * d) : Finset ℕ) : Set ℕ) := by
    ext x
    simp [smul_eq_mul]
  rw [e]
  change (((Finset.range k).image (fun n : ℕ => a + n * d) : Finset ℕ) : Set ℕ).encard = k
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj, Finset.card_range]

lemma cover_nonempty (N k : ℕ) :
    {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k}.Nonempty := by
  refine ⟨_, Finset.range (k * N + 1), rfl, ?_⟩
  intro d hd
  unfold Set.ContainsAP
  refine ⟨0, {0 + n • d | (n : ℕ) (_ : n < ((k : ℕ) : ℕ∞))}, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := hx
    have hn' : n < k := by exact_mod_cast hn
    have hle : n * d ≤ k * N := Nat.mul_le_mul (le_of_lt hn') hd.2
    rw [Finset.mem_coe, Finset.mem_range, smul_eq_mul, zero_add]
    exact Nat.lt_succ_of_le hle
  · unfold Set.IsAPOfLengthWith
    exact ⟨apcard 0 d k (by omega), rfl⟩

theorem part1 : ∀ N₁ N₂ k : ℕ, N₁ ≤ N₂ → Green37.m N₁ k ≤ Green37.m N₂ k := by
  intro N1 N2 k hN
  unfold Green37.m
  apply Nat.sInf_le
  obtain ⟨A, hA, hcov⟩ := Nat.sInf_mem (cover_nonempty N2 k)
  exact ⟨A, hA, fun d hd => hcov d ⟨hd.1, le_trans hd.2 hN⟩⟩

theorem part2 : ∀ N : ℕ, 2 ≤ N → ∃ p : ℕ, Nat.Prime p ∧ N ≤ 2 * p ∧ p ≤ N := by
  intro N hN
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 2) (by omega)
  exact ⟨p, hp, by omega, by omega⟩

end OMA.SG37H1H3

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1_H1_R1.H3 :=
  ⟨OMA.SG37H1H3.part1, OMA.SG37H1H3.part2⟩
