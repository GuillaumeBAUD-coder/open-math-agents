import OMAReductions.R_Erdos436_erdos_436_variants_ge_four_R1

-- Step Erdos436.erdos_436.variants.ge_four.R1.H1: hypothesis H1 of reduction Erdos436.erdos_436.variants.ge_four.R1
-- Credit: @koolkao
-- Original proof: choose p ≡ 1 + 4P (mod 8P), P the product of the odd numbers up to M (Dirichlet),
-- so p ≡ 5 (mod 8) makes 2 a non-residue, and p ≡ 1 (mod q), p ≡ 1 (mod 4) make every odd prime
-- q ≤ M a residue by quadratic reciprocity.

namespace OMA436H1


/-- The product of the odd numbers up to `M`. -/
lemma oddProd_odd (M : ℕ) : Odd (∏ i ∈ (Finset.range (M + 1)).filter Odd, i) := by
  apply Finset.prod_induction _ Odd
  · intro a b ha hb
    exact Nat.odd_mul.mpr ⟨ha, hb⟩
  · exact odd_one
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

lemma dvd_oddProd {M q : ℕ} (hq : Odd q) (hqM : q ≤ M) :
    q ∣ ∏ i ∈ (Finset.range (M + 1)).filter Odd, i := by
  apply Finset.dvd_prod_of_mem
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hq⟩


end OMA436H1

open OMA436H1 in
theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_ge_four_R1.H1 := by
  intro M B
  set P := ∏ i ∈ (Finset.range (M + 1)).filter Odd, i with hPdef
  have hPodd : Odd P := oddProd_odd M
  obtain ⟨t, ht⟩ := hPodd
  have hcop : Nat.Coprime (1 + 4 * P) (8 * P) := by
    apply Nat.Coprime.mul_right
    · have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
      rw [h8]
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_two_right]
      exact ⟨2 * P, by ring⟩
    · have := (Nat.coprime_add_mul_right_left 1 P 4).mpr (Nat.coprime_one_left P)
      simpa [mul_comm] using this
  obtain ⟨p, hpgt, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B M) (by omega : 8 * P ≠ 0) hcop
  have hpB : p > B := lt_of_le_of_lt (le_max_left _ _) hpgt
  have hpM : M < p := lt_of_le_of_lt (le_max_right _ _) hpgt
  have hp8 : p % 8 = 5 := by
    have h := Nat.ModEq.of_mul_right P hpmod
    unfold Nat.ModEq at h
    rw [h, ht]
    omega
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hpB, hp, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    have hne : p ≠ 2 := by omega
    have hsq : IsSquare (2 : ZMod p) := ⟨x, by rw [← hx, sq]⟩
    rcases (ZMod.exists_sq_eq_two_iff hne).mp hsq with h | h <;> omega
  · intro q hq hqodd hqM
    have : Fact q.Prime := ⟨hq⟩
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hqodd) even_two
    have hp4 : p % 4 = 1 := by omega
    have hpq : p % q = 1 := by
      have hdvd : q ∣ P := dvd_oddProd hqodd hqM
      have h := Nat.ModEq.of_dvd (Dvd.dvd.mul_left hdvd 8) hpmod
      obtain ⟨c, hc⟩ := hdvd
      unfold Nat.ModEq at h
      rw [h, hc]
      have hq1 : 1 < q := hq.one_lt
      rw [show 1 + 4 * (q * c) = 1 + q * (4 * c) by ring, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hq1
    have hsq : IsSquare ((p : ℕ) : ZMod q) := by
      have : ((p : ℕ) : ZMod q) = 1 := by
        rw [← ZMod.natCast_mod, hpq, Nat.cast_one]
      rw [this]
      exact ⟨1, by ring⟩
    obtain ⟨x, hx⟩ := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hp4 hq2).mpr hsq
    exact ⟨x, by rw [hx, sq]⟩
