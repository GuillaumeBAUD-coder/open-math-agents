import OMAReductions.R_Erdos436_erdos_436_variants_ge_four_R1

-- Step Erdos436.erdos_436.variants.ge_four.R1.H1: hypothesis H1 of reduction Erdos436.erdos_436.variants.ge_four.R1

/-!
Let `P` be the product of the odd primes up to `M`. By Dirichlet's theorem there is a prime
`p > B` with `p ≡ 1 + 4 P (mod 8 P)`. Then `p ≡ 5 (mod 8)`, so `2` is not a square modulo `p`,
and `p ≡ 1 (mod q)` for every odd prime `q ≤ M`, so by quadratic reciprocity (`p ≡ 1 (mod 4)`)
each such `q` is a square modulo `p`.
-/

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_ge_four_R1.H1 := by
  unfold OMA.R_Erdos436_erdos_436_variants_ge_four_R1.H1
  intro M B
  have hPodd : Odd (∏ q ∈ (Finset.range (M + 1)).filter (fun q => q.Prime ∧ Odd q), q) :=
    Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one
      (fun q hq => (Finset.mem_filter.mp hq).2.2)
  have hdvd : ∀ q : ℕ, q.Prime → Odd q → q ≤ M →
      q ∣ ∏ q ∈ (Finset.range (M + 1)).filter (fun q => q.Prime ∧ Odd q), q := by
    intro q hq ho hM
    exact Finset.dvd_prod_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq, ho⟩)
  generalize (∏ q ∈ (Finset.range (M + 1)).filter (fun q => q.Prime ∧ Odd q), q) = P
    at hPodd hdvd
  have hP0 : P ≠ 0 := by
    intro h
    rw [h] at hPodd
    exact Nat.not_odd_zero hPodd
  have hcop : Nat.Coprime (1 + 4 * P) (8 * P) := by
    apply Nat.Coprime.mul_right
    · have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
      rw [h8]
      apply Nat.Coprime.pow_right
      exact Nat.coprime_two_right.mpr ⟨2 * P, by ring⟩
    · exact (Nat.coprime_add_mul_right_left 1 P 4).mpr (Nat.coprime_one_left P)
  obtain ⟨p, hpB, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (B + 2) (by omega : 8 * P ≠ 0) hcop
  haveI : Fact p.Prime := ⟨hp⟩
  have hp8 : p % 8 = 5 := by
    have h8 : p ≡ 1 + 4 * P [MOD 8] := Nat.ModEq.of_mul_right P hmod
    unfold Nat.ModEq at h8
    obtain ⟨t, ht⟩ := hPodd
    omega
  refine ⟨p, by omega, hp, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    have hsq : IsSquare (2 : ZMod p) := ⟨x, by rw [← hx, sq]⟩
    rcases (ZMod.exists_sq_eq_two_iff (by omega)).mp hsq with h | h <;> omega
  · intro q hq ho hM
    haveI : Fact q.Prime := ⟨hq⟩
    have hqP := hdvd q hq ho hM
    have e1 : ((p : ℕ) : ZMod q) = ((1 + 4 * P : ℕ) : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hmod.of_dvd (Dvd.dvd.mul_left hqP 8))
    have e2 : ((P : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff P q).mpr hqP
    have e3 : ((p : ℕ) : ZMod q) = 1 := by
      rw [e1]
      push_cast
      rw [e2]
      ring
    have hsq : IsSquare ((p : ℕ) : ZMod q) := by
      rw [e3]
      exact ⟨1, by ring⟩
    have hq2 : q ≠ 2 := by
      intro h
      rw [h] at ho
      exact (by decide : ¬ Odd 2) ho
    obtain ⟨r, hr⟩ :=
      (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (by omega : p % 4 = 1) hq2).mpr hsq
    exact ⟨r, by rw [sq, ← hr]⟩
