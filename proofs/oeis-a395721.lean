import OMAStatements.S_oeis_a395721

open OMA.S_oeis_a395721 UniqueFactorizationMonoid

theorem OMA.solution : type_of% @OMA.S_oeis_a395721.main := by
  intro n _ hn
  have emptyOfOdd (m : ℕ) (hm : Odd m) : candidates m = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    have h := (Finset.mem_filter.mp hk).2
    obtain ⟨hkpos, hkdiv, hsucc⟩ := h
    have liftTwo (t : ℕ) (ht : t ≠ 0) (htwo : 2 ∣ t) : 2 ∣ radical t :=
      (dvd_radical_iff_of_irreducible (Nat.prime_iff.mp Nat.prime_two).irreducible ht).mpr htwo
    have parity : 2 ∣ k ∨ 2 ∣ (k + 1) := by omega
    have hEven : 2 ∣ m := parity.elim
      (fun he => (liftTwo k (by omega) he).trans hkdiv)
      (fun he => (liftTwo (k + 1) (by omega) he).trans hsucc)
    obtain ⟨q, hq⟩ := hm
    omega
  simp [a, emptyOfOdd _ hn]
