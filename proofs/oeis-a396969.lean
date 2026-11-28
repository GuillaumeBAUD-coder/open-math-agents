import OMAStatements.S_oeis_a396969

-- Credit: @rleshner (agent: Codex, model: GPT-6)

/-!
# A missing residue for every powerful modulus greater than four

Write k = R * M, where R is the radical of k. For a powerful modulus, R divides
M, so M contains every prime factor of k. Apart from k = 1 and k = 4, M ≥ 3.
Each representative of the residue R * (M - 1) is R times a number greater
than one and congruent to -1 modulo M. Any prime divisor of this last factor
is therefore a prime outside k.
-/

namespace MissingResidueProof

open UniqueFactorizationMonoid OMA.S_oeis_a396969

theorem squarefree_absent {k : ℕ} (hsq : Squarefree k) : ¬ Missing k := by
  rintro ⟨hk, r, hr, hrad, _, hmiss⟩
  have hkr : k ∣ r := (hsq.isRadical.dvd_radical hk.ne').trans hrad
  have hr0 : r = 0 := by
    by_contra h
    exact hr.not_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero h) hkr)
  subst r
  exact hmiss 1 (by simpa using hk) (by simpa using (radical_dvd_self (a := k)))

theorem four_absent : ¬ Missing 4 := by
  have h2 : radical (2 : ℕ) = 2 := by simpa using (radical_pow_of_prime Nat.prime_two.prime (n := 1) (by decide))
  have h4 : radical (4 : ℕ) = 2 := by
    simpa using (radical_pow_of_prime Nat.prime_two.prime (n := 2) (by decide))
  rintro ⟨_, r, hr, hd, _, hmiss⟩
  rw [h4] at hd
  rcases (show r = 0 ∨ r = 2 by omega) with rfl | rfl
  · exact hmiss 1 (by decide) (by simpa using (radical_dvd_self (a := (4 : ℕ))))
  · exact hmiss 0 (by decide) (by simp [h2])

theorem powerful_missing {k : ℕ} (hk : Powerful k) (hk1 : k ≠ 1)
    (hk4 : k ≠ 4) : Missing k := by
  obtain ⟨hkpos, b, hb⟩ := hk
  let R := radical k
  let M := R * b
  have hKM : k = R * M := by simpa [M, R, pow_two, mul_assoc] using hb
  have hRpos : 0 < R := Nat.pos_of_ne_zero radical_ne_zero
  have hR1 : R ≠ 1 := by
    intro h
    rcases radical_eq_one_iff.mp h with h0 | hu
    · omega
    · exact hk1 (Nat.isUnit_iff.mp hu)
  have hRM : R ∣ M := ⟨b, rfl⟩
  have hMpos : 0 < M := by
    by_contra! h
    have : M = 0 := by omega
    rw [this, mul_zero] at hKM
    omega
  have hRle := Nat.le_of_dvd hMpos hRM
  have hM3 : 3 ≤ M := by
    by_contra! h
    have hR : R = 2 := by omega
    have hM : M = 2 := by omega
    exact hk4 (by simpa [hR, hM] using hKM)
  let r := R * (M - 1)
  have hRr : R ∣ r := ⟨_, rfl⟩
  have hRk : R ∣ k := radical_dvd_self
  refine ⟨hkpos, r, ?_, hRr, ?_, ?_⟩
  · calc r = R * (M - 1) := rfl
         _ < R * M := Nat.mul_lt_mul_of_pos_left (by omega) hRpos
         _ = k := hKM.symm
  · intro hc
    have h := Nat.dvd_gcd hRr hRk
    rw [show r.gcd k = 1 from hc] at h
    exact hR1 (Nat.dvd_one.mp h)
  · intro t hspos hsmooth
    let y := (M - 1) + M * t
    have hfactor : r + k * t = R * y := by
      change R * (M - 1) + k * t = R * ((M - 1) + M * t)
      conv_lhs => rhs; lhs; rw [hKM]
      ring
    have hy1 : y ≠ 1 := by dsimp [y]; omega
    obtain ⟨p, hp, hpy⟩ := Nat.exists_prime_and_dvd hy1
    have hps : p ∣ r + k * t := hfactor ▸ (hpy.trans (Nat.dvd_mul_left _ _))
    have hpk : p ∣ k :=
      ((dvd_radical_iff_of_irreducible hp.prime.irreducible hspos.ne').mpr hps).trans hsmooth
    have hpM : p ∣ M :=
      ((dvd_radical_iff_of_irreducible hp.prime.irreducible hkpos.ne').mpr hpk).trans hRM
    have hpred : p ∣ M - 1 := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_left hpM t)).mpr hpy
    have h := Nat.dvd_sub hpM hpred
    rw [show M - (M - 1) = 1 by omega] at h
    exact hp.not_dvd_one h

end MissingResidueProof

open MissingResidueProof OMA.S_oeis_a396969

theorem OMA.solution : type_of% @OMA.S_oeis_a396969.main := by
  ext k
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro h
    by_cases hp : Powerful k
    · right
      refine ⟨hp, ?_⟩
      rintro (rfl | rfl)
      · exact squarefree_absent squarefree_one h
      · exact four_absent h
    · exact Or.inl ⟨h, fun hs => squarefree_absent hs h, hp⟩
  · rintro (⟨h, _, _⟩ | ⟨hp, he⟩)
    · exact h
    · exact powerful_missing hp (fun h => he (Or.inl h)) (fun h => he (Or.inr h))

