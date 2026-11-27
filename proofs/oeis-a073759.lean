import OMAStatements.S_oeis_a073759

-- Proof of R. J. Mathar's conjecture by @anmolspace.

namespace MatharProof

open OMA.S_oeis_a073759

/-- A prime common to m and n also divides their positive difference. -/
private lemma upper_bound (n : ℕ) : a n ≤ n - n.minFac := by
  apply Finset.sup_le_iff.mpr
  intro m hm
  obtain ⟨hmrange, _, hcommon⟩ := Finset.mem_filter.mp hm
  have hmn := (Finset.mem_Ico.mp hmrange).2
  obtain ⟨p, hp, hpm, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcommon
  have hpGap := Nat.le_of_dvd (Nat.sub_pos_of_lt hmn) (Nat.dvd_sub hpn hpm)
  have least := Nat.minFac_le_of_dvd hp.two_le hpn
  change m ≤ n - n.minFac
  omega

/-- The candidate n − p lies strictly above n / 2 for every composite n ≥ 5. -/
private lemma attain (n : ℕ) (hn : 5 ≤ n) (hc : ¬ n.Prime) : n - n.minFac ≤ a n := by
  let p := n.minFac
  have prime : p.Prime := Nat.minFac_prime (by omega)
  have divides : p ∣ n := Nat.minFac_dvd n
  have htwo := prime.two_le
  have half : 2*p < n := by
    by_cases h : p = 2
    · omega
    · have square : p^2 ≤ n := Nat.minFac_sq_le_self (by omega) hc
      have hp : 3 ≤ p := by omega
      nlinarith [Nat.zero_le ((p-3)*(p-3))]
  have hgap : p ∣ n - p := Nat.dvd_sub divides (dvd_refl p)
  have nondivisor : ¬ n - p ∣ n := by
    intro h
    have h' := Nat.dvd_sub h (dvd_refl (n-p))
    rw [show n-(n-p)=p by omega] at h'
    have := Nat.le_of_dvd prime.pos h'
    omega
  have common : ¬ (n-p).Coprime n :=
    Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, prime, hgap, divides⟩
  apply Finset.le_sup (f := id)
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, nondivisor, common⟩

private lemma even_gap (n : ℕ) (hn : 5 ≤ n) : 2 * ((n-n.minFac)/2) = n-n.minFac := by
  by_cases he : 2 ∣ n
  · rw [(Nat.minFac_eq_two_iff n).mpr he]
    omega
  · have prime := Nat.minFac_prime (n := n) (by omega)
    rcases prime.eq_two_or_odd with h | h
    · exact False.elim (he ((Nat.minFac_eq_two_iff n).mp h))
    · omega

end MatharProof

open MatharProof OMA.S_oeis_a073759 in
theorem OMA.solution : type_of% @OMA.S_oeis_a073759.main := by
  intro n hn
  change a n = 2 * ((n-n.minFac)/2)
  rw [even_gap n hn]
  apply le_antisymm (upper_bound n)
  by_cases hp : n.Prime
  · simp [hp.minFac_eq]
  · exact attain n hn hp
