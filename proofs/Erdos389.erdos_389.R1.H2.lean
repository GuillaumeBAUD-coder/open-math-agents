import OMAReductions.R_Erdos389_erdos_389_R1

/-! Compare `p`-adic valuations. For `p ≤ B` this is the second hypothesis. For `p > B` we have
`p > n - 1` and `p² > n + 2k - 1`, so Legendre's formula has a single term and
`v_p(L) = ⌊(n+k-1)/p⌋`, `v_p(R) = ⌊(n+2k-1)/p⌋ - ⌊(n+k-1)/p⌋`. If `2⌊(n+k-1)/p⌋ > ⌊(n+2k-1)/p⌋`,
then `X = ⌊(n+k-1)/p⌋ p` gives `s = X - k` with `(n-1)/2 < s ≤ n-1` and `p ∣ k + s`, against the
smoothness hypothesis. -/

namespace OMA.E389

theorem val_fact {p m : ℕ} (hp : p.Prime) (hm : m < p ^ 2) :
    padicValNat p m.factorial = m / p := by
  haveI := Fact.mk hp
  have hlog : Nat.log p m < 2 := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp
    · exact Nat.log_lt_of_lt_pow hpos.ne' hm
  rw [padicValNat_factorial hlog]
  have h12 : Finset.Ico 1 2 = {1} := by decide
  rw [h12]
  simp

end OMA.E389

theorem OMA.solution : OMA.R_Erdos389_erdos_389_R1.H2 := by
  intro n k hn hk hs hp
  have hL0 : ∏ i ∈ Finset.range k, (n + i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by omega)
  have hR0 : ∏ i ∈ Finset.range k, (n + k + i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by omega)
  refine (Nat.factorization_prime_le_iff_dvd hL0 hR0).mp ?_
  intro p pp
  rw [Nat.factorization_def _ pp, Nat.factorization_def _ pp]
  by_cases hpB : p ≤ max (n - 1) (Nat.sqrt (n + 2 * k - 1))
  · exact hp p pp hpB
  · have hpB' : max (n - 1) (Nat.sqrt (n + 2 * k - 1)) < p := not_le.mp hpB
    have hp1 : n - 1 < p := lt_of_le_of_lt (le_max_left _ _) hpB'
    have hp2 : Nat.sqrt (n + 2 * k - 1) < p := lt_of_le_of_lt (le_max_right _ _) hpB'
    have hsq : n + 2 * k - 1 < p ^ 2 := by
      rw [sq]
      exact Nat.sqrt_lt.mp hp2
    have hpp : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
    haveI := Fact.mk pp
    have e1 : (n - 1).factorial * ∏ i ∈ Finset.range k, (n + i) = (n + k - 1).factorial := by
      rw [← Nat.ascFactorial_eq_prod_range]
      exact Nat.factorial_mul_ascFactorial' n k hn
    have e2 : (n + k - 1).factorial * ∏ i ∈ Finset.range k, (n + k + i) =
        (n + 2 * k - 1).factorial := by
      rw [← Nat.ascFactorial_eq_prod_range, Nat.factorial_mul_ascFactorial' (n + k) k (by omega)]
      congr 1
      omega
    have v1 := congrArg (padicValNat p) e1
    have v2 := congrArg (padicValNat p) e2
    rw [padicValNat.mul (Nat.factorial_ne_zero _) hL0, OMA.E389.val_fact pp (by omega),
      OMA.E389.val_fact pp (by omega)] at v1
    rw [padicValNat.mul (Nat.factorial_ne_zero _) hR0, OMA.E389.val_fact pp (by omega),
      OMA.E389.val_fact pp hsq] at v2
    have z : (n - 1) / p = 0 := Nat.div_eq_of_lt hp1
    have key : 2 * ((n + k - 1) / p) ≤ (n + 2 * k - 1) / p := by
      rw [Nat.le_div_iff_mul_le pp.pos]
      by_contra hcon
      have hcon' : n + 2 * k - 1 < 2 * ((n + k - 1) / p) * p := not_le.mp hcon
      obtain ⟨X, hX⟩ : ∃ X, X = (n + k - 1) / p * p := ⟨_, rfl⟩
      have hXle : X ≤ n + k - 1 := hX ▸ Nat.div_mul_le_self (n + k - 1) p
      have h2X : 2 * ((n + k - 1) / p) * p = 2 * X := by rw [hX]; ring
      rw [h2X] at hcon'
      have hdvd : p ∣ k + (X - k) := by
        have hk' : k + (X - k) = X := by omega
        rw [hk', hX]
        exact Dvd.intro_left _ rfl
      have hle := hs (X - k) (by omega) (by omega) p pp hdvd
      exact absurd hle hpB
    omega
