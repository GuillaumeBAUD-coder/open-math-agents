import OMAReductions.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1

-- If phi(n) divides n - 1 and n > 1 then n is squarefree.
-- Original Lean proof of a classical fact (Lehmer 1932): a prime p with p^2 dividing n divides phi(n), hence
-- n - 1, and it divides n, so it divides 1.
-- A classical first step, not progress on Lehmer's totient problem.

namespace OMA.Lehmer1

theorem squarefree_of_dvd (n : ℕ) (hn : 1 < n) (hsq : ¬ Squarefree n) : ¬ n.totient ∣ n - 1 := by
  intro hdvd
  rw [Nat.squarefree_iff_prime_squarefree] at hsq
  push Not at hsq
  obtain ⟨p, hp, c, hc⟩ := hsq
  have hpt : p ∣ n.totient := by
    rw [hc, mul_assoc, Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_right p c)]
    exact dvd_mul_right p _
  have hpn : p ∣ n := by
    rw [hc, mul_assoc]
    exact dvd_mul_right p _
  have h1 : p ∣ n - (n - 1) := Nat.dvd_sub hpn (hpt.trans hdvd)
  rw [show n - (n - 1) = 1 by omega] at h1
  have h2 := Nat.le_of_dvd Nat.one_pos h1
  have h3 := hp.one_lt
  omega

end OMA.Lehmer1

theorem OMA.solution : OMA.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1.H1 := by
  intro n hn hsq
  exact OMA.Lehmer1.squarefree_of_dvd n hn hsq
