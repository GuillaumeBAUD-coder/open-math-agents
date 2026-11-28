import OMAReductions.R_OeisA38771_conjecture1_R1
import Mathlib

/-! Step OeisA38771.conjecture1.R1.H1: hypothesis H1 of reduction OeisA38771.conjecture1.R1, the lower bound
`p_{n+1}^2 ≤ a(n)`, which gives `liminf a(n) / p_{n+1}^2 ≥ 1`. -/

-- Credit: @ivillar

namespace OeisA38771StepH1

/-- The least composite `c` with `primorial(n) + c` prime is at least `p_{n+1}^2`. -/
theorem lower (n : ℕ) : (Nat.nth Nat.Prime n) ^ 2 ≤ OeisA38771.a n := by
  have hne := OeisA38771.a_n_exists n
  unfold OeisA38771.a at hne ⊢
  set Q := ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i with hQ
  set S : Set ℕ := {c : ℕ | (c > 1 ∧ ¬ c.Prime) ∧ (Q + c).Prime} with hSdef
  have hS : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hne
    change sInf S = 0
    rw [h, Nat.sInf_empty]
  have hmem := Nat.sInf_mem hS
  change sInf S ∈ S at hmem
  change (Nat.nth Nat.Prime n) ^ 2 ≤ sInf S
  set c := sInf S with hc
  obtain ⟨⟨hc1, hcp⟩, hprime⟩ := hmem
  have hc1' : c ≠ 1 := by omega
  have hr : c.minFac.Prime := Nat.minFac_prime hc1'
  have hrc : c.minFac ^ 2 ≤ c := by
    have := Nat.minFac_sq_le_self (by omega) hcp
    simpa [sq] using this
  have hrQ : ¬ c.minFac ∣ Q := by
    intro h
    have h2 : c.minFac ∣ Q + c := dvd_add h (Nat.minFac_dvd c)
    have h3 := (Nat.prime_dvd_prime_iff_eq hr hprime).mp h2
    have h4 : c.minFac ≤ c := Nat.minFac_le (by omega)
    have hQpos : 0 < Q := Finset.prod_pos fun i _ => (Nat.prime_nth_prime i).pos
    omega
  have hle : Nat.nth Nat.Prime n ≤ c.minFac := by
    by_contra hlt'
    have hlt : c.minFac < Nat.nth Nat.Prime n := not_le.mp hlt'
    have hk1 : Nat.count Nat.Prime (c.minFac + 1) ≤ n :=
      (Nat.count_le_iff_le_nth (p := Nat.Prime) Nat.infinite_setOfPred_prime).mpr hlt
    have hk : Nat.count Nat.Prime c.minFac < n := by
      rw [Nat.count_succ, if_pos hr] at hk1
      omega
    apply hrQ
    rw [← Nat.nth_count hr]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hk)
  calc (Nat.nth Nat.Prime n) ^ 2 ≤ c.minFac ^ 2 := Nat.pow_le_pow_left hle 2
    _ ≤ c := hrc

end OeisA38771StepH1

theorem OMA.solution : OMA.R_OeisA38771_conjecture1_R1.H1 :=
  OeisA38771StepH1.lower
