import OMAReductions.R_Erdos384_erdos_384_R1

/-!
# Ecklund's first case (step H1 of Erdos384.erdos_384.R1)

If `4 ≤ k`, `k² < n` and no prime `p ≤ n/2` divided `C(n, k)`, then every prime factor of
`C(n, k)` would be an odd prime of `(n - k, n]` occurring once, so `C(n, k)` divides the product
of the odd numbers of `(n - k, n]`. Since that whole interval multiplies to `k! * C(n, k)`, the
even numbers of `(n - k, n]` (at least `k / 2` of them, each `≥ n - k + 1`) would multiply to at
most `k!`, while `k! < (n - k + 1) ^ (k / 2)` once `n > k²`.
-/

open Nat Finset

namespace OMA.EckH1

theorem fact_lt_pow : ∀ k, 2 ≤ k → ∀ m, k * k + 2 ≤ m + k → k ! < m ^ (k / 2) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk m hm
    rcases (show k = 2 ∨ k = 3 ∨ 4 ≤ k by omega) with rfl | rfl | h4
    · norm_num [Nat.factorial] at hm ⊢; omega
    · norm_num [Nat.factorial] at hm ⊢; omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have hj : 2 ≤ j := by omega
      have hm' : j * j + 2 ≤ m + j := by nlinarith
      have h1 := ih j (by omega) hj m hm'
      have h2 : (j + 2) * (j + 1) < m := by nlinarith
      rw [Nat.factorial_succ, Nat.factorial_succ, show (j + 1 + 1) / 2 = j / 2 + 1 by omega,
        pow_succ]
      calc (j + 1 + 1) * ((j + 1) * j !) = ((j + 2) * (j + 1)) * j ! := by ring
        _ < m * j ! := Nat.mul_lt_mul_of_pos_right h2 (Nat.factorial_pos j)
        _ ≤ m * m ^ (j / 2) := Nat.mul_le_mul_left m h1.le
        _ = m ^ (j / 2) * m := by ring

theorem ecklund_small_k : ∀ n k : ℕ, 4 ≤ k → k * k < n →
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  intro n k hk hn
  by_contra hcon
  push_neg at hcon
  have hkn : 4 * k < n := by nlinarith
  have hC0 : n.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  -- every prime factor of C(n, k) lies in (n - k, n] and is odd
  have hpf : (n.choose k).primeFactors ⊆ (Ioc (n - k) n).filter (fun m => ¬ Even m) := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpd, -⟩ := hp
    have h2p := hcon p hpp hpd
    have hdesc : p ∣ ∏ i ∈ range k, (n - i) := by
      rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose]
      exact Dvd.dvd.mul_left hpd _
    obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hdesc
    rw [Finset.mem_range] at hi
    have hni : n - i ≤ n := Nat.sub_le n i
    obtain ⟨c, hc⟩ := hpi
    have hc1 : c = 1 := by
      rcases c with _ | _ | c
      · simp at hc; omega
      · rfl
      · nlinarith
    subst hc1
    rw [mul_one] at hc
    have h2 : 2 < p := by omega
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨by omega, by omega⟩, fun he => ?_⟩
    have := hpp.eq_one_or_self_of_dvd 2 (even_iff_two_dvd.mp he)
    omega
  -- C(n, k) is squarefree
  have hsqf : Squarefree (n.choose k) := by
    rw [Nat.squarefree_iff_factorization_le_one hC0]
    intro p
    by_cases hp : p.Prime
    · by_cases hpd : p ∣ n.choose k
      · apply Nat.factorization_choose_le_one
        have h1 := hcon p hp hpd
        have h2 := hp.two_le
        rw [sq]; nlinarith
      · simp [Nat.factorization_eq_zero_of_not_dvd hpd]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hCdvd : n.choose k ∣ ∏ m ∈ (Ioc (n - k) n).filter (fun m => ¬ Even m), m :=
    calc n.choose k = ∏ p ∈ (n.choose k).primeFactors, p :=
          (Nat.prod_primeFactors_of_squarefree hsqf).symm
      _ ∣ _ := Finset.prod_dvd_prod_of_subset _ _ _ hpf
  -- the product of (n - k, n] is k! * C(n, k)
  have hprod : ∏ m ∈ Ioc (n - k) n, m = k ! * n.choose k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
    apply Finset.prod_nbij' (fun m => n - m) (fun i => n - i)
    · intro a ha; simp only [Finset.mem_Ioc] at ha; simp only [Finset.mem_range]; omega
    · intro a ha; simp only [Finset.mem_range] at ha; simp only [Finset.mem_Ioc]; omega
    · intro a ha; simp only [Finset.mem_Ioc] at ha; omega
    · intro a ha; simp only [Finset.mem_range] at ha; omega
    · intro a ha; simp only [Finset.mem_Ioc] at ha; omega
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Ioc (n - k) n) (fun m => Even m)
    (fun m => m)
  set E := ∏ m ∈ (Ioc (n - k) n).filter (fun m => Even m), m with hE
  set O := ∏ m ∈ (Ioc (n - k) n).filter (fun m => ¬ Even m), m with hO
  have hOpos : 0 < O := by
    apply Finset.prod_pos
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
    omega
  have hCO : n.choose k ≤ O := Nat.le_of_dvd hOpos hCdvd
  have hEk : E ≤ k ! := by
    have h1 : E * O = k ! * n.choose k := by rw [hsplit, hprod]
    have h2 : E * O ≤ k ! * O := by rw [h1]; exact Nat.mul_le_mul_left _ hCO
    exact Nat.le_of_mul_le_mul_right h2 hOpos
  -- at least k / 2 even numbers in (n - k, n]
  have hcard : k / 2 ≤ ((Ioc (n - k) n).filter (fun m => Even m)).card := by
    have : (range (k / 2)).card ≤ ((Ioc (n - k) n).filter (fun m => Even m)).card := by
      apply Finset.card_le_card_of_injOn (fun j => 2 * ((n - k) / 2 + 1 + j))
      · intro j hj
        simp only [Finset.coe_range, Set.mem_Iio] at hj
        simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq]
        exact ⟨⟨by omega, by omega⟩, even_two_mul _⟩
      · intro a _ b _ h
        simp only at h
        omega
    simpa using this
  have hm : k * k + 2 ≤ (n - k + 1) + k := by omega
  have h1 := fact_lt_pow k (by omega) (n - k + 1) hm
  have h2 : (n - k + 1) ^ (k / 2) ≤ (n - k + 1) ^ ((Ioc (n - k) n).filter (fun m => Even m)).card :=
    Nat.pow_le_pow_right (by omega) hcard
  have h3 : (n - k + 1) ^ ((Ioc (n - k) n).filter (fun m => Even m)).card ≤ E := by
    apply Finset.pow_card_le_prod
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
    omega
  omega

end OMA.EckH1

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1.H1 := by
  exact OMA.EckH1.ecklund_small_k
