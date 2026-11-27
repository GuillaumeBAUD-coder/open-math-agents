import OMAStatements.S_oeis_a101292

-- Reduction oeis-a101292.R1 of A101292: a(n) = n! + Sum_{i=1..n} i.
-- Credit: @justusklocke-cloud
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a101292_R1

open OMA.S_oeis_a101292 (a)

private theorem triangularSum (n : ℕ) : (∑ i ∈ Finset.Icc 1 n, i) = n * (n + 1) / 2 := by
  calc
    (∑ i ∈ Finset.Icc 1 n, i) = ∑ i ∈ Finset.range (n + 1), i := by
      apply Finset.sum_subset
      · intro i hi
        simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
        omega
      · intro i hi hnot
        simp only [Finset.mem_range, Finset.mem_Icc] at hi hnot
        omega
    _ = n * (n + 1) / 2 := by simpa [mul_comm] using Finset.sum_range_id (n + 1)

private theorem factorialValuation {n : ℕ} (hn : 100 < n) :
    3 * (n : ℝ) / 4 < (padicValNat 2 n.factorial : ℝ) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstep (k : ℕ) : padicValNat 2 k.factorial = padicValNat 2 (k / 2).factorial + k / 2 := by
    calc
      padicValNat 2 k.factorial = padicValNat 2 (2 * (k / 2)).factorial :=
        (padicValNat_mul_div_factorial (p := 2) k).symm
      _ = _ := padicValNat_factorial_mul (p := 2) (k / 2)
  have h1 := hstep n
  have h2 := hstep (n / 2)
  have h3 := hstep (n / 2 / 2)
  have hnat : 3 * n < 4 * padicValNat 2 n.factorial := by omega
  exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr (by
    have hreal : 3 * (n : ℝ) < 4 * (padicValNat 2 n.factorial : ℝ) := by exact_mod_cast hnat
    simpa [mul_comm] using hreal)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checkedNeighbors : ∀ n : Fin 101,
    let t := n.val.factorial + n.val * (n.val + 1) / 2
    let indices : List ℕ :=
      [2, 3, 5, 6, 9, 11, 15, 19, 23, 28, 33, 38, 43, 48, 54, 59,
       65, 71, 77, 83, 89, 95, 102, 108, 115, 122, 128, 135, 142, 149, 156, 163,
       171, 178, 185, 193, 200, 208, 215, 223, 230, 238, 246, 254, 262, 270, 277, 285,
       294, 302, 310, 318, 326, 334, 343, 351, 359, 368, 376, 385, 393, 402, 410, 419,
       428, 436, 445, 454, 462, 471, 480, 489, 498, 507, 516, 525, 534, 543, 552, 561,
       570, 579, 588, 597, 607, 616, 625, 634, 644, 653, 662, 672, 681, 691, 700, 709,
       719, 728, 738, 747, 757]
    let r := indices[n.val]!
    (t = 1 ∨ t = 2 ∨ t = 5 ∨ t = 34) ∨
      (Nat.fastFib r < t ∧ t < Nat.fastFib (r + 1)) := by
  decide +kernel

private theorem smallFactoriangular {n m : ℕ} (hn : n ≤ 100)
    (hm : n.factorial + n * (n + 1) / 2 = Nat.fib m) :
    Nat.fib m ∈ ({1, 2, 5, 34} : Set ℕ) := by
  rcases checkedNeighbors ⟨n, by omega⟩ with hknown | hgap
  · rw [← hm]
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hknown
  · obtain ⟨r, hlo, hhi⟩ : ∃ r : ℕ,
        Nat.fastFib r < n.factorial + n * (n + 1) / 2 ∧
          n.factorial + n * (n + 1) / 2 < Nat.fastFib (r + 1) := ⟨_, hgap⟩
    rw [Nat.fastFib_eq, hm] at hlo hhi
    have hleft : r < m := lt_of_not_ge fun h => hlo.not_ge (Nat.fib_mono h)
    have hright : m < r + 1 := lt_of_not_ge fun h => hhi.not_ge (Nat.fib_mono h)
    omega

private lemma twice_triangular (n : ℕ) : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
  have h : 2 ∣ n * (n + 1) := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · simp [he]
    · have hnext : (n + 1) % 2 = 0 := by omega
      simp [hnext]
  exact Nat.mul_div_cancel' h

private lemma triangular_mono : Monotone (fun n : ℕ => n * (n + 1) / 2) := by
  intro a b hab
  exact Nat.div_le_div_right (Nat.mul_le_mul hab (Nat.add_le_add_right hab 1))

private lemma fib_period {period modulus : ℕ}
    (h0 : Nat.fib period ≡ Nat.fib 0 [MOD modulus])
    (h1 : Nat.fib (period + 1) ≡ Nat.fib 1 [MOD modulus]) (n : ℕ) :
    Nat.fib (n + period) ≡ Nat.fib n [MOD modulus] := by
  have hpair : ∀ k, (Nat.fib (k + period) ≡ Nat.fib k [MOD modulus]) ∧
      (Nat.fib (k + period + 1) ≡ Nat.fib (k + 1) [MOD modulus]) := by
    intro k
    induction k with
    | zero => simpa only [Nat.zero_add] using And.intro h0 h1
    | succ k ih =>
      constructor
      · simpa only [show k.succ + period = k + period + 1 by omega] using ih.2
      · rw [show k.succ + period + 1 = (k + period) + 2 by omega,
          show k.succ + 1 = k + 2 by omega, Nat.fib_add_two, Nat.fib_add_two]
        exact ih.1.add ih.2
  exact (hpair n).1

private lemma fib_reduce_index (n : ℕ) :
    Nat.fib n ≡ Nat.fib (n % 1680) [MOD 85414139387657080] := by
  have h0 : Nat.fib 1680 ≡ Nat.fib 0 [MOD 85414139387657080] := by
    rw [Nat.fib_eq_fastFib]
    decide +kernel
  have h1 : Nat.fib (1680 + 1) ≡ Nat.fib 1 [MOD 85414139387657080] := by
    rw [Nat.fib_eq_fastFib]
    decide +kernel
  have h : ∀ q : ℕ,
      Nat.fib (n % 1680 + 1680 * q) ≡ Nat.fib (n % 1680) [MOD 85414139387657080] := by
    intro q
    induction q with
    | zero => rw [Nat.mul_zero, Nat.add_zero]
    | succ q ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc]
      exact (fib_period h0 h1 _).trans ih
  simpa only [Nat.mod_add_div] using h (n / 1680)

private lemma residue_check : ∀ i : Fin 1680,
    let r := Nat.fastFib i.val % 85414139387657080
    55 < r → (Nat.sqrt (8 * r + 1)) ^ 2 ≠ 8 * r + 1 := by
  decide +kernel

/-- The large finite range of Gómez Ruiz and Luca, proved by an exact modular sieve. -/
private theorem noSolutionBetween (n m : ℕ) (hlo : 83 ≤ n) (hhi : n ≤ 400000000) :
    n.factorial + n * (n + 1) / 2 ≠ Nat.fib m := by
  intro heq
  have hdvd : 85414139387657080 ∣ n.factorial :=
    (by decide +kernel : 85414139387657080 ∣ (83 : ℕ).factorial).trans (Nat.factorial_dvd_factorial hlo)
  have hsmall : (n * (n + 1) / 2) < 85414139387657080 := (triangular_mono hhi).trans_lt (by decide +kernel)
  have hbig : 55 < (n * (n + 1) / 2) := (by decide +kernel : 55 < (83 * (83 + 1) / 2)).trans_le
    (triangular_mono hlo)
  have hfib : Nat.fib m % 85414139387657080 = (n * (n + 1) / 2) := by
    rw [← heq]
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, Nat.zero_add, Nat.mod_eq_of_lt hsmall,
      Nat.mod_eq_of_lt hsmall]
  have hperiodpos : 0 < 1680 := by decide
  let i : Fin 1680 := ⟨m % 1680, Nat.mod_lt _ hperiodpos⟩
  have hi : Nat.fastFib i.val % 85414139387657080 = (n * (n + 1) / 2) := by
    rw [Nat.fastFib_eq]
    have h := (fib_reduce_index m).symm
    change Nat.fib (m % 1680) % 85414139387657080 = Nat.fib m % 85414139387657080 at h
    exact h.trans hfib
  have habs := residue_check i
  dsimp only at habs
  rw [hi] at habs
  apply habs hbig
  have hsquare : 8 * (n * (n + 1) / 2) + 1 = (2 * n + 1) ^ 2 := by
    nlinarith only [twice_triangular n]
  rw [hsquare, Nat.sqrt_eq']

/-- A bound for the 2-adic valuation of the factorial, as in equations (7) and (8).
The coefficient adds the two separate bounds for the factors. -/
def H1 : Prop :=
  ∀ n m : ℕ, 100 < n → OMA.S_oeis_a101292.a n = Nat.fib m →
    (padicValNat 2 n.factorial : ℝ) < 30442 * (max 10 (Real.log n)) ^ 3

/-- The elementary real inequality used to turn the valuation estimate into a finite bound. -/
def H2 : Prop :=
  ∀ x : ℝ, 400000000 < x → 30442 * (max 10 (Real.log x)) ^ 3 ≤ 3 * x / 4

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a101292.main := by
  intro hvaluation hreal
  ext x
  constructor
  · rintro ⟨⟨n, rfl⟩, ⟨m, hm⟩⟩
    have hnm : n.factorial + n * (n + 1) / 2 = Nat.fib m := by
      simpa only [a, triangularSum] using hm.symm
    by_cases hsmall : n ≤ 100
    · rw [← hm]
      exact smallFactoriangular hsmall hnm
    have hbig : 100 < n := Nat.lt_of_not_ge hsmall
    have hbound : n ≤ 400000000 := by
      by_contra! hlarge
      have hlargeReal : (400000000 : ℝ) < n := by exact_mod_cast hlarge
      exact (not_le_of_gt (factorialValuation hbig))
        ((hvaluation n m hbig hm.symm).le.trans (hreal n hlargeReal))
    exact (noSolutionBetween n m (by omega) hbound hnm).elim
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩⟩
    · exact ⟨⟨1, by decide +kernel⟩, ⟨3, by decide +kernel⟩⟩
    · exact ⟨⟨2, by decide +kernel⟩, ⟨5, by decide +kernel⟩⟩
    · exact ⟨⟨4, by decide +kernel⟩, ⟨9, by decide +kernel⟩⟩

end OMA.R_oeis_a101292_R1
