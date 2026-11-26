import FormalConjectures.ErdosProblems.«454»

/-! The first minimum of a linearly tilted prime sequence gives a strict midpoint. -/

open Filter

namespace OMA

lemma exists_small_totient (c : ℕ) (hc : 0 < c) :
    ∃ a : ℕ, 0 < a ∧ c * a.totient ≤ a := by
  classical
  let u := Set.indicator {p : ℕ | p.Prime} (fun p : ℕ => (1 : ℝ) / p)
  have hu (p : ℕ) : 0 ≤ u p := Set.indicator_nonneg (fun _ _ => by positivity) _
  have hdiv : Tendsto (fun N : ℕ => ∑ p ∈ Finset.range N, u p) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hu).mp not_summable_one_div_on_primes
  obtain ⟨N, hN⟩ := ((tendsto_atTop.mp hdiv) (c : ℝ)).exists
  let s := N.primesBelow
  have hsum : (c : ℝ) ≤ ∑ p ∈ s, (p : ℝ)⁻¹ := by
    simpa only [s, u, Nat.primesBelow_eq_filter_range, Finset.sum_filter,
      Set.indicator_apply, Set.mem_ofPred_eq, one_div] using hN
  let a : ℕ := ∏ p ∈ s, p
  have hprime (p : ℕ) (hp : p ∈ s) : p.Prime := Nat.prime_of_mem_primesBelow hp
  have ha : 0 < a := Finset.prod_pos fun p hp => (hprime p hp).pos
  have hpf : a.primeFactors = s := Nat.primeFactors_prod hprime
  have htot : (a.totient : ℝ) = a * ∏ p ∈ s, (1 - (p : ℝ)⁻¹) := by
    have heq := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors a)
    push_cast at heq
    simpa only [hpf] using heq
  have hprod :
      (∏ p ∈ s, (1 - (p : ℝ)⁻¹)) ≤ Real.exp (-(∑ p ∈ s, (p : ℝ)⁻¹)) := by
    calc
      _ ≤ ∏ p ∈ s, Real.exp (-(p : ℝ)⁻¹) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).one_le
          exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp')
        · intro p _
          linarith only [Real.add_one_le_exp (-(p : ℝ)⁻¹)]
      _ = _ := by rw [← Real.exp_sum, Finset.sum_neg_distrib]
  have hlow : (c : ℝ) ≤ Real.exp (∑ p ∈ s, (p : ℝ)⁻¹) := by
    linarith only [hsum, Real.add_one_le_exp (∑ p ∈ s, (p : ℝ)⁻¹)]
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hexp : Real.exp (-(∑ p ∈ s, (p : ℝ)⁻¹)) ≤ (c : ℝ)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hcR hlow
  have hle : (c : ℝ) * (a.totient : ℝ) ≤ (a : ℝ) := by
    calc
      _ = (a : ℝ) * ((c : ℝ) * ∏ p ∈ s, (1 - (p : ℝ)⁻¹)) := by rw [htot]; ring
      _ ≤ (a : ℝ) * ((c : ℝ) * (c : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hprod.trans hexp) hcR.le) (Nat.cast_nonneg a)
      _ = _ := by rw [mul_inv_cancel₀ hcR.ne', mul_one]
  exact ⟨a, ha, by exact_mod_cast hle⟩

lemma primeIndexLinearBound (c : ℕ) (hc : 0 < c) :
    ∃ K : ℕ, ∀ n : ℕ, c * n ≤ n.nth Nat.Prime + K := by
  obtain ⟨a, ha, hca⟩ := exists_small_totient c hc
  let b := a + 1
  let K := c * (b.primeCounting' + a.totient)
  refine ⟨K, ?_⟩
  intro n
  let p := n.nth Nat.Prime
  have hp : p.primeCounting' = n := Nat.primeCounting'_nth_eq n
  change c * n ≤ p + K
  by_cases hbp : b ≤ p
  · let d := p - b
    have hd : b + d = p := Nat.add_sub_of_le hbp
    have hcount := Nat.primeCounting'_add_le (a := a) (k := b) ha.ne' (by dsimp [b]; omega) d
    rw [hd, hp] at hcount
    calc
      _ ≤ c * (b.primeCounting' + a.totient * (d / a + 1)) := Nat.mul_le_mul_left _ hcount
      _ = K + (c * a.totient) * (d / a) := by dsimp only [K]; ring
      _ ≤ K + a * (d / a) := Nat.add_le_add_left (Nat.mul_le_mul_right _ hca) _
      _ ≤ K + d := Nat.add_le_add_left (by rw [mul_comm]; exact Nat.div_mul_le_self d a) _
      _ ≤ p + K := by rw [add_comm K]; exact Nat.add_le_add_right (Nat.sub_le _ _) _
  · have hn : n ≤ b.primeCounting' := by
      rw [← hp]
      exact Nat.monotone_primeCounting' (by omega : p ≤ b)
    calc
      _ ≤ c * b.primeCounting' := Nat.mul_le_mul_left _ hn
      _ ≤ K := by dsimp only [K]; exact Nat.mul_le_mul_left c (by omega)
      _ ≤ _ := by omega

lemma integerSequence_first_minimum (g : ℕ → ℤ) (K : ℤ) (hK : ∀ n, K ≤ g n) :
    ∃ n, (∀ m, g n ≤ g m) ∧ ∀ m < n, g n < g m := by
  classical
  obtain ⟨z, hz, hzmin⟩ := Int.exists_least_of_bdd (P := fun z => ∃ n, g n = z)
    ⟨K, by rintro _ ⟨n, rfl⟩; exact hK n⟩ ⟨g 0, 0, rfl⟩
  let n := Nat.find hz
  have hn : g n = z := Nat.find_spec hz
  refine ⟨n, ?_, ?_⟩
  · intro m
    rw [hn]
    exact hzmin _ ⟨m, rfl⟩
  · intro m hm
    rw [hn]
    exact lt_of_le_of_ne (hzmin _ ⟨m, rfl⟩) (Ne.symm (Nat.find_min hz hm))

lemma nth_prime_odd_of_pos {n : ℕ} (hn : 0 < n) : Odd (n.nth Nat.Prime) := by
  apply (Nat.prime_nth_prime n).odd_of_ne_two
  have := Nat.add_two_le_nth_prime n
  omega

end OMA

theorem OMA.solution : type_of% @Erdos454.erdos_454.variants.two_le_limsup := by
  classical
  have hpred : (Prime : ℕ → Prop) = Nat.Prime :=
    funext fun _ => propext Nat.prime_iff.symm
  simp only [hpred]
  apply le_limsup_of_frequently_le'
  refine frequently_atTop.mpr fun N => ?_
  let M := max N 1
  let k := M + 1
  let c := k.nth Nat.Prime + 1
  let g (n : ℕ) : ℤ := (n.nth Nat.Prime : ℤ) - (c : ℤ) * (n : ℤ)
  obtain ⟨K, hK⟩ := OMA.primeIndexLinearBound c (Nat.succ_pos _)
  have hbounded (j : ℕ) : -(K : ℤ) ≤ g j := by
    have hj : (c : ℤ) * (j : ℤ) ≤ (j.nth Nat.Prime : ℤ) + (K : ℤ) := by
      exact_mod_cast hK j
    dsimp only [g]
    linarith only [hj]
  obtain ⟨n, hmin, hfirst⟩ := OMA.integerSequence_first_minimum g (-(K : ℤ)) hbounded
  have hnM : M < n := by
    by_contra h
    have hn : n ≤ M := by omega
    have hnk : (n : ℤ) + 1 ≤ (k : ℤ) := by
      exact_mod_cast (show n + 1 ≤ k from Nat.add_le_add_right hn 1)
    have hmul := mul_le_mul_of_nonneg_left hnk (Int.natCast_nonneg c)
    have hpk : (k.nth Nat.Prime : ℤ) + 1 = (c : ℤ) := by simp [c]
    have hn0 := Int.natCast_nonneg (n.nth Nat.Prime)
    have hnk' := hmin k
    dsimp only [g] at hnk'
    linarith only [hmul, hpk, hn0, hnk']
  have hn1 : 1 < n := lt_of_le_of_lt (le_max_right _ _) hnM
  have hnN : N ≤ n := (le_max_left _ _).trans hnM.le
  refine ⟨n, hnN, ?_⟩
  have hFn : 2 * n.nth Nat.Prime + 2 ≤ Erdos454.f n := by
    unfold Erdos454.f
    simp only [hpred, if_neg (not_le_of_gt hn1)]
    have : Nonempty {i : Fin n // 0 < (i : ℕ)} := ⟨⟨⟨1, hn1⟩, Nat.zero_lt_succ _⟩⟩
    apply le_ciInf
    intro i
    let j : ℕ := i.1
    have hjpos : 0 < j := i.2
    have hjlt : j < n := i.1.isLt
    change 2 * n.nth Nat.Prime + 2 ≤ (n + j).nth Nat.Prime + (n - j).nth Nat.Prime
    have hminus := hfirst (n - j) (by omega)
    have hplus := hmin (n + j)
    dsimp only [g] at hminus hplus
    rw [Int.natCast_sub (by omega : j ≤ n)] at hminus
    push_cast at hplus
    have hstrictI : (2 : ℤ) * (n.nth Nat.Prime : ℤ) <
        ((n + j).nth Nat.Prime : ℤ) + ((n - j).nth Nat.Prime : ℤ) := by
      linarith only [hminus, hplus]
    have hstrict : 2 * n.nth Nat.Prime <
        (n + j).nth Nat.Prime + (n - j).nth Nat.Prime := by exact_mod_cast hstrictI
    have hoddl := OMA.nth_prime_odd_of_pos (show 0 < n + j by omega)
    have hoddr := OMA.nth_prime_odd_of_pos (show 0 < n - j by omega)
    obtain ⟨q, hq⟩ := hoddl.add_odd hoddr
    omega
  have hFn' : (2 : ℕ∞) * (n.nth Nat.Prime : ℕ∞) + 2 ≤ (Erdos454.f n : ℕ∞) := by
    exact_mod_cast hFn
  have hfinite : (2 : ℕ∞) * (n.nth Nat.Prime : ℕ∞) ≠ ⊤ := by
    change ((2 * n.nth Nat.Prime : ℕ) : ℕ∞) ≠ ⊤
    exact ENat.natCast_ne_top _
  exact ENat.le_sub_of_add_le_left hfinite hFn'