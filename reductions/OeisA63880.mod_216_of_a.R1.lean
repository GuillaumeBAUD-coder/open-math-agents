import FormalConjectures.OEIS.«63880»

-- Credit: @desenyon
open OeisA63880
open scoped ArithmeticFunction.sigma

namespace OMA.R_OeisA63880_mod_216_of_a_R1

private theorem splitUnitary {m q : ℕ} (hm : 0 < m) (hq : IsPrimePow q)
    (hc : q.Coprime m) :
    unitaryDivisors (m*q) = unitaryDivisors m ∪ (unitaryDivisors m).image (· * q) := by
  have hq0 := hq.pos
  ext d
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hd, -⟩, hcd⟩
    obtain ⟨t, ht⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_mul_pos_right (ht ▸ Nat.mul_pos hm hq0)
    rw [ht, Nat.mul_div_cancel_left _ hd0] at hcd
    have hqt : q ∣ d*t := ht ▸ dvd_mul_left q m
    rcases (hcd.isPrimePow_dvd_mul hq).1 hqt with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have he : m = b*t := Nat.eq_of_mul_eq_mul_right hq0 (by linear_combination ht)
      subst m
      have hb : 0 < b := Nat.pos_of_mul_pos_left hd0
      exact Or.inr ⟨b, ⟨⟨dvd_mul_right _ _, hm.ne'⟩, by
        simpa [Nat.mul_div_cancel_left _ hb] using (Nat.coprime_mul_iff_left.1 hcd).2⟩, mul_comm ..⟩
    · have he : m = d*b := Nat.eq_of_mul_eq_mul_right hq0 (by linear_combination ht)
      subst m
      exact Or.inl ⟨⟨dvd_mul_right _ _, hm.ne'⟩, by
        simpa [Nat.mul_div_cancel_left _ hd0] using (Nat.coprime_mul_iff_right.1 hcd).2⟩
  · rintro (⟨⟨⟨t, rfl⟩, -⟩, hcd⟩ | ⟨b, ⟨⟨⟨t, rfl⟩, -⟩, hcd⟩, rfl⟩)
    · have hd := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd] at hcd
      refine ⟨⟨dvd_mul_of_dvd_left (dvd_mul_right d t) q, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_assoc, Nat.mul_div_cancel_left _ hd]
      exact hcd.mul_right (Nat.coprime_mul_iff_right.1 hc).1.symm
    · have hb := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hb] at hcd
      refine ⟨⟨mul_dvd_mul (dvd_mul_right b t) dvd_rfl, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_right_comm b t q, Nat.mul_div_cancel_left _ (Nat.mul_pos hb hq0)]
      exact hcd.mul_left (Nat.coprime_mul_iff_right.1 hc).2

private theorem unitarySum {m q : ℕ} (hm : 0 < m) (hq : IsPrimePow q)
    (hc : q.Coprime m) : usigma (m*q) = usigma m * (q+1) := by
  have dis : Disjoint (unitaryDivisors m) ((unitaryDivisors m).image (· * q)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hd'
    have dvd : b*q ∣ m := (Nat.mem_divisors.1 (Finset.mem_filter.1 hd).1).1
    exact hq.ne_one (hc.eq_one_of_dvd ((dvd_mul_left q b).trans dvd))
  unfold usigma
  rw [splitUnitary hm hq hc, Finset.sum_union dis,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hq.pos h),
    ← Finset.sum_mul, mul_add, mul_one, add_comm]

private theorem sigmaTwo (a : ℕ) : σ 1 (2^a) + 1 = 2 * 2^a := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  induction a with
  | zero => decide
  | succ a ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- Rule out the odd solutions. -/
def H1 : Prop := ∀ m : ℕ, Odd m → ¬ A m

/-- Rule out Mersenne multipliers of exponent at least four for the nonunitary sum
of an odd integer. -/
def H2 : Prop := ∀ m k : ℕ, Odd m → 4 ≤ k →
  (2 ^ k - 1) * (σ 1 m - usigma m) ≠ 3 * usigma m

/-- At the remaining ratio 10/7, the odd part must contain 27. -/
def H3 : Prop := ∀ m : ℕ, Odd m → 7 * σ 1 m = 10 * usigma m → 27 ∣ m

theorem main : H1 → H2 → H3 → type_of% @OeisA63880.mod_216_of_a := by
  intro oddCase large ratio n hn
  obtain ⟨a, m, ho, he⟩ := Nat.exists_eq_two_pow_mul_odd hn.1.ne'
  rw [mul_comm] at he
  subst n
  have hm := Nat.pos_of_mul_pos_right hn.1
  have hc : Nat.Coprime 2 m := Nat.prime_two.coprime_iff_not_dvd.2 (by
    obtain ⟨t, ht⟩ := ho
    omega)
  cases a with
  | zero => exact False.elim (oddCase m ho (by simpa using hn))
  | succ a =>
    have eqn := hn.2
    rw [unitarySum hm ((isPrimePow_nat_iff _).2 ⟨2, a+1, Nat.prime_two, by omega, rfl⟩)
      (hc.pow_left _), ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      (hc.pow_left _).symm] at eqn
    have g := sigmaTwo (a+1)
    have le : usigma m ≤ σ 1 m := by
      simp only [ArithmeticFunction.sigma_apply, pow_one, usigma]
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset ..)
    by_cases big : 2 ≤ a
    · exfalso
      apply large m (a+2) ho (by omega)
      have e : 2^(a+2) - 1 = σ 1 (2^(a+1)) := by rw [pow_succ 2 (a+1)]; omega
      rw [e, Nat.mul_sub, Nat.sub_eq_iff_eq_add (Nat.mul_le_mul_left _ le)]
      nlinarith [congrArg (· * usigma m) g]
    · interval_cases a
      · exact False.elim (oddCase m ho (A_of_mul_prime hm (by simpa using hn) Nat.prime_two
          (Nat.prime_two.coprime_iff_not_dvd.1 hc)))
      · norm_num at g eqn ⊢
        obtain ⟨t, ht⟩ := ratio m ho (by nlinarith)
        obtain ⟨s, hs⟩ := ho
        omega

end OMA.R_OeisA63880_mod_216_of_a_R1
