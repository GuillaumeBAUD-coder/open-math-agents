import OMAStatements.S_oeis_a074216
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

namespace OMA.P_oeis_a074216

open OMA.S_oeis_a074216

private lemma sigma_eq_arith (m : ℕ) : sigma m = ArithmeticFunction.sigma 1 m := by
  unfold sigma
  simp [ArithmeticFunction.sigma_apply]

private lemma sigma_prime_pow (p e : ℕ) (hp : p.Prime) :
    sigma (p ^ e) = ∑ i ∈ Finset.range (e + 1), p ^ i := by
  rw [sigma_eq_arith]
  have h := ArithmeticFunction.sigma_apply_prime_pow (k := 1) hp (i := e)
  simpa using h

private lemma sigma_pow_two_odd (e : ℕ) : Odd (sigma (2 ^ e)) := by
  rw [sigma_prime_pow 2 e Nat.prime_two, Finset.sum_range_succ']
  simp only [pow_zero]
  have hev : Even (∑ k ∈ Finset.range e, 2 ^ (k + 1)) := by
    have hmul : ∑ k ∈ Finset.range e, 2 ^ (k + 1) = 2 * ∑ k ∈ Finset.range e, 2 ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hmul]; exact even_two_mul _
  rcases hev with ⟨t, ht⟩
  exact ⟨t, by omega⟩

private lemma sigma_odd_sq_odd (u : ℕ) (hu : Odd u) : Odd (sigma (u ^ 2)) := by
  have hu0 : u ≠ 0 := by rcases hu with ⟨k, rfl⟩; omega
  have hu2 : u ^ 2 ≠ 0 := by positivity
  -- Every divisor of u^2 is odd, so sigma(u^2) ≡ (u^2).divisors.card (mod 2)
  have hmod : sigma (u ^ 2) % 2 = (u ^ 2).divisors.card % 2 := by
    unfold sigma
    rw [Finset.sum_nat_mod]
    have hall : ∀ d ∈ (u ^ 2).divisors, d % 2 = 1 := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      have hodd_u2 : Odd (u ^ 2) := hu.pow
      have hodd_d : Odd d := by
        rcases hd.1 with ⟨c, hc⟩
        rcases hodd_u2 with ⟨t, ht⟩
        by_contra hne
        rw [Nat.not_odd_iff_even] at hne
        rcases hne with ⟨s, hs⟩
        have h2 : 2 * t + 1 = 2 * (s * c) := by nlinarith
        omega
      rcases hodd_d with ⟨s, rfl⟩; omega
    have hsum : ∑ d ∈ (u ^ 2).divisors, d % 2 = ∑ _d ∈ (u ^ 2).divisors, 1 :=
      Finset.sum_congr rfl (fun d hd => hall d hd)
    rw [hsum, Finset.sum_const, smul_eq_mul, mul_one]
  -- (u^2).divisors.card is odd because d ↦ u^2 / d is an involution with unique fixed point u
  have hcard_odd : (u ^ 2).divisors.card % 2 = 1 := by
    let D := (u ^ 2).divisors
    let L := D.filter (fun d => d < u)
    let R := D.filter (fun d => u < d)
    have hmem_u : u ∈ D := Nat.mem_divisors.mpr ⟨⟨u, by ring⟩, hu2⟩
    have hsplit : D = insert u (L ∪ R) := by
      ext d
      simp only [L, R, Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hd
        rcases lt_trichotomy d u with hlt | rfl | hgt
        · exact Or.inr (Or.inl ⟨hd, hlt⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨hd, hgt⟩)
      · rintro (rfl | ⟨hd, _⟩ | ⟨hd, _⟩)
        · exact hmem_u
        · exact hd
        · exact hd
    have hu_not : u ∉ L ∪ R := by simp [L, R]
    have hdisj : Disjoint L R := Finset.disjoint_left.mpr (fun d h1 h2 => by
      simp only [L, R, Finset.mem_filter] at h1 h2; omega)
    have hLR : L.card = R.card := by
      apply Finset.card_bij (fun d _ => u ^ 2 / d)
      · intro d hd
        simp only [L, R, D, Finset.mem_filter, Nat.mem_divisors] at hd ⊢
        rcases hd with ⟨⟨⟨c, hc⟩, _⟩, hlt⟩
        have hdpos : 0 < d := Nat.pos_of_ne_zero (fun h => by subst h; simp at hc; exact hu0 hc)
        have hdiv : u ^ 2 / d = c := by rw [hc, Nat.mul_div_cancel_left c hdpos]
        rw [hdiv]
        refine ⟨⟨⟨d, by linarith⟩, hu2⟩, ?_⟩
        nlinarith
      · intro d1 h1 d2 h2 heq
        simp only [L, D, Finset.mem_filter, Nat.mem_divisors] at h1 h2
        have h1m := Nat.mul_div_cancel' h1.1.1
        have h2m := Nat.mul_div_cancel' h2.1.1
        have hqpos : 0 < u ^ 2 / d2 := by
          have : d2 ≤ u ^ 2 := Nat.le_of_dvd (Nat.pos_of_ne_zero hu2) h2.1.1
          exact Nat.div_pos this (Nat.pos_of_ne_zero (fun h => by subst h; exact hu2 (zero_dvd_iff.mp h2.1.1)))
        rw [heq] at h1m
        exact Nat.eq_of_mul_eq_mul_right hqpos (h1m.trans h2m.symm)
      · intro c hc
        simp only [L, R, D, Finset.mem_filter, Nat.mem_divisors] at hc ⊢
        rcases hc with ⟨⟨⟨d, hd⟩, _⟩, hgt⟩
        have hcpos : 0 < c := by omega
        have hdiv : u ^ 2 / c = d := by rw [hd, Nat.mul_div_cancel_left d hcpos]
        have hdpos : 0 < d := Nat.pos_of_ne_zero (fun h => by subst h; simp at hd; exact hu0 hd)
        refine ⟨d, ⟨⟨⟨c, by linarith⟩, hu2⟩, by nlinarith⟩, ?_⟩
        rw [hd, mul_comm c d, Nat.mul_div_cancel_left c hdpos]
    change D.card % 2 = 1
    rw [hsplit, Finset.card_insert_of_notMem hu_not, Finset.card_union_of_disjoint hdisj, hLR]
    omega
  rw [Nat.odd_iff, hmod, hcard_odd]

private lemma exists_pow_prime_mul_coprime (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    ∃ e u : ℕ, n = p ^ e * u ∧ Nat.Coprime p u := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hdiv : p ∣ n
    · rcases hdiv with ⟨m, rfl⟩
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp at hn
        · exact hpos
      have hlt : m < p * m := lt_mul_of_one_lt_left (by omega) hp.one_lt
      rcases ih m hlt hm1 with ⟨e, u, hmu, hcop⟩
      exact ⟨e + 1, u, by rw [hmu]; ring, hcop⟩
    · exact ⟨0, n, by simp, hp.coprime_iff_not_dvd.mpr hdiv⟩

private lemma not_two_dvd_sigma_two_mul_sq (r : ℕ) (hr : 1 ≤ r) :
    ¬ (2 ∣ sigma (2 * r ^ 2)) := by
  rcases exists_pow_prime_mul_coprime 2 r Nat.prime_two hr with ⟨a, u, rfl, hcop⟩
  have heq : 2 * (2 ^ a * u) ^ 2 = 2 ^ (2 * a + 1) * u ^ 2 := by ring
  rw [heq, sigma_eq_arith]
  have hcop2 : Nat.Coprime (2 ^ (2 * a + 1)) (u ^ 2) := (hcop.pow_left _).pow_right _
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop2, ← sigma_eq_arith, ← sigma_eq_arith]
  have h1 : Odd (sigma (2 ^ (2 * a + 1))) := sigma_pow_two_odd (2 * a + 1)
  have hu_odd : Odd u := Nat.coprime_two_left.mp hcop
  have h2 : Odd (sigma (u ^ 2)) := sigma_odd_sq_odd u hu_odd
  have hodd : Odd (sigma (2 ^ (2 * a + 1)) * sigma (u ^ 2)) := h1.mul h2
  intro hdvd
  rcases hodd with ⟨t, ht⟩
  rcases hdvd with ⟨s, hs⟩
  omega

private lemma sigma_pow_three_mod_three (e : ℕ) : sigma (3 ^ e) % 3 = 1 := by
  rw [sigma_prime_pow 3 e Nat.prime_three, Finset.sum_range_succ']
  simp only [pow_zero]
  have h3 : 3 ∣ ∑ k ∈ Finset.range e, 3 ^ (k + 1) := by
    have hmul : ∑ k ∈ Finset.range e, 3 ^ (k + 1) = 3 * ∑ k ∈ Finset.range e, 3 ^ k := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    rw [hmul]; exact dvd_mul_right 3 _
  rcases h3 with ⟨t, ht⟩
  rw [ht]; omega

private lemma three_dvd_sigma_three_mul_sq_iff (r : ℕ) (hr : 1 ≤ r) :
    3 ∣ sigma (3 * r ^ 2) ↔ 3 ∣ sigma (r ^ 2) := by
  rcases exists_pow_prime_mul_coprime 3 r Nat.prime_three hr with ⟨a, v, rfl, hcop⟩
  have h1 : 3 * (3 ^ a * v) ^ 2 = 3 ^ (2 * a + 1) * v ^ 2 := by ring
  have h2 : (3 ^ a * v) ^ 2 = 3 ^ (2 * a) * v ^ 2 := by ring
  rw [h1, h2, sigma_eq_arith, sigma_eq_arith]
  have hc1 : Nat.Coprime (3 ^ (2 * a + 1)) (v ^ 2) := (hcop.pow_left _).pow_right _
  have hc2 : Nat.Coprime (3 ^ (2 * a)) (v ^ 2) := (hcop.pow_left _).pow_right _
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc1,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc2,
      ← sigma_eq_arith, ← sigma_eq_arith, ← sigma_eq_arith]
  have hm1 := sigma_pow_three_mod_three (2 * a + 1)
  have hm2 := sigma_pow_three_mod_three (2 * a)
  have hcop1 : Nat.Coprime 3 (sigma (3 ^ (2 * a + 1))) :=
    Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)
  have hcop2 : Nat.Coprime 3 (sigma (3 ^ (2 * a))) :=
    Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)
  rw [hcop1.dvd_mul_left, hcop2.dvd_mul_left]

private lemma sq_iff (r : ℕ) (hr : 1 ≤ r) :
    IsInA074216 (r ^ 2) ↔ IsInA072864 r := by
  unfold IsInA074216 IsInA072864
  constructor
  · rintro ⟨_, _, h3⟩
    refine ⟨hr, ?_, (three_dvd_sigma_three_mul_sq_iff r hr).mpr h3⟩
    intro k hk1 hkd
    by_contra hlt
    have hk2 : k = 2 := by omega
    subst hk2
    exact not_two_dvd_sigma_two_mul_sq r hr hkd
  · rintro ⟨_, _, h3⟩
    exact ⟨by nlinarith, ⟨r, rfl⟩, (three_dvd_sigma_three_mul_sq_iff r hr).mp h3⟩

private lemma prove_main :
    (∀ m : ℕ, IsInA074216 m ↔ ∃ r : ℕ, IsInA072864 r ∧ m = r ^ 2) ∧
    (∀ r : ℕ, 1 ≤ r → (IsInA074216 (r ^ 2) ↔ IsInA072864 r)) := by
  refine ⟨?_, sq_iff⟩
  intro m
  constructor
  · intro hm
    rcases hm.2.1 with ⟨r, rfl⟩
    have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | hpos
      · have := hm.1; simp at this
      · exact hpos
    exact ⟨r, (sq_iff r hr).mp hm, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact (sq_iff r hr.1).mpr hr

end OMA.P_oeis_a074216

theorem OMA.solution : type_of% @OMA.S_oeis_a074216.main :=
  OMA.P_oeis_a074216.prove_main
