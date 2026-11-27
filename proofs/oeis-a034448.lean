import OMAStatements.S_oeis_a034448

/-!
Source: https://oeis.org/A034448
Credit: @anmolspace (Lean formalization). Velin Yanev conjectured the ratio in 2017.
Juan José Alba González described the reduction to prime powers in 2021.
-/

namespace OMA.A034448Proof

open Finset ArithmeticFunction UniqueFactorizationMonoid OMA.S_oeis_a034448

private theorem quotient_product {a b m n : ℕ} (ha : a ∣ m) (hb : b ∣ n)
    (hpa : 0 < a) (hpb : 0 < b) : m * n / (a * b) = (m / a) * (n / b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [Nat.mul_div_cancel_left x hpa, Nat.mul_div_cancel_left y hpb,
    show a * x * (b * y) = a * b * (x * y) by ring,
    Nat.mul_div_cancel_left (x * y) (mul_pos hpa hpb)]

/-- Unitary divisors of coprime numbers multiply independently. -/
private theorem unitary_mul {m n : ℕ} (hmn : m.Coprime n) :
    unitarySum (m * n) = unitarySum m * unitarySum n := by
  simp only [unitarySum, Finset.sum_filter]
  rw [sum_mul_sum, ← sum_product', hmn.divisors_mul, sum_map]
  calc
    _ = ∑ v ∈ (m.divisors ×ˢ n.divisors).attach,
        (if v.val.1.Coprime (m / v.val.1) then v.val.1 else 0) *
        (if v.val.2.Coprime (n / v.val.2) then v.val.2 else 0) := by
      apply sum_congr rfl
      rintro ⟨⟨x, y⟩, hxy⟩ _
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      have hxm := Nat.dvd_of_mem_divisors hx
      have hyn := Nat.dvd_of_mem_divisors hy
      have hcross₁ : x.Coprime (n / y) :=
        (hmn.coprime_dvd_left hxm).coprime_dvd_right (Nat.div_dvd_of_dvd hyn)
      have hcross₂ : y.Coprime (m / x) :=
        (hmn.symm.coprime_dvd_left hyn).coprime_dvd_right (Nat.div_dvd_of_dvd hxm)
      change (if (x * y).Coprime (m * n / (x * y)) then x * y else 0) = _
      rw [quotient_product hxm hyn (Nat.pos_of_mem_divisors hx) (Nat.pos_of_mem_divisors hy)]
      simp only [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right]
      split_ifs <;> simp_all
    _ = _ := Finset.sum_attach _ (fun v : ℕ × ℕ =>
      (if v.1.Coprime (m / v.1) then v.1 else 0) * (if v.2.Coprime (n / v.2) then v.2 else 0))

private theorem unitary_prime_power {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    unitarySum (p ^ e) = 1 + p ^ e := by
  have hs : (p ^ e).divisors.filter (fun d => d.Coprime (p ^ e / d)) = {1, p ^ e} := by
    ext d
    rw [mem_filter, Nat.mem_divisors_prime_pow hp, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hc⟩
      by_cases hzero : j = 0
      · left; simp [hzero]
      by_cases htop : j = e
      · exact Or.inr (congrArg (p ^ ·) htop)
      exfalso
      rw [Nat.pow_div hj hp.pos] at hc
      have ha : p ∣ p ^ j := dvd_pow_self _ hzero
      have hb : p ∣ p ^ (e - j) := dvd_pow_self _ (by omega)
      exact hp.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd ha hb)
    · rintro (rfl | rfl)
      · exact ⟨⟨0, by omega, by simp⟩, by simp⟩
      · exact ⟨⟨e, le_rfl, rfl⟩, by simp [pow_pos hp.pos]⟩
  have hne : 1 ≠ p ^ e := (one_lt_pow₀ hp.one_lt he.ne').ne
  simp [unitarySum, hs, hne]

private theorem prime_identity {p : ℕ} (hp : p.Prime) (i : ℕ) :
    unitarySum (p ^ (i + 1)) * sigma 1 (p ^ (i + 1) / radical (p ^ (i + 1))) =
      sigma 1 ((p ^ (i + 1)) ^ 2 / radical (p ^ (i + 1))) := by
  have hr : radical (p ^ (i + 1)) = p := by
    simpa using radical_pow_of_prime (Nat.prime_iff.mp hp) (Nat.succ_ne_zero i)
  have hdiv : p ^ (i + 1) / p = p ^ i := by rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  have hdiv2 : (p ^ (i + 1)) ^ 2 / p = p ^ (i + 1 + i) := by
    rw [pow_two, Nat.mul_div_assoc _ (dvd_pow_self p (i.succ_ne_zero)), hdiv]
    exact (pow_add p (i + 1) i).symm
  have blocks (m : ℕ) : (1 + p ^ m) * (∑ j ∈ range m, p ^ j) = ∑ j ∈ range (m + m), p ^ j := by
    rw [sum_range_add]
    simp_rw [pow_add]
    rw [← mul_sum]
    ring
  rw [unitary_prime_power hp (Nat.succ_pos i), hr, hdiv, hdiv2,
    sigma_apply_prime_pow hp, sigma_apply_prime_pow hp]
  simp only [mul_one]
  rw [show i + 1 + i + 1 = (i + 1) + (i + 1) by omega]
  exact blocks (i + 1)

end OMA.A034448Proof

open OMA.A034448Proof OMA.S_oeis_a034448 ArithmeticFunction UniqueFactorizationMonoid in
theorem OMA.solution : type_of% @OMA.S_oeis_a034448.main := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp he =>
    intro _
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    exact prime_identity hp j
  | zero => omega
  | one => simp [unitarySum]; decide
  | coprime a b ha hb h ia ib =>
    intro _
    have da : radical a ∣ a := radical_dvd_self
    have db : radical b ∣ b := radical_dvd_self
    have da₂ : radical a ∣ a ^ 2 := da.trans (dvd_pow_self a (by decide))
    have db₂ : radical b ∣ b ^ 2 := db.trans (dvd_pow_self b (by decide))
    have hc₁ := (h.coprime_dvd_left (Nat.div_dvd_of_dvd da)).coprime_dvd_right
      (Nat.div_dvd_of_dvd db)
    have hc₂ := ((h.pow 2 2).coprime_dvd_left (Nat.div_dvd_of_dvd da₂)).coprime_dvd_right
      (Nat.div_dvd_of_dvd db₂)
    rw [unitary_mul h, radical_mul (Nat.coprime_iff_isRelPrime.mp h), mul_pow,
      quotient_product da db (Nat.radical_pos a) (Nat.radical_pos b),
      quotient_product da₂ db₂ (Nat.radical_pos a) (Nat.radical_pos b),
      isMultiplicative_sigma.map_mul_of_coprime hc₁, isMultiplicative_sigma.map_mul_of_coprime hc₂,
      ← ia (by omega), ← ib (by omega)]
    ring
