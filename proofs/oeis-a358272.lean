import OMAStatements.S_oeis_a358272
import Mathlib

namespace OMA.S_oeis_a358272

open Finset ArithmeticFunction

private theorem card_fiber (n d : ℕ) (hd : d ∣ n) (hn : 0 < n) :
    #{k ∈ Icc 1 n | Nat.gcd k n = d} = (n / d).totient := by
  obtain ⟨m, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  rw [Nat.mul_div_cancel_left _ hd0, ← Nat.filter_coprime_Ico_eq_totient m 1]
  apply Finset.card_nbij' (fun k => k / d) (fun j => j * d)
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter, mem_Icc, mem_Ico] at hk ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hk
    have hdk : d ∣ k := h3 ▸ Nat.gcd_dvd_left k (d * m)
    obtain ⟨j, rfl⟩ := hdk
    rw [Nat.mul_div_cancel_left _ hd0]
    rw [Nat.gcd_mul_left] at h3
    have : Nat.gcd j m = 1 := by
      have : d * Nat.gcd j m = d * 1 := by simpa using h3
      exact Nat.eq_of_mul_eq_mul_left hd0 this
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp at h1
      · exact h
    have hj2 : j ≤ m := Nat.le_of_mul_le_mul_left h2 hd0
    exact ⟨⟨hj1, by omega⟩, Nat.coprime_comm.mp this⟩
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, mem_Icc, mem_Ico] at hj ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hj
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.mul_pos_iff_of_pos_left hd0 |>.mpr (by omega) |> fun h => by nlinarith
    · nlinarith
    · rw [mul_comm j d, Nat.gcd_mul_left]
      have : Nat.gcd j m = 1 := Nat.coprime_comm.mp h3
      simp [this]
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter, mem_Icc] at hk
    have hdk : d ∣ k := hk.2 ▸ Nat.gcd_dvd_left k (d * m)
    exact Nat.div_mul_cancel hdk
  · intro j _
    exact Nat.mul_div_cancel _ hd0

private theorem sum_fiber (h : ℕ → ℤ) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Icc 1 n, h (Nat.gcd k n) = ∑ d ∈ n.divisors, h d * ((n / d).totient : ℤ) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Icc 1 n) (t := n.divisors) (g := fun k => Nat.gcd k n)]
  · apply Finset.sum_congr rfl
    intro d hd
    have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
    rw [Finset.sum_congr rfl (g := fun _ => h d)]
    · simp [card_fiber n d hdn hn, mul_comm]
    · intro k hk
      rw [(Finset.mem_filter.mp hk).2]
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, by omega⟩

/-- the arithmetic function `n * λ(n)` -/
private noncomputable def gA : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else (n : ℤ) * liouville n, by simp⟩

private theorem gA_mult : gA.IsMultiplicative := by
  refine ⟨by simp [gA, liouville_apply_one], ?_⟩
  intro m n _
  by_cases hm : m = 0
  · simp [gA, hm]
  by_cases hn : n = 0
  · simp [gA, hn]
  have : m * n ≠ 0 := mul_ne_zero hm hn
  simp only [gA, ArithmeticFunction.coe_mk, hm, hn, this, if_false, liouville_apply_mul]
  push_cast; ring

private noncomputable def tA : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else (n.totient : ℤ), by simp⟩

private theorem tA_mult : tA.IsMultiplicative := by
  refine ⟨by simp [tA], ?_⟩
  intro m n h
  by_cases hm : m = 0
  · simp [tA, hm]
  by_cases hn : n = 0
  · simp [tA, hn]
  have : m * n ≠ 0 := mul_ne_zero hm hn
  simp only [tA, ArithmeticFunction.coe_mk, hm, hn, this, if_false]
  rw [Nat.totient_mul h]; push_cast; ring

noncomputable def F (n : ℕ) : ℤ :=
  ∑ k ∈ Icc 1 n, (Nat.gcd k n : ℤ) * liouville (Nat.gcd k n)

private theorem F_eq (n : ℕ) (hn : 0 < n) : F n = (gA * tA) n := by
  unfold F
  rw [sum_fiber (fun d => (d : ℤ) * liouville d) n hn, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j => gA i * tA j)]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hq : n / d ≠ 0 := (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne'
  simp [gA, tA, hd0, hq]

private theorem liou_pp (p i : ℕ) (hp : p.Prime) : liouville (p ^ i) = (-1) ^ i := by
  rw [liouville_apply (pow_ne_zero _ hp.ne_zero), ArithmeticFunction.cardFactors_apply_prime_pow hp]

private theorem gA_pp (p i : ℕ) (hp : p.Prime) : gA (p ^ i) = (-(p : ℤ)) ^ i := by
  simp only [gA, ArithmeticFunction.coe_mk, pow_ne_zero _ hp.ne_zero, if_false, liou_pp p i hp]
  push_cast
  rw [neg_pow]; ring

private theorem tA_succ (p j : ℕ) (hp : p.Prime) :
    tA (p ^ (j + 1)) = (p : ℤ) ^ j * ((p : ℤ) - 1) := by
  simp only [tA, ArithmeticFunction.coe_mk, pow_ne_zero _ hp.ne_zero, if_false]
  rw [Nat.totient_prime_pow_succ hp]
  push_cast [hp.one_le]
  ring

private theorem tA_zero (p : ℕ) : tA (p ^ 0) = 1 := by simp [tA]

private noncomputable def T (p e : ℕ) : ℤ :=
  ∑ i ∈ range (e + 1), (-(p : ℤ)) ^ i * tA (p ^ (e - i))

private theorem T_succ (p e : ℕ) : T p (e + 1) = tA (p ^ (e + 1)) + (-(p : ℤ)) * T p e := by
  unfold T
  rw [Finset.sum_range_succ' _ (e + 1), Finset.mul_sum]
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_add_right]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]; ring

private theorem T_closed (p e : ℕ) (hp : p.Prime) : T p e = (-1) ^ e * (p : ℤ) ^ (2 * (e / 2)) := by
  induction e with
  | zero => simp [T, tA]
  | succ e ih =>
    rw [T_succ, ih, tA_succ p e hp]
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' e
    · have h1 : 2 * m / 2 = m := by omega
      have h2 : (2 * m + 1) / 2 = m := by omega
      have e1 : ((-1 : ℤ)) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
      rw [h1, h2, pow_succ (-1 : ℤ) (2 * m), e1]
      ring
    · have h1 : (2 * m + 1) / 2 = m := by omega
      have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      have e1 : ((-1 : ℤ)) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
      rw [h1, h2, pow_succ (-1 : ℤ) (2 * m), pow_succ (-1 : ℤ) (2 * m + 1), pow_succ (-1 : ℤ) (2 * m), e1]
      ring

private theorem F_pp (p e : ℕ) (hp : p.Prime) :
    (gA * tA) (p ^ e) = (-1) ^ e * (p : ℤ) ^ (2 * (e / 2)) := by
  rw [← T_closed p e hp, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun i j => gA i * tA j),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  unfold T
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ e := by simpa [Nat.lt_succ_iff] using hi
  simp only [Function.Embedding.coeFn_mk]
  rw [gA_pp p i hp, Nat.pow_div hi' hp.pos]

theorem main_aux : ∀ a : ℕ → ℤ, a 1 = 1 →
    (∀ m n : ℕ, Nat.Coprime m n → a (m * n) = a m * a n) →
    (∀ p e : ℕ, p.Prime → a (p ^ e) = (-1) ^ e * (p : ℤ) ^ (2 * (e / 2))) →
    ∀ n : ℕ, 0 < n → a n = F n := by
  intro a h1 hm hp n hn
  rw [F_eq n hn]
  have hmul : (gA * tA).IsMultiplicative := gA_mult.mul tA_mult
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => simp [h1, hmul.map_one]
  | prime_pow p e hp' he => rw [hp p e hp', F_pp p e hp']
  | coprime a' b ha hb hab iha ihb =>
    rw [hm _ _ hab, hmul.map_mul_of_coprime hab, iha (by omega), ihb (by omega)]

end OMA.S_oeis_a358272

theorem OMA.solution : type_of% @OMA.S_oeis_a358272.main := by
  intro a h1 hm hp n hn
  exact OMA.S_oeis_a358272.main_aux a h1 hm hp n hn
