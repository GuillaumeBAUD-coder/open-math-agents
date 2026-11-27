import FormalConjectures.ErdosProblems.«1160»

/-!
Su and Xia, arXiv:2610.11092v1, Theorem 1.1 implies the sum variant
by taking x equal to 2^m. This reduction separates the two enumeration
estimates that enter their proof in section 8.7. For a cutoff r, orders
divisible by 2^k below 2^(k+r) have one of finitely many multipliers q.
We can therefore use a separate eventual bound for each fixed q.
-/

open Filter Finset Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3

/-- Uniform saving for orders with a large deficit in their 2-adic exponent.
For non-powers of two this is the large-deficit range in section 8.7.
For powers of two it follows from the estimates in Corollary 7.1. -/
def H1 : Prop :=
  ∃ r : ℕ, 0 < r ∧ ∀ᶠ k : ℕ in atTop, ∀ n ∈ Ico 1 (2 ^ (k + r)),
    ¬ 2 ^ k ∣ n → 2 ^ (k + r) * g n ≤ g (2 ^ (k + r))

/-- Saving at a fixed dyadic fraction q/2^r of the endpoint.
The odd part of q is fixed, as in the bounded-deficit range of section 8.7.
The threshold may depend on both q and r. -/
def H2 : Prop :=
  ∀ r q : ℕ, 0 < r → 0 < q → q < 2 ^ r → ∀ᶠ k : ℕ in atTop,
    2 ^ (k + r) * g (2 ^ k * q) ≤ g (2 ^ (k + r))

lemma sum_le_of_pointwise (a : ℕ → ℕ) (t : ℕ) (ht : 0 < t)
    (h : ∀ n ∈ Ico 1 t, t * a n ≤ a t) : ∑ n ∈ Ico 1 t, a n ≤ a t := by
  apply Nat.le_of_mul_le_mul_left _ ht
  calc
    t * ∑ n ∈ Ico 1 t, a n = ∑ n ∈ Ico 1 t, t * a n := Finset.mul_sum ..
    _ ≤ ∑ _n ∈ Ico 1 t, a t := Finset.sum_le_sum h
    _ = (t - 1) * a t := by rw [Finset.sum_const, smul_eq_mul, Nat.card_Ico]
    _ ≤ t * a t := Nat.mul_le_mul_right _ (Nat.sub_le t 1)

theorem main : H1 → H2 → type_of% @Erdos1160.erdos_1160.variants.sum := by
  rintro ⟨r, hr, hfar⟩ hfixed
  have hnear : ∀ᶠ k : ℕ in atTop, ∀ q ∈ Ico 1 (2 ^ r),
      2 ^ (k + r) * g (2 ^ k * q) ≤ g (2 ^ (k + r)) :=
    (eventually_all_finset _).2 fun q hq =>
      hfixed r q hr (mem_Ico.mp hq).1 (mem_Ico.mp hq).2
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hfar.and hnear)
  refine eventually_atTop.mpr ⟨K + r, fun m hm => ?_⟩
  let k := m - r
  have hk : K ≤ k := by dsimp [k]; omega
  have he : k + r = m := by dsimp [k]; omega
  obtain ⟨hbulk, hfinite⟩ := hK k hk
  rw [← he]
  apply sum_le_of_pointwise g _ (Nat.two_pow_pos _)
  intro n hn
  by_cases hd : 2 ^ k ∣ n
  · obtain ⟨q, rfl⟩ := hd
    obtain ⟨hpos, hlt⟩ := mem_Ico.mp hn
    have hq : 0 < q := by
      by_contra! hz
      simp [Nat.eq_zero_of_le_zero hz] at hpos
    rw [pow_add] at hlt
    exact hfinite q (mem_Ico.mpr ⟨hq, Nat.lt_of_mul_lt_mul_left hlt⟩)
  · exact hbulk n hn hd

open scoped Topology

/-- Direct application of the dyadic limit in Su and Xia, Theorem 1.1.
The ratio is the count through order 2^m divided by the endpoint count. -/
lemma sum_of_su_xia_limit
    (h : Tendsto (fun m : ℕ =>
      ((∑ n ∈ Icc 1 (2 ^ m), g n : ℕ) : ℝ) / (g (2 ^ m) : ℝ)) atTop (𝓝 1)) :
    type_of% @Erdos1160.erdos_1160.variants.sum := by
  have hlo := (tendsto_order.mp h).1 0 (by norm_num)
  have hhi := (tendsto_order.mp h).2 2 (by norm_num)
  filter_upwards [hlo, hhi] with m hpos hlt
  dsimp only at hpos hlt
  have hden : 0 < (g (2 ^ m) : ℝ) := by
    by_contra! hz
    have he : (g (2 ^ m) : ℝ) = 0 := le_antisymm hz (Nat.cast_nonneg _)
    simp [he] at hpos
  have hb := (div_lt_iff₀ hden).mp hlt
  rw [← Ico_insert_right (Nat.one_le_two_pow : 1 ≤ 2 ^ m),
    Finset.sum_insert Finset.right_notMem_Ico] at hb
  push_cast at hb
  exact_mod_cast (by linarith : ((∑ n ∈ Ico 1 (2 ^ m), g n : ℕ) : ℝ) ≤ (g (2 ^ m) : ℝ))

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3
