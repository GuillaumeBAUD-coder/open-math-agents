import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R1
import Mathlib

/-!
Subbarao-Warren 2-adic exponent balance decomposition for unitary perfect numbers
whose odd powerful core is a single prime power distinct from 9.
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R1_H2_R2

def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    c.primeFactors.card = 1 → c ≠ 9 →
    ∃ M : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * ∏ p ∈ S, p →
      S.card ≤ M

def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    c.primeFactors.card = 1 → c ≠ 9 →
    ∃ V : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * ∏ p ∈ S, p →
      ∀ p ∈ S, (1 + p).factorization 2 ≤ V

lemma factorization_prod_apply {α : Type*} (s : Finset α) (f : α → ℕ)
    (hf : ∀ x ∈ s, f x ≠ 0) (p : ℕ) :
    (∏ x ∈ s, f x).factorization p = ∑ x ∈ s, (f x).factorization p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hx0 : f x ≠ 0 := hf x (Finset.mem_insert_self x s)
    have hs0 : ∏ y ∈ s, f y ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun y hy => hf y (Finset.mem_insert_of_mem hy))
    rw [Finset.prod_insert hx, Nat.factorization_mul hx0 hs0, Finsupp.add_apply,
      ih (fun y hy => hf y (Finset.mem_insert_of_mem hy)), Finset.sum_insert hx]

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R1.H2 := by
  intro h1 h2 c hc_odd hc_pow hc_card hc_ne9
  obtain ⟨M, hM⟩ := h1 c hc_odd hc_pow hc_card hc_ne9
  obtain ⟨V, hV⟩ := h2 c hc_odd hc_pow hc_card hc_ne9
  have hc_ne0 : c ≠ 0 := by
    rintro rfl
    simp at hc_odd
  have h2_not_dvd_c : ¬ 2 ∣ c := by
    intro hdvd
    obtain ⟨k, hk⟩ := hc_odd
    omega
  have h2_not_mem_c : 2 ∉ c.primeFactors := by
    intro hmem
    exact h2_not_dvd_c (Nat.dvd_of_mem_primeFactors hmem)
  have hc_fac2 : c.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd h2_not_dvd_c
  let C2 := ∑ q ∈ c.primeFactors, (1 + q ^ c.factorization q).factorization 2
  let B := C2 + M * V
  refine (Finset.range (B + 1)).finite_toSet.subset ?_
  intro a ha
  dsimp only at ha
  obtain ⟨ha5, S, hScard, hSsub, hSprime, heq⟩ := ha
  have hM_bound : S.card ≤ M := hM a S ha5 hScard hSsub hSprime heq
  have hV_bound : ∀ p ∈ S, (1 + p).factorization 2 ≤ V := hV a S ha5 hScard hSsub hSprime heq
  set b := 2 ^ a * c
  set u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
  have h2a_ne0 : (2 : ℕ) ^ a ≠ 0 := pow_ne_zero a (by decide)
  have hb_ne0 : b ≠ 0 := mul_ne_zero h2a_ne0 hc_ne0
  have ha_ne0 : a ≠ 0 := by omega
  have hb_pf : b.primeFactors = insert 2 c.primeFactors := by
    dsimp only [b]
    rw [Nat.primeFactors_mul h2a_ne0 hc_ne0, Nat.primeFactors_pow 2 ha_ne0,
      Nat.Prime.primeFactors Nat.prime_two, Finset.singleton_union]
  have hb_fac2 : b.factorization 2 = a := by
    dsimp only [b]
    rw [Nat.factorization_mul h2a_ne0 hc_ne0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same, hc_fac2, add_zero]
  have hb_fac_odd : ∀ q ∈ c.primeFactors, b.factorization q = c.factorization q := by
    intro q hq
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hq_ne2 : q ≠ 2 := fun h => h2_not_mem_c (h ▸ hq)
    have hq_not_dvd_2a : ¬ q ∣ 2 ^ a := by
      intro hdvd
      have hq_dvd_2 : q ∣ 2 := hq_prime.dvd_of_dvd_pow hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hq_dvd_2 with hq1 | hq2
      · exact hq_prime.ne_one hq1
      · exact hq_ne2 hq2
    dsimp only [b]
    rw [Nat.factorization_mul h2a_ne0 hc_ne0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hq_not_dvd_2a, zero_add]
  have hu_eq : u = (1 + 2 ^ a) * ∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q) := by
    dsimp only [u]
    rw [hb_pf, Finset.prod_insert h2_not_mem_c, hb_fac2]
    congr 1
    apply Finset.prod_congr rfl
    intro q hq
    rw [hb_fac_odd q hq]
  have h12a_ne0 : 1 + 2 ^ a ≠ 0 := by positivity
  have hprod_c_ne0 : (∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun _ _ => by positivity)
  have hu_ne0 : u ≠ 0 := by
    rw [hu_eq]
    exact mul_ne_zero h12a_ne0 hprod_c_ne0
  have hprod_S1_ne0 : (∏ p ∈ S, (1 + p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun _ _ => by positivity)
  have hprod_S_ne0 : (∏ p ∈ S, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => (hSprime p hp).1.ne_zero)
  have h2b_ne0 : 2 * b ≠ 0 := mul_ne_zero (by decide) hb_ne0
  have h2_dvd_b : 2 ∣ b := by
    dsimp only [b]
    refine dvd_mul_of_dvd_left ?_ c
    rw [show a = (a - 1) + 1 by omega, pow_succ']
    exact dvd_mul_right 2 _
  have h12a_fac2 : (1 + 2 ^ a).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    have h2_dvd_2a : 2 ∣ 2 ^ a := by
      rw [show a = (a - 1) + 1 by omega, pow_succ']
      exact dvd_mul_right 2 _
    have h2_dvd_1 : 2 ∣ 1 := (Nat.dvd_add_left h2_dvd_2a).mp hdvd
    omega
  have hlhs_fac2 : (u * ∏ p ∈ S, (1 + p)).factorization 2 =
      C2 + ∑ p ∈ S, (1 + p).factorization 2 := by
    rw [Nat.factorization_mul hu_ne0 hprod_S1_ne0, Finsupp.add_apply, hu_eq,
      Nat.factorization_mul h12a_ne0 hprod_c_ne0, Finsupp.add_apply, h12a_fac2, zero_add,
      factorization_prod_apply _ _ (fun _ _ => by positivity),
      factorization_prod_apply _ _ (fun _ _ => by positivity)]
  have hrhs_fac2 : ((2 * b) * ∏ p ∈ S, p).factorization 2 = a + 1 := by
    rw [Nat.factorization_mul h2b_ne0 hprod_S_ne0, Finsupp.add_apply,
      Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hb_ne0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, hb_fac2,
      factorization_prod_apply _ _ (fun p hp => (hSprime p hp).1.ne_zero)]
    have hsum0 : ∑ p ∈ S, p.factorization 2 = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      obtain ⟨hp_prime, hp_ndvd⟩ := hSprime p hp
      apply Nat.factorization_eq_zero_of_not_dvd
      intro h2_dvd_p
      rcases (Nat.dvd_prime hp_prime).mp h2_dvd_p with h1' | h2'
      · omega
      · subst h2'
        exact hp_ndvd h2_dvd_b
    rw [hsum0]
    omega
  have hv2_eq : C2 + ∑ p ∈ S, (1 + p).factorization 2 = a + 1 := by
    rw [← hlhs_fac2, heq, hrhs_fac2]
  have hsum_le : ∑ p ∈ S, (1 + p).factorization 2 ≤ M * V := by
    calc ∑ p ∈ S, (1 + p).factorization 2
        ≤ ∑ _p ∈ S, V := Finset.sum_le_sum hV_bound
      _ = S.card * V := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ M * V := Nat.mul_le_mul_right V hM_bound
  have ha_le : a ≤ B := by
    dsimp only [B]
    omega
  simp only [Finset.coe_range, Set.mem_Iio]
  omega

end OMA.R_Erdos1052_erdos_1052_R2_H2_R1_H2_R2
