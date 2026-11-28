import OMAReductions.R_Erdos1052_erdos_1052_R3
import Mathlib

namespace OMA.Helpers

theorem upn1052_sum_all (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors.filter (fun d => d.Coprime (n / d)), d
      = (∑ i ∈ Erdos1052.properUnitaryDivisors n, i) + n := by
  have hset : n.divisors.filter (fun d => d.Coprime (n / d))
      = insert n (Erdos1052.properUnitaryDivisors n) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert,
      Erdos1052.properUnitaryDivisors, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hd, -⟩, hc⟩
      rcases (Nat.le_of_dvd hn hd).lt_or_eq with h | h
      · right; exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn, h⟩, hd, hc⟩
      · left; exact h
    · rintro (rfl | ⟨⟨_, _⟩, hd, hc⟩)
      · refine ⟨⟨dvd_rfl, hn.ne'⟩, ?_⟩
        rw [Nat.div_self hn]; exact Nat.coprime_one_right _
      · exact ⟨⟨hd, hn.ne'⟩, hc⟩
  rw [hset, Finset.sum_insert, add_comm]
  simp [Erdos1052.properUnitaryDivisors]

theorem upn1052_prod_ne_zero (n : ℕ) (T : Finset ℕ) (hT : T ⊆ n.primeFactors) :
    (∏ p ∈ T, p ^ n.factorization p) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ hp =>
    pow_ne_zero _ (Nat.mem_primeFactors.1 (hT hp)).1.ne_zero

theorem upn1052_sub_mem (n : ℕ) (hn : 0 < n) (T : Finset ℕ) (hT : T ⊆ n.primeFactors) :
    (∏ p ∈ T, p ^ n.factorization p) ∈ n.divisors.filter (fun d => d.Coprime (n / d)) := by
  have hn' : (∏ p ∈ n.primeFactors \ T, p ^ n.factorization p)
      * (∏ p ∈ T, p ^ n.factorization p) = n := by
    rw [Finset.prod_sdiff hT]
    exact (Nat.prod_primeFactors_pow_factorization hn.ne').symm
  have hd0 : 0 < ∏ p ∈ T, p ^ n.factorization p :=
    Nat.pos_of_ne_zero (upn1052_prod_ne_zero n T hT)
  have hdiv : n / (∏ p ∈ T, p ^ n.factorization p)
      = ∏ p ∈ n.primeFactors \ T, p ^ n.factorization p := by
    exact Nat.div_eq_of_eq_mul_left hd0 hn'.symm
  simp only [Finset.mem_filter, Nat.mem_divisors]
  refine ⟨⟨Dvd.intro_left _ hn', hn.ne'⟩, ?_⟩
  rw [hdiv]
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  rw [Finset.mem_sdiff] at hq
  have hpP := (Nat.mem_primeFactors.1 (hT hp)).1
  have hqP := (Nat.mem_primeFactors.1 hq.1).1
  apply Nat.Coprime.pow
  rw [Nat.coprime_primes hpP hqP]
  rintro rfl
  exact hq.2 hp

theorem upn1052_fact_ne (n p : ℕ) (hp : p ∈ n.primeFactors) : n.factorization p ≠ 0 := by
  have h := Nat.mem_primeFactors.1 hp
  exact (Nat.Prime.factorization_pos_of_dvd h.1 h.2.2 h.2.1).ne'

theorem upn1052_pf_prod (n : ℕ) (T : Finset ℕ) (hT : T ⊆ n.primeFactors) :
    (∏ p ∈ T, p ^ n.factorization p).primeFactors = T := by
  ext p
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hdvd, -⟩
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    have hqP := (Nat.mem_primeFactors.1 (hT hq)).1
    rw [(Nat.prime_dvd_prime_iff_eq hp hqP).1 (hp.dvd_of_dvd_pow hpq)]
    exact hq
  · intro hp
    have hpP := Nat.mem_primeFactors.1 (hT hp)
    refine ⟨hpP.1, ?_, upn1052_prod_ne_zero n T hT⟩
    exact dvd_trans (dvd_pow_self p (upn1052_fact_ne n p (hT hp)))
      (Finset.dvd_prod_of_mem _ hp)

theorem upn1052_right_inv (n : ℕ) (hn : 0 < n) (d : ℕ)
    (hd : d ∈ n.divisors.filter (fun d => d.Coprime (n / d))) :
    ∏ p ∈ d.primeFactors, p ^ n.factorization p = d := by
  simp only [Finset.mem_filter, Nat.mem_divisors] at hd
  obtain ⟨⟨hd, -⟩, hc⟩ := hd
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn.ne' hd
  have hq0 : n / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn hd) (Nat.pos_of_ne_zero hd0)).ne'
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hd0]
  apply Finset.prod_congr rfl
  intro p hp
  have hp' := Nat.mem_primeFactors.1 hp
  have hnd : n = d * (n / d) := (Nat.mul_div_cancel' hd).symm
  have hz : (n / d).factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    have := Nat.dvd_gcd hp'.2.1 h
    rw [Nat.Coprime.gcd_eq_one hc] at this
    exact hp'.1.not_dvd_one this
  have h2 : n.factorization p = d.factorization p := by
    conv_lhs => rw [hnd]
    rw [Nat.factorization_mul hd0 hq0, Finsupp.add_apply, hz, add_zero]
  rw [h2]

theorem upn1052_sum_eq_prod (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors.filter (fun d => d.Coprime (n / d)), d
      = ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) := by
  rw [Finset.prod_one_add]
  symm
  apply Finset.sum_nbij' (fun T => ∏ p ∈ T, p ^ n.factorization p) (fun d => d.primeFactors)
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact upn1052_sub_mem n hn T hT
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    rw [Finset.mem_powerset]
    exact Nat.primeFactors_mono hd.1.1 hn.ne'
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact upn1052_pf_prod n T hT
  · intro d hd
    exact upn1052_right_inv n hn d hd
  · intro T _
    rfl

theorem upn1052_formula (n : ℕ) (h : Erdos1052.IsUnitaryPerfect n) :
    ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) = 2 * n := by
  rw [← upn1052_sum_eq_prod n h.2, upn1052_sum_all n h.2, h.1]
  ring

theorem upn1052_card (n : ℕ) (hn : 0 < n)
    (h : ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) = 2 * n) :
    n.primeFactors.card ≤ padicValNat 2 n + 2 := by
  have hdvd : 2 ^ (n.primeFactors.erase 2).card ∣ 2 * n := by
    rw [← h]
    calc 2 ^ (n.primeFactors.erase 2).card = ∏ p ∈ n.primeFactors.erase 2, 2 := by
          rw [Finset.prod_const]
      _ ∣ ∏ p ∈ n.primeFactors.erase 2, (1 + p ^ n.factorization p) := by
          apply Finset.prod_dvd_prod_of_dvd
          intro p hp
          have hp2 := Finset.ne_of_mem_erase hp
          have hpp := (Nat.mem_primeFactors.1 (Finset.mem_of_mem_erase hp)).1
          have hodd : Odd p := hpp.eq_two_or_odd'.resolve_left hp2
          exact even_iff_two_dvd.1 (Odd.add_odd odd_one (hodd.pow))
      _ ∣ ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) :=
          Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset _ _)
  have hle : (n.primeFactors.erase 2).card ≤ padicValNat 2 (2 * n) :=
    (padicValNat_dvd_iff_le (by omega)).1 hdvd
  rw [padicValNat.mul (by norm_num) hn.ne', padicValNat.self (by norm_num)] at hle
  have := Finset.pred_card_le_card_erase (s := n.primeFactors) (a := 2)
  omega

theorem upn1052_pow_bound (x : ℚ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    (1 + x) ^ k ≤ 1 + (2 ^ k - 1) * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2k : (1 : ℚ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    calc (1 + x) ^ (k + 1) = (1 + x) ^ k * (1 + x) := pow_succ _ _
      _ ≤ (1 + (2 ^ k - 1) * x) * (1 + x) := mul_le_mul_of_nonneg_right ih (by linarith)
      _ ≤ 1 + (2 ^ (k + 1) - 1) * x := by
          rw [pow_succ]
          nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h2k) h0) (sub_nonneg.2 h1)]

theorem upn1052_finite (r : ℕ) : ∀ ρ : ℚ,
    {s : Finset ℕ | s.card = r ∧ (∀ q ∈ s, 2 ≤ q) ∧ ∏ q ∈ s, (1 + 1 / (q : ℚ)) = ρ}.Finite := by
  induction r with
  | zero =>
    intro ρ
    apply (Set.finite_singleton (∅ : Finset ℕ)).subset
    rintro s ⟨hs, -, -⟩
    rw [Set.mem_singleton_iff]
    exact Finset.card_eq_zero.1 hs
  | succ r ih =>
    intro ρ
    apply (Set.Finite.biUnion (Set.finite_le_nat ⌈(2 : ℚ) ^ (r + 1) / (ρ - 1)⌉₊)
      (fun m _ => (ih (ρ / (1 + 1 / (m : ℚ)))).image (insert m))).subset
    rintro s ⟨hs, h2, hprod⟩
    have hne : s.Nonempty := Finset.card_pos.1 (by omega)
    have hms : s.min' hne ∈ s := Finset.min'_mem s hne
    have hmin : ∀ q ∈ s, s.min' hne ≤ q := fun q hq => Finset.min'_le s q hq
    have hm2 : 2 ≤ s.min' hne := h2 _ hms
    have hmq : (0 : ℚ) < (s.min' hne : ℕ) := by exact_mod_cast (by omega : 0 < s.min' hne)
    have hf : (0 : ℚ) < 1 + 1 / ((s.min' hne : ℕ) : ℚ) := by positivity
    have hsplit : ∏ q ∈ s, (1 + 1 / (q : ℚ))
        = (1 + 1 / ((s.min' hne : ℕ) : ℚ)) * ∏ q ∈ s.erase (s.min' hne), (1 + 1 / (q : ℚ)) :=
      (Finset.mul_prod_erase s _ hms).symm
    have hrest1 : (1 : ℚ) ≤ ∏ q ∈ s.erase (s.min' hne), (1 + 1 / (q : ℚ)) := by
      have := Finset.prod_le_prod (s := s.erase (s.min' hne)) (f := fun _ : ℕ => (1 : ℚ))
        (g := fun q : ℕ => 1 + 1 / (q : ℚ)) (fun _ _ => zero_le_one)
        (fun q _ => by simp only [le_add_iff_nonneg_right]; positivity)
      simpa using this
    have hupper : ρ ≤ (1 + 1 / ((s.min' hne : ℕ) : ℚ)) ^ (r + 1) := by
      rw [← hprod, ← hs, ← Finset.prod_const]
      apply Finset.prod_le_prod (fun q _ => by positivity) (fun q hq => ?_)
      have hle : ((s.min' hne : ℕ) : ℚ) ≤ q := by exact_mod_cast hmin q hq
      have hq0 : (0 : ℚ) < q := lt_of_lt_of_le hmq hle
      have : 1 / (q : ℚ) ≤ 1 / ((s.min' hne : ℕ) : ℚ) := one_div_le_one_div_of_le hmq hle
      linarith
    have hx0 : (0 : ℚ) < 1 / ((s.min' hne : ℕ) : ℚ) := by positivity
    have hx1 : 1 / ((s.min' hne : ℕ) : ℚ) ≤ 1 := by
      rw [div_le_one hmq]; exact_mod_cast (by omega : 1 ≤ s.min' hne)
    have hbern := upn1052_pow_bound _ hx0.le hx1 (r + 1)
    have hρ1 : 1 < ρ := by
      rw [← hprod, hsplit]; nlinarith
    have hmB : s.min' hne ≤ ⌈(2 : ℚ) ^ (r + 1) / (ρ - 1)⌉₊ := by
      have key : ρ - 1 ≤ 2 ^ (r + 1) * (1 / ((s.min' hne : ℕ) : ℚ)) := by nlinarith
      rw [mul_one_div, le_div_iff₀ hmq] at key
      have : ((s.min' hne : ℕ) : ℚ) ≤ 2 ^ (r + 1) / (ρ - 1) := by
        rw [le_div_iff₀ (by linarith)]; linarith
      exact_mod_cast this.trans (Nat.le_ceil _)
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq]
    refine ⟨s.min' hne, hmB, s.erase (s.min' hne), ⟨?_, ?_, ?_⟩, Finset.insert_erase hms⟩
    · rw [Finset.card_erase_of_mem hms, hs]; rfl
    · intro q hq; exact h2 q (Finset.mem_of_mem_erase hq)
    · rw [eq_div_iff hf.ne', mul_comm, ← hsplit, hprod]

theorem upn1052_injOn (n : ℕ) :
    Set.InjOn (fun p => p ^ n.factorization p) n.primeFactors := by
  intro p hp q hq hpq
  have hp' := Nat.mem_primeFactors.1 hp
  have hq' := Nat.mem_primeFactors.1 hq
  have : p ∣ q ^ n.factorization q := by
    have h0 : p ∣ p ^ n.factorization p := dvd_pow_self p (upn1052_fact_ne n p hp)
    simp only at hpq
    rwa [hpq] at h0
  exact (Nat.prime_dvd_prime_iff_eq hp'.1 hq'.1).1 (hp'.1.dvd_of_dvd_pow this)

theorem upn1052_ratio (n : ℕ) (hn : 0 < n)
    (h : ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) = 2 * n) :
    ∏ p ∈ n.primeFactors, (1 + 1 / (((p ^ n.factorization p : ℕ)) : ℚ)) = 2 := by
  have h1 : ∏ p ∈ n.primeFactors, (((1 + p ^ n.factorization p : ℕ)) : ℚ) = 2 * n := by
    rw [← Nat.cast_prod, h]; push_cast; ring
  have h2 : ∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ)) : ℚ) = n := by
    rw [← Nat.cast_prod, ← Nat.prod_primeFactors_pow_factorization hn.ne']
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  calc ∏ p ∈ n.primeFactors, (1 + 1 / (((p ^ n.factorization p : ℕ)) : ℚ))
      = ∏ p ∈ n.primeFactors, ((((1 + p ^ n.factorization p : ℕ)) : ℚ)
          / (((p ^ n.factorization p : ℕ)) : ℚ)) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hx : (((p ^ n.factorization p : ℕ)) : ℚ) ≠ 0 := by
          exact_mod_cast pow_ne_zero _ (Nat.mem_primeFactors.1 hp).1.ne_zero
        rw [Nat.cast_add (1 : ℕ), Nat.cast_one, add_div, div_self hx]
        ring
    _ = (∏ p ∈ n.primeFactors, (((1 + p ^ n.factorization p : ℕ)) : ℚ))
          / ∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ)) : ℚ) :=
        Finset.prod_div_distrib _ _
    _ = 2 := by rw [h1, h2, mul_div_assoc, div_self hn0, mul_one]

theorem upn1052_main : OMA.R_Erdos1052_erdos_1052_R3.H1 := by
  intro A
  have hprodQ : ∀ n : ℕ, n ≠ 0 →
      ∏ q ∈ n.primeFactors.image (fun p => p ^ n.factorization p), q = n := by
    intro n hn
    rw [Finset.prod_image (upn1052_injOn n)]
    exact (Nat.prod_primeFactors_pow_factorization hn).symm
  apply Set.Finite.of_finite_image
    (f := fun n : ℕ => n.primeFactors.image (fun p => p ^ n.factorization p))
  · apply (Set.Finite.biUnion (Set.finite_le_nat (A + 2))
      (fun r _ => upn1052_finite r 2)).subset
    rintro _ ⟨n, ⟨hup, hA⟩, rfl⟩
    have hn := hup.2
    have hform := upn1052_formula n hup
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨(n.primeFactors.image (fun p => p ^ n.factorization p)).card, ?_, rfl, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn (upn1052_injOn n)]
      have := upn1052_card n hn hform
      omega
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      have hpp := (Nat.mem_primeFactors.1 hp).1
      exact hpp.two_le.trans (Nat.le_self_pow (upn1052_fact_ne n p hp) p)
    · rw [Finset.prod_image (upn1052_injOn n)]
      exact upn1052_ratio n hn hform
  · intro n hn m hm hnm
    simp only at hnm
    rw [← hprodQ n hn.1.2.ne', ← hprodQ m hm.1.2.ne', hnm]

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R3.H1 := OMA.Helpers.upn1052_main
