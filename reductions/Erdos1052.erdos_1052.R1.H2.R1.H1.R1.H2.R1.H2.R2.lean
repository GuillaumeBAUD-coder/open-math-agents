import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1

/-!
A Graham chain bound forces 3 to be a simple prime. Its unique source is
then a simple prime q with 3 dividing q + 1. The two steps ask for a bound
on the source and for a bound on the 2-adic exponent with the source fixed.
The Graham path and Mersenne estimates and the 5-adic budget come from
adammcarter's earlier reductions.
-/
namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R2

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1

-- Bound the supplying prime uniformly over admissible perfect numbers.
def H1 : Prop := ∃ Q : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 4 →
    Even (padicValNat 2 n) → 128 ≤ padicValNat 2 n →
    (∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    ∀ q : ℕ, q.Prime → q ∣ n → q ≠ 2 → q ≠ 5 → 3 ∣ q + 1 → q ≤ Q

-- Bound the 2-adic exponent after the supplying prime q is fixed.
def H2 : Prop := ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 5 → 3 ∣ q + 1 →
    ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 4 →
    Even (padicValNat 2 n) → 128 ≤ padicValNat 2 n →
    (∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    q ∣ n → padicValNat 2 n ≤ A

theorem three_present {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 10 ≤ m) : 3 ∈ P := by
  by_contra h3
  let β : ℕ → ℚ := fun p => if p = 3 then 1 else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  have hβ p (hp : p ∈ P) : β p = ((p : ℚ) + 1) / ((p : ℚ) - 1) :=
    by simp [β, (show p ≠ 3 from fun he => h3 (he ▸ hp))]
  have hB p (hp : p ∈ P) : 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    rw [hβ p hp]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  have h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127 := by norm_num [β]
  obtain ⟨S1, -, S2, -, -, -, -, -⟩ := facts hP (hK5 4) E
  obtain ⟨g, hg⟩ := exists_child ({5} : Finset ℕ)
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  have hβpos : ∀ p ∈ P, 0 < β p := fun p hp => by
    have h0 : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
    linarith [(hB p hp).1]
  have hg1 : ∀ p ∈ P, g p ∈ P → g p ≠ 1 := fun p _ h h1 => by
    have := (hP _ h).1
    rw [h1] at this
    exact Nat.not_prime_one this
  have hgP : ∀ p ∈ P, g p ≠ 1 → g p ∈ P := fun p hp h =>
    S1 _ ((hg p).2.2.1 h).1 ((hg p).2.2.1 h).2.1 ((hg p).2.2.1 h).2.2 p hp (hg p).1
  have hpath := path_bound g β P.card P rfl hpos
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      have := two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1
      have := hc.1.two_le
      omega)
    (fun p hp p' hp' h he => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      exact S2 _ hc.1 hc.2.1 hc.2.2 p hp p' hp' (hg p).1 (he ▸ (hg p').1))
    (fun p hp => (hB p hp).1)
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      rw [hβ (g p) h, hβ p hp]
      exact B_step hc.1.two_le (two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1))
  -- a path starts at a prime q such that every odd prime factor of q + 1 lies in N
  have hleaf : ∀ q ∈ P.filter (fun q => g q ∉ P),
      ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ ({5} : Finset ℕ) := fun q hq => by
    obtain ⟨hqP, hgq⟩ := Finset.mem_filter.mp hq
    by_cases h : g q = 1
    · exact (hg q).2.1 h
    · exact absurd (hgP q hqP h) hgq
  have hLP : ∀ q ∈ P.filter (fun q => g q ∉ P), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  have hsplit := Finset.prod_filter_mul_prod_filter_not (P.filter (fun q => g q ∉ P))
    (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1) β
  let L := (P.filter (fun q => g q ∉ P)).filter
      (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1)
  have hsub : L ⊆ P := fun _ h => hLP _ (Finset.mem_filter.mp h).1
  have hdiv q (hq : q ∈ L) : 5 ∣ q + 1 := by
    obtain ⟨hqL, hn⟩ := Finset.mem_filter.mp hq
    obtain ⟨c, hc, hd⟩ := Nat.exists_prime_and_dvd hn
    have hcd := hd.trans (Nat.ordCompl_dvd (q + 1) 2)
    have hc2 : c ≠ 2 := fun he => Nat.not_dvd_ordCompl Nat.prime_two (Nat.succ_ne_zero q) (he ▸ hd)
    have he := Finset.mem_singleton.mp (hleaf q hqL c hc hc2 hcd)
    rwa [he] at hcd
  have hcard : L.card ≤ 4 := by
    by_contra hh
    have hd := Finset.prod_dvd_prod_of_dvd (s := L) (fun _ => 5) (fun q => q+1) hdiv
    rw [Finset.prod_const] at hd
    have hd5 := (pow_dvd_pow 5 (show 5 ≤ L.card by omega)).trans hd
    exact kill_v5 hP h5 E (one_dvd _) hsub (dvd_mul_of_dvd_right hd5 _)
  have hsmall q (hq : q ∈ L) : q = 19 ∨ 29 ≤ q := by
    have hqP := (hP q (hsub hq)).1
    have hd := hdiv q hq
    by_contra! hbad
    obtain ⟨hne, hlt⟩ := hbad
    have finiteCheck : ∀ i : Fin 29, i.val.Prime → 5 ∣ i.val+1 → i.val=19 := by decide
    exact hne (finiteCheck ⟨q,hlt⟩ hqP hd)
  have hγ q (hq : q ∈ L) (h19 : q ≠ 19) : β q ≤ 15/14 := by
    rw [hβ _ (hsub hq)]
    have hh := B_anti (a := 29) (by norm_num) ((hsmall q hq).resolve_left h19)
    norm_num at hh ⊢
    exact hh
  have hzleaves : ∏ q ∈ L, β q ≤ (10/9 : ℚ) * (15/14)^3 := by
    by_cases h19 : 19 ∈ L
    · rw [← Finset.mul_prod_erase L β h19]
      have hb := Finset.prod_le_prod (g := fun _ => (15/14 : ℚ))
        (fun q hq => (hβpos q (hsub (Finset.mem_of_mem_erase hq))).le)
        (fun q hq => hγ q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq))
      rw [Finset.prod_const] at hb
      have hc := Finset.card_erase_of_mem h19
      have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 15/14)
        (show (L.erase 19).card ≤ 3 by omega)
      have hw : β 19 = 10/9 := by norm_num [β]
      rw [hw]
      exact mul_le_mul_of_nonneg_left (hb.trans hpow) (by norm_num)
    · have hb := Finset.prod_le_prod (g := fun _ => (15/14 : ℚ))
        (fun q hq => (hβpos q (hsub hq)).le)
        (fun q hq => hγ q hq (fun h => h19 (h ▸ hq)))
      rw [Finset.prod_const] at hb
      exact (hb.trans (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 15/14) hcard)).trans (by norm_num)
  have hmleaves : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter
        (fun q => ¬ (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    refine mersenne_bound β _ (fun q hq => (hP q (hLP q (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => ?_)
      (fun q hq => ⟨hβpos q (hLP q (Finset.mem_filter.mp hq).1),
        (hB q (hLP q (Finset.mem_filter.mp hq).1)).2⟩) h1
    obtain ⟨hqL, hzd⟩ := Finset.mem_filter.mp hq
    have h1' : (q + 1) / 2 ^ (q + 1).factorization 2 = 1 := not_not.mp hzd
    have hmul := Nat.ordProj_mul_ordCompl_eq_self (q + 1) 2
    rw [h1', mul_one] at hmul
    exact ⟨(q + 1).factorization 2, hmul.symm⟩
  have hpL := mul_le_mul hzleaves hmleaves
    (Finset.prod_nonneg fun q hq => (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le)
    (by norm_num : 0 ≤ (10/9 : ℚ) * (15/14)^3)
  unfold L at hpL
  rw [hsplit] at hpL
  have hp := hpath.trans hpL
  norm_num [β] at hp
  have hEq : (1 + 1 / (2 : ℚ) ^ m) * ((626 : ℚ) / 625) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
    have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) :=
      Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
    have hcast : ((2 : ℚ) ^ m + 1) * 626 * ∏ p ∈ P, ((p : ℚ) + 1) =
        2 ^ (m + 1) * 625 * ∏ p ∈ P, (p : ℚ) := by
      have h := congrArg (Nat.cast : ℕ → ℚ) E
      push_cast at h
      exact h
    have e : ∏ p ∈ P, (1 + 1 / (p : ℚ)) = (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have : (0 : ℚ) < p := by exact_mod_cast hpos p hp
      field_simp
    have h2 : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
    rw [e]
    field_simp
    rw [pow_succ] at hcast
    linarith
  have hT : 1 + 1 / (2 : ℚ) ^ m ≤ 1025 / 1024 := by
    have h2 : (2 : ℚ) ^ 10 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have : 1 / (2 : ℚ) ^ m ≤ 1 / (2 : ℚ) ^ 10 := one_div_le_one_div_of_le (by positivity) h2
    norm_num at this ⊢
    linarith
  have ht := mul_le_mul (mul_le_mul_of_nonneg_right hT (by norm_num : (0 : ℚ) ≤ 626/625))
    hp (Finset.prod_nonneg fun p _ => by positivity) (by norm_num)
  norm_num [one_div] at hEq ht
  linarith only [hEq, ht]

theorem source_exists {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (hEven : Even m) : ∃ q ∈ P, 3 ∣ q + 1 := by
  have h3 := three_present hP h5 E hm
  have hd : 3 ∣ 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p :=
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ h3) _
  rw [← E] at hd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with hx | hx
  · rcases Nat.prime_three.dvd_mul.mp hx with hy | hy
    · obtain ⟨t, rfl⟩ := hEven
      have he : (2:ℕ)^(t+t) = 4^t := by rw [← two_mul, pow_mul]; norm_num
      have hc : (4:ℕ)^t ≡ 1 [MOD 3] :=
        (show (4:ℕ) ≡ 1 [MOD 3] by decide).pow t |>.trans (by rw [one_pow])
      rw [he] at hy
      change 4^t % 3 = 1 at hc
      omega
    · norm_num at hy
  · exact (Prime.dvd_finsetProd_iff Nat.prime_three.prime _).mp hx

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.H2 := by
  intro h1 h2
  obtain ⟨Q, hQ⟩ := h1
  classical
  let A (q : ℕ) : ℕ := if h : q.Prime ∧ q ≠ 2 ∧ q ≠ 5 ∧ 3 ∣ q+1 then
    (h2 q h.1 h.2.1 h.2.2.1 h.2.2.2).choose else 0
  refine ⟨(Finset.range (Q+1)).sup A, fun n hn hs he hev hbig hr => ?_⟩
  obtain ⟨hp, h5, E⟩ := setup hn hs
  rw [he] at E
  obtain ⟨q, hq, hq3⟩ := source_exists hp h5 E (by omega) hev
  obtain ⟨hpf, hq5⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq2, hqn⟩ := Finset.mem_erase.mp hpf
  have hpr := Nat.prime_of_mem_primeFactors hqn
  have hd := Nat.dvd_of_mem_primeFactors hqn
  have hq5' : q ≠ 5 := by simpa using hq5
  have hqQ := hQ n hn hs he hev hbig hr q hpr hd hq2 hq5' hq3
  have hgood : q.Prime ∧ q ≠ 2 ∧ q ≠ 5 ∧ 3 ∣ q+1 := ⟨hpr,hq2,hq5',hq3⟩
  have hle : padicValNat 2 n ≤ A q := by
    simpa only [A, dif_pos hgood] using (h2 q hpr hq2 hq5' hq3).choose_spec n hn hs he hev hbig hr hd
  exact hle.trans (Finset.le_sup (Finset.mem_range.mpr (by omega : q < Q+1)))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R2
