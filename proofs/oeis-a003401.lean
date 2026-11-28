import OMAStatements.S_oeis_a003401

/-!
# Proof of OEIS A003401: reciprocal sum of constructible polygon orders

Assuming `F 0, …, F 4` are the only Fermat primes, an integer `n ≥ 1` has `φ(n)` a power of `2`
if and only if `n` has a unique representation `2^a * ∏ k ∈ S, F k` with `a : ℕ` and
`S : Finset (Fin 5)`. Factoring the reciprocal sum across `ℕ × Finset (Fin 5)` yields
`2 * ∏ k ∈ Finset.range 5, (1 + 1 / F k) = 4869735552 / 1431655765`.
-/

namespace OMA.S_oeis_a003401.Proof

open OMA.S_oeis_a003401

private lemma F_prime_of_lt_five {k : ℕ} (hk : k < 5) : (F k).Prime := by
  interval_cases k <;> norm_num [F]

private lemma F_strictMono : StrictMono F := by
  intro i j hij
  unfold F
  have h1 : 2 ^ i < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) hij
  have h2 : 2 ^ 2 ^ i < 2 ^ 2 ^ j := Nat.pow_lt_pow_right (by norm_num) h1
  omega

private lemma F_pos (k : ℕ) : 0 < F k := by
  unfold F
  positivity

private lemma F_coprime_two (k : ℕ) : Nat.Coprime 2 (F k) := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro h
  have h2 : 2 ∣ 2 ^ 2 ^ k := dvd_pow_self 2 (Nat.ne_of_gt (Nat.two_pow_pos k))
  have h1 : 2 ∣ 1 := (Nat.dvd_add_right h2).mp h
  omega

private lemma F_coprime_of_ne {i j : Fin 5} (hij : i ≠ j) : Nat.Coprime (F i) (F j) :=
  (Nat.coprime_primes (F_prime_of_lt_five i.isLt) (F_prime_of_lt_five j.isLt)).mpr
    fun h => hij (Fin.ext (F_strictMono.injective h))

private lemma add_one_dvd_pow_odd_add_one (b t : ℕ) :
    b + 2 ∣ (b + 1) ^ (2 * t + 1) + 1 := by
  induction t with
  | zero =>
    simp
  | succ t ih =>
    have hEq :
        (b + 1) ^ (2 * (t + 1) + 1) + 1 + b * (b + 2) =
          (b + 1) ^ 2 * ((b + 1) ^ (2 * t + 1) + 1) := by
      ring
    have hMul : b + 2 ∣ (b + 1) ^ 2 * ((b + 1) ^ (2 * t + 1) + 1) :=
      dvd_mul_of_dvd_right ih ((b + 1) ^ 2)
    rw [← hEq] at hMul
    exact (Nat.dvd_add_left (dvd_mul_left (b + 2) b)).mp hMul

private lemma prime_eq_F_of_sub_one_eq_two_pow {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p - 1 = 2 ^ m) : ∃ k : ℕ, p = F k := by
  have hp_ge : 1 ≤ p := hp.one_le
  have hp_eq : p = 2 ^ m + 1 := by omega
  have hm_ne : m ≠ 0 := by
    intro hm0
    rw [hm0] at hp_eq
    norm_num at hp_eq
    exact hp2 hp_eq
  set k : ℕ := m.factorization 2
  set d : ℕ := m / 2 ^ k
  have hm_eq : 2 ^ k * d = m := by
    simpa [k, d] using Nat.ordProj_mul_ordCompl_eq_self m 2
  have hd_not_dvd : ¬ 2 ∣ d := Nat.not_dvd_ordCompl Nat.prime_two hm_ne
  have hd_odd : d % 2 = 1 := by omega
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (by
    intro hd0
    rw [hd0, mul_zero] at hm_eq
    exact hm_ne hm_eq.symm)
  have hd_eq_one : d = 1 := by
    by_contra hd1
    have hd_ge : 3 ≤ d := by omega
    obtain ⟨t, ht⟩ : ∃ t : ℕ, d = 2 * t + 1 := ⟨d / 2, by omega⟩
    set a : ℕ := 2 ^ 2 ^ k
    have ha_ge : 2 ≤ a := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ 2 ^ k := Nat.pow_le_pow_right (by norm_num) this
    have hdiv : a + 1 ∣ p := by
      rw [hp_eq, ← hm_eq, pow_mul, ht]
      have h1 : a - 1 + 2 = a + 1 := by omega
      have h2 : a - 1 + 1 = a := by omega
      have hdvd := add_one_dvd_pow_odd_add_one (a - 1) t
      rw [h1, h2] at hdvd
      exact hdvd
    have hgt1 : 1 < a + 1 := by omega
    have hltp : a + 1 < p := by
      rw [hp_eq, ← hm_eq, pow_mul]
      have hpow : a ^ 1 < a ^ d := Nat.pow_lt_pow_right (by omega) (by omega)
      simpa [a] using Nat.add_lt_add_right hpow 1
    rcases hp.eq_one_or_self_of_dvd (a + 1) hdiv with h1 | h2 <;> omega
  refine ⟨k, ?_⟩
  rw [hp_eq, ← hm_eq, hd_eq_one, mul_one, F]

private lemma totient_prod_F (S : Finset (Fin 5)) :
    (∏ k ∈ S, F k).totient = 2 ^ (∑ k ∈ S, 2 ^ (k : ℕ)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    have hcop : Nat.Coprime (F k) (∏ j ∈ S, F j) :=
      Nat.Coprime.prod_right fun j hj => F_coprime_of_ne (fun h => hk (h ▸ hj))
    rw [Finset.prod_insert hk, Nat.totient_mul hcop, ih, Finset.sum_insert hk, pow_add]
    have htk : (F k).totient = 2 ^ 2 ^ (k : ℕ) := by
      rw [Nat.totient_prime (F_prime_of_lt_five k.isLt)]
      simp [F]
    rw [htk]

private lemma prod_F_pos (S : Finset (Fin 5)) : 0 < ∏ k ∈ S, F k :=
  Finset.prod_pos fun k _ => F_pos k

private lemma coprime_two_prod_F (S : Finset (Fin 5)) :
    Nat.Coprime 2 (∏ k ∈ S, F k) := by
  refine Nat.Coprime.prod_right fun k _ => F_coprime_two k

private lemma coprime_two_pow_prod_F (a : ℕ) (S : Finset (Fin 5)) :
    Nat.Coprime (2 ^ a) (∏ k ∈ S, F k) :=
  (coprime_two_prod_F S).pow_left a

private lemma inA003401_of_pair (a : ℕ) (S : Finset (Fin 5)) :
    InA003401 (2 ^ a * ∏ k ∈ S, F k) := by
  refine ⟨Nat.mul_pos (Nat.two_pow_pos a) (prod_F_pos S), ?_⟩
  rw [Nat.totient_mul (coprime_two_pow_prod_F a S), totient_prod_F]
  cases a with
  | zero =>
    refine ⟨∑ k ∈ S, 2 ^ (k : ℕ), ?_⟩
    simp
  | succ b =>
    refine ⟨b + ∑ k ∈ S, 2 ^ (k : ℕ), ?_⟩
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos b)]
    simp [pow_add]

private lemma factorization_two_pair (a : ℕ) (S : Finset (Fin 5)) :
    (2 ^ a * ∏ k ∈ S, F k).factorization 2 = a := by
  have h1 : (2 ^ a : ℕ) ≠ 0 := Nat.ne_of_gt (Nat.two_pow_pos a)
  have h2 : (∏ k ∈ S, F k) ≠ 0 := Nat.ne_of_gt (prod_F_pos S)
  rw [Nat.factorization_mul h1 h2, Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same]
  have hnotdvd : ¬ 2 ∣ ∏ k ∈ S, F k :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (coprime_two_prod_F S)
  rw [Nat.factorization_eq_zero_of_not_dvd hnotdvd, add_zero]

private lemma F_dvd_prod_F_iff {k : Fin 5} {S : Finset (Fin 5)} :
    F k ∣ ∏ j ∈ S, F j ↔ k ∈ S := by
  constructor
  · intro hd
    have hpk := (F_prime_of_lt_five k.isLt).prime
    obtain ⟨j, hjS, hkj⟩ := (hpk.dvd_finsetProd_iff (fun j : Fin 5 => F j)).mp hd
    have heq : F k = F j :=
      (Nat.prime_dvd_prime_iff_eq (F_prime_of_lt_five k.isLt) (F_prime_of_lt_five j.isLt)).mp hkj
    have hkj' : k = j := Fin.ext (F_strictMono.injective heq)
    exact hkj' ▸ hjS
  · intro hk
    exact Finset.dvd_prod_of_mem (fun j : Fin 5 => F j) hk

private lemma pair_injective :
    Function.Injective (fun p : ℕ × Finset (Fin 5) => 2 ^ p.1 * ∏ k ∈ p.2, F k) := by
  rintro ⟨a₁, S₁⟩ ⟨a₂, S₂⟩ h
  have ha : a₁ = a₂ := by
    have hf := congrArg (fun n => n.factorization 2) h
    simpa [factorization_two_pair] using hf
  subst ha
  have hprod : ∏ k ∈ S₁, F k = ∏ k ∈ S₂, F k :=
    Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a₁) h
  have hS : S₁ = S₂ := by
    ext k
    rw [← F_dvd_prod_F_iff, ← F_dvd_prod_F_iff, hprod]
  exact Prod.ext rfl hS

private lemma exists_pair_of_inA003401
    (hF : ∀ k : ℕ, 5 ≤ k → ¬ (F k).Prime) {n : ℕ} (hn : InA003401 n) :
    ∃ p : ℕ × Finset (Fin 5), 2 ^ p.1 * ∏ k ∈ p.2, F k = n := by
  rcases hn with ⟨hn1, j, htot⟩
  have hn0 : n ≠ 0 := by omega
  have hodd_prime : ∀ p : ℕ, p.Prime → p ∣ n → p ≠ 2 →
      n.factorization p = 1 ∧ ∃ k : Fin 5, p = F k := by
    intro p hp hpn hp2
    have hcop : Nat.Coprime (p ^ n.factorization p) (n / p ^ n.factorization p) :=
      (Nat.coprime_ordCompl hp hn0).pow_left (n.factorization p)
    have hsplit : p ^ n.factorization p * (n / p ^ n.factorization p) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n p
    have hdvd_tot : (p ^ n.factorization p).totient ∣ 2 ^ j := by
      have hmul_tot :
          n.totient = (p ^ n.factorization p).totient * (n / p ^ n.factorization p).totient := by
        rw [← Nat.totient_mul hcop, hsplit]
      rw [← htot, hmul_tot]
      exact dvd_mul_right (p ^ n.factorization p).totient (n / p ^ n.factorization p).totient
    have he_pos : 0 < n.factorization p := by
      have : 1 ≤ n.factorization p := (hp.dvd_iff_one_le_factorization hn0).mp hpn
      omega
    have htot_pow : (p ^ n.factorization p).totient = p ^ (n.factorization p - 1) * (p - 1) :=
      Nat.totient_prime_pow hp he_pos
    rw [htot_pow] at hdvd_tot
    have he1 : n.factorization p = 1 := by
      by_contra hne1
      have hge1 : 1 ≤ n.factorization p - 1 := by omega
      have hp_dvd_pow : p ∣ 2 ^ j :=
        dvd_trans (dvd_pow_self p (by omega)) (dvd_trans (dvd_mul_right _ _) hdvd_tot)
      have hp_dvd_two : p ∣ 2 := hp.dvd_of_dvd_pow hp_dvd_pow
      rcases Nat.prime_two.eq_one_or_self_of_dvd p hp_dvd_two with h1 | h2
      · exact hp.ne_one h1
      · exact hp2 h2
    have hpm_dvd : p - 1 ∣ 2 ^ j := dvd_trans (dvd_mul_left _ _) hdvd_tot
    obtain ⟨m, -, hpm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hpm_dvd
    obtain ⟨k, hk⟩ := prime_eq_F_of_sub_one_eq_two_pow hp hp2 hpm
    have hk5 : k < 5 := by
      by_contra hge5
      exact hF k (by omega) (hk ▸ hp)
    exact ⟨he1, ⟨⟨k, hk5⟩, hk⟩⟩
  set a : ℕ := n.factorization 2
  set m : ℕ := n / 2 ^ a
  set S : Finset (Fin 5) := Finset.univ.filter fun k : Fin 5 => F k ∣ n
  have hm_split : 2 ^ a * m = n := by
    simpa [a, m] using Nat.ordProj_mul_ordCompl_eq_self n 2
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, mul_zero] at hm_split
    exact hn0 hm_split.symm
  have hm_dvd_n : m ∣ n := ⟨2 ^ a, by linarith⟩
  have hnot2m : ¬ 2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two hn0
  have hm_fact : ∀ p ∈ m.primeFactors, m.factorization p = 1 := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := fun h => hnot2m (h ▸ hpm)
    have hpn : p ∣ n := dvd_trans hpm hm_dvd_n
    have hnp1 : n.factorization p = 1 := (hodd_prime p hpp hpn hp2).1
    have h2_fact : (2 ^ a).factorization p = 0 := by
      rw [Nat.Prime.factorization_pow Nat.prime_two]
      simp [hp2]
    have hmul : n.factorization p = (2 ^ a).factorization p + m.factorization p := by
      rw [← hm_split, Nat.factorization_mul (Nat.ne_of_gt (Nat.two_pow_pos a)) hm0,
        Finsupp.add_apply]
    omega
  have hm_pf : m.primeFactors = S.image (fun k : Fin 5 => F k) := by
    ext p
    simp only [Nat.mem_primeFactors, Finset.mem_image, S, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hpp, hpm, -⟩
      have hp2 : p ≠ 2 := fun h => hnot2m (h ▸ hpm)
      have hpn : p ∣ n := dvd_trans hpm hm_dvd_n
      obtain ⟨k, hk⟩ := (hodd_prime p hpp hpn hp2).2
      exact ⟨k, hk ▸ hpn, hk.symm⟩
    · rintro ⟨k, hkn, rfl⟩
      refine ⟨F_prime_of_lt_five k.isLt, ?_, hm0⟩
      have hcop : Nat.Coprime (F k) (2 ^ a) := (F_coprime_two k).symm.pow_right a
      rw [← hm_split] at hkn
      exact hcop.dvd_of_dvd_mul_left hkn
  have hm_eq : m = ∏ k ∈ S, F k := by
    have hfp := Nat.prod_factorization_pow_eq_self hm0
    rw [Finsupp.prod, Nat.support_factorization] at hfp
    calc m = ∏ p ∈ m.primeFactors, p ^ (m.factorization p) := hfp.symm
      _ = ∏ p ∈ m.primeFactors, p := by
        refine Finset.prod_congr rfl fun p hp => ?_
        rw [hm_fact p hp, pow_one]
      _ = ∏ p ∈ S.image (fun k : Fin 5 => F k), p := by rw [hm_pf]
      _ = ∏ k ∈ S, F k := by
        rw [Finset.prod_image]
        intro i _ j _ hij
        exact Fin.ext (F_strictMono.injective hij)
  refine ⟨(a, S), ?_⟩
  rw [← hm_eq, hm_split]

private lemma sum_prod_one_add {n : ℕ} (g : ℕ → ℝ) :
    (∑ S : Finset (Fin n), ∏ k ∈ S, g k) =
      ∏ k ∈ Finset.range n, (1 + g k) := by
  have h1 :
      ∏ k : Fin n, (1 + g k) =
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, ∏ k ∈ S, g k :=
    Finset.prod_one_add (Finset.univ : Finset (Fin n))
  rw [Finset.powerset_univ] at h1
  rw [← h1]
  exact Fin.prod_univ_eq_prod_range (fun k : ℕ => 1 + g k) n

private lemma summand_eq (a : ℕ) (S : Finset (Fin 5)) :
    (1 : ℝ) / ((2 ^ a * ∏ k ∈ S, F k : ℕ) : ℝ) =
      ((1 : ℝ) / 2) ^ a * ∏ k ∈ S, (1 : ℝ) / (F k : ℝ) := by
  push_cast
  simp only [one_div, mul_inv, inv_pow, Finset.prod_inv_distrib]

private lemma hasSum_mul_right_real {f : ℕ → ℝ} {A : ℝ} (hf : HasSum f A) (c : ℝ) :
    HasSum (fun a : ℕ => f a * c) (A * c) := by
  change Filter.Tendsto (fun s : Finset ℕ => ∑ a ∈ s, f a * c) Filter.atTop (nhds (A * c))
  have h1 : Filter.Tendsto (fun s : Finset ℕ => (∑ a ∈ s, f a) * c) Filter.atTop (nhds (A * c)) :=
    ((continuous_mul_const c).tendsto A).comp hf
  refine h1.congr fun s => ?_
  exact Finset.sum_mul s f c

private lemma hasSum_prod_of_fintype {β : Type*} [Fintype β] [DecidableEq β]
    {f : ℕ → ℝ} {A : ℝ} (hf : HasSum f A) (g : β → ℝ) :
    HasSum (fun p : ℕ × β => f p.1 * g p.2) (A * ∑ b : β, g b) := by
  have hterm : ∀ b ∈ (Finset.univ : Finset β),
      HasSum (fun p : ℕ × β => if p.2 = b then f p.1 * g b else 0) (A * g b) := by
    intro b _
    have hinj : Function.Injective (fun a : ℕ => (a, b)) :=
      fun a₁ a₂ h => (Prod.mk.inj h).1
    have hsupp : ∀ p : ℕ × β, p ∉ Set.range (fun a : ℕ => (a, b)) →
        (if p.2 = b then f p.1 * g b else 0) = 0 := by
      intro ⟨a, b'⟩ hp
      have hne : b' ≠ b := by
        intro heq
        exact hp ⟨a, by simp [heq]⟩
      simp [hne]
    refine (hinj.hasSum_iff hsupp).mp ?_
    have hcomp :
        ((fun p : ℕ × β => if p.2 = b then f p.1 * g b else 0) ∘ fun a : ℕ => (a, b)) =
          fun a : ℕ => f a * g b := by
      funext a
      simp
    rw [hcomp]
    exact hasSum_mul_right_real hf (g b)
  have hsum := hasSum_sum hterm
  have hlhs :
      (fun p : ℕ × β => ∑ b ∈ (Finset.univ : Finset β), if p.2 = b then f p.1 * g b else 0) =
        fun p : ℕ × β => f p.1 * g p.2 := by
    funext ⟨a, b⟩
    simp
  have hrhs : (∑ b ∈ (Finset.univ : Finset β), A * g b) = A * ∑ b : β, g b :=
    (Finset.mul_sum Finset.univ g A).symm
  rw [hlhs, hrhs] at hsum
  exact hsum

private lemma hasSum_prod_geometric {n : ℕ} (g : ℕ → ℝ) :
    HasSum
      (fun p : ℕ × Finset (Fin n) => ((1 : ℝ) / 2) ^ p.1 * ∏ k ∈ p.2, g k)
      (2 * ∏ k ∈ Finset.range n, (1 + g k)) := by
  rw [← sum_prod_one_add g]
  exact hasSum_prod_of_fintype hasSum_geometric_two (fun S : Finset (Fin n) => ∏ k ∈ S, g k)

private lemma exists_equiv_pair (hF : ∀ k : ℕ, 5 ≤ k → ¬ (F k).Prime) :
    ∃ e : ℕ × Finset (Fin 5) ≃ {n : ℕ // InA003401 n},
      ∀ p : ℕ × Finset (Fin 5), (e p : ℕ) = 2 ^ p.1 * ∏ k ∈ p.2, F k := by
  let f : ℕ × Finset (Fin 5) → {n : ℕ // InA003401 n} :=
    fun p => ⟨2 ^ p.1 * ∏ k ∈ p.2, F k, inA003401_of_pair p.1 p.2⟩
  have hf_bij : Function.Bijective f := by
    constructor
    · intro p₁ p₂ h
      exact pair_injective (congrArg Subtype.val h)
    · rintro ⟨n, hn⟩
      obtain ⟨p, hp⟩ := exists_pair_of_inA003401 hF hn
      exact ⟨p, Subtype.ext hp⟩
  refine ⟨Equiv.ofBijective f hf_bij, fun p => ?_⟩
  rfl

private lemma hasSum_of_no_large_fermat
    (hF : ∀ k : ℕ, 5 ≤ k → ¬ (F k).Prime) :
    HasSum (fun n : {n : ℕ // InA003401 n} => (1 : ℝ) / (n : ℕ))
      (2 * ∏ k ∈ Finset.range 5, (1 + 1 / (F k : ℝ))) := by
  obtain ⟨e, he⟩ := exists_equiv_pair hF
  refine (e.hasSum_iff).mp ?_
  have hfun :
      ((fun n : {n : ℕ // InA003401 n} => (1 : ℝ) / (n : ℕ)) ∘ e) =
        fun p : ℕ × Finset (Fin 5) =>
          ((1 : ℝ) / 2) ^ p.1 * ∏ k ∈ p.2, (1 : ℝ) / (F k : ℝ) := by
    funext ⟨a, S⟩
    simp only [Function.comp_apply, he]
    exact summand_eq a S
  rw [hfun]
  exact hasSum_prod_geometric (n := 5) (fun k => (1 : ℝ) / (F k : ℝ))

private lemma prod_value :
    2 * ∏ k ∈ Finset.range 5, (1 + 1 / (F k : ℝ)) = 4869735552 / 1431655765 := by
  norm_num [F, Finset.prod_range_succ]

end OMA.S_oeis_a003401.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a003401.main := by
  intro hF
  exact ⟨OMA.S_oeis_a003401.Proof.hasSum_of_no_large_fermat hF,
    OMA.S_oeis_a003401.Proof.prod_value⟩
