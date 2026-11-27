import OMAReductions.R_Erdos1052_erdos_1052_R1
import Mathlib.Tactic

/-!
# Proof of Erdos 1052 Reduction H1 (Graham 1989)

Every unitary perfect number whose odd part is squarefree is equal to 6, 60, or 87360.
Following S. W. Graham, Fibonacci Quarterly 27 (1989), 317-322.
-/

namespace Erdos1052H1

/- Section 1: Combinatorial and telescoping rational product bounds -/

lemma finset_eq_range_card_of_downward {I : Finset ℕ}
    (hdown : ∀ i, i + 1 ∈ I → i ∈ I) : I = Finset.range I.card := by
  have hle_mem : ∀ k ∈ I, ∀ j ≤ k, j ∈ I := by
    intro k hk j hjk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
    clear hjk
    induction d with
    | zero => simpa using hk
    | succ d ih =>
      refine ih (hdown (j + d) ?_)
      simpa [Nat.add_assoc] using hk
  have hsub : I ⊆ Finset.range I.card := by
    intro k hk
    rw [Finset.mem_range]
    by_contra hge
    have hcard_le : I.card ≤ k := by omega
    have hrsub : Finset.range (k + 1) ⊆ I := by
      intro j hj
      exact hle_mem k hk j (by rw [Finset.mem_range] at hj; omega)
    have hle := Finset.card_le_card hrsub
    rw [Finset.card_range] at hle
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by simp)

lemma prod_rat_le_of_subset {α : Type*} [DecidableEq α] {s t : Finset α} {g : α → ℚ}
    (hst : s ⊆ t) (h1 : ∀ x ∈ t, x ∉ s → 1 ≤ g x) (h0 : ∀ x ∈ t, 0 ≤ g x) :
    ∏ x ∈ s, g x ≤ ∏ x ∈ t, g x := by
  rw [← Finset.sdiff_union_of_subset hst, Finset.prod_union Finset.sdiff_disjoint]
  have hge1 : 1 ≤ ∏ x ∈ t \ s, g x :=
    Finset.one_le_prod fun x hx => h1 x (Finset.sdiff_subset hx) (Finset.mem_sdiff.mp hx).2
  have hnn : 0 ≤ ∏ x ∈ s, g x := Finset.prod_nonneg fun x hx => h0 x (hst hx)
  nlinarith

lemma five_factor_lt_two {a0 a3 a7 a31 a127 b3 b7 b31 b127 : ℚ}
    (hbal : a0 * (a3 * a7 * a31 * a127) = 2)
    (nn3 : 0 ≤ a3) (nn7 : 0 ≤ a7) (nn31 : 0 ≤ a31) (nn127 : 0 ≤ a127)
    (le0 : a0 ≤ 1025 / 1024) (le3 : a3 ≤ b3) (le7 : a7 ≤ b7)
    (le31 : a31 ≤ b31) (le127 : a127 ≤ b127)
    (hlt : (1025 / 1024) * (b3 * b7 * b31 * b127) < 2) : False := by
  have b3_nn : 0 ≤ b3 := le_trans nn3 le3
  have b7_nn : 0 ≤ b7 := le_trans nn7 le7
  have b31_nn : 0 ≤ b31 := le_trans nn31 le31
  have h1 : a3 * a7 ≤ b3 * b7 := mul_le_mul le3 le7 nn7 b3_nn
  have h2 : a3 * a7 * a31 ≤ b3 * b7 * b31 :=
    mul_le_mul h1 le31 nn31 (mul_nonneg b3_nn b7_nn)
  have h3 : a3 * a7 * a31 * a127 ≤ b3 * b7 * b31 * b127 :=
    mul_le_mul h2 le127 nn127 (mul_nonneg (mul_nonneg b3_nn b7_nn) b31_nn)
  have h4 : a0 * (a3 * a7 * a31 * a127) ≤
      (1025 / 1024) * (b3 * b7 * b31 * b127) :=
    mul_le_mul le0 h3 (mul_nonneg (mul_nonneg (mul_nonneg nn3 nn7) nn31) nn127) (by norm_num)
  linarith

lemma seq_lower_bound {p : ℕ → ℕ} {d K : ℕ}
    (h0 : K = 0 ∨ 2 * d + 1 ≤ p 0)
    (hstep : ∀ i, i + 1 < K → 2 * p i - 1 ≤ p (i + 1)) :
    ∀ i < K, 2 ^ (i + 1) * d + 1 ≤ p i := by
  intro i hi
  induction i with
  | zero =>
    rcases h0 with rfl | h0
    · omega
    · simpa using h0
  | succ i ih =>
    have hprev := ih (by omega)
    have hs := hstep i hi
    have hpow : 2 ^ (i + 1 + 1) * d = 2 * (2 ^ (i + 1) * d) := by
      rw [pow_succ']
      ring
    omega

lemma prod_telescoping_two (d L : ℕ) :
    ∏ i ∈ Finset.range L, (2 * (2 ^ i * (d : ℚ) + 1) / (2 ^ (i + 1) * (d : ℚ) + 1)) =
      2 ^ L * ((d : ℚ) + 1) / (2 ^ L * (d : ℚ) + 1) := by
  induction L with
  | zero =>
    have hpos : (0 : ℚ) < (d : ℚ) + 1 := by positivity
    simp [div_self hpos.ne']
  | succ L ih =>
    rw [Finset.prod_range_succ, ih]
    have h1 : (0 : ℚ) < 2 ^ L * (d : ℚ) + 1 := by positivity
    have h2 : (0 : ℚ) < 2 ^ (L + 1) * (d : ℚ) + 1 := by positivity
    field_simp
    ring

lemma prod_chain_bound {p : ℕ → ℕ} {d L : ℕ} (hd : 1 ≤ d)
    (h0 : L = 0 ∨ 2 * d + 1 ≤ p 0)
    (hstep : ∀ i, i + 1 < L → 2 * p i - 1 ≤ p (i + 1)) :
    ∏ i ∈ Finset.range L, (((p i : ℚ) + 1) / (p i : ℚ)) ≤ ((d : ℚ) + 1) / (d : ℚ) := by
  have hlow := seq_lower_bound h0 hstep
  have hterm : ∀ i ∈ Finset.range L,
      (((p i : ℚ) + 1) / (p i : ℚ)) ≤
        2 * (2 ^ i * (d : ℚ) + 1) / (2 ^ (i + 1) * (d : ℚ) + 1) := by
    intro i hi
    have hiL : i < L := Finset.mem_range.mp hi
    have hle : 2 ^ (i + 1) * d + 1 ≤ p i := hlow i hiL
    have hleQ : (2 : ℚ) ^ (i + 1) * (d : ℚ) + 1 ≤ (p i : ℚ) := by exact_mod_cast hle
    have hp1 : 1 ≤ p i := by omega
    have hp_pos : (0 : ℚ) < (p i : ℚ) := by exact_mod_cast hp1
    have hden_pos : (0 : ℚ) < 2 ^ (i + 1) * (d : ℚ) + 1 := by positivity
    rw [div_le_div_iff₀ hp_pos hden_pos]
    have h2s : (2 : ℚ) ^ (i + 1) = 2 * 2 ^ i := pow_succ' 2 i
    rw [h2s] at hleQ ⊢
    linarith
  have hprod_le :
      ∏ i ∈ Finset.range L, (((p i : ℚ) + 1) / (p i : ℚ)) ≤
        ∏ i ∈ Finset.range L, (2 * (2 ^ i * (d : ℚ) + 1) / (2 ^ (i + 1) * (d : ℚ) + 1)) :=
    Finset.prod_le_prod (fun i hi => by
      have hle := hlow i (Finset.mem_range.mp hi)
      have hp1 : 1 ≤ p i := by omega
      have hp_pos : (0 : ℚ) < (p i : ℚ) := by exact_mod_cast hp1
      positivity) hterm
  refine hprod_le.trans ?_
  rw [prod_telescoping_two]
  have hd_pos : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hden_pos : (0 : ℚ) < 2 ^ L * (d : ℚ) + 1 := by positivity
  rw [div_le_div_iff₀ hden_pos hd_pos]
  linarith

lemma prod_telescoping_four (L : ℕ) :
    ∏ i ∈ Finset.range L, (4 * (4 ^ i * (3071 : ℚ) + 1) / (4 ^ (i + 1) * (3071 : ℚ) + 1)) =
      4 ^ L * 3072 / (4 ^ L * (3071 : ℚ) + 1) := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    rw [Finset.prod_range_succ, ih]
    have h1 : (0 : ℚ) < 4 ^ L * (3071 : ℚ) + 1 := by positivity
    have h2 : (0 : ℚ) < 4 ^ (L + 1) * (3071 : ℚ) + 1 := by positivity
    field_simp
    ring

lemma prod_rho4_bound (L : ℕ) :
    ∏ i ∈ Finset.range L, (4 * (4 ^ i * (3071 : ℚ) + 1) / (4 ^ (i + 1) * (3071 : ℚ) + 1)) ≤
      3072 / 3071 := by
  rw [prod_telescoping_four]
  have hden : (0 : ℚ) < 4 ^ L * (3071 : ℚ) + 1 := by positivity
  rw [div_le_div_iff₀ hden (by norm_num)]
  linarith

lemma term_rho4_le (i : ℕ) :
    ((2 : ℚ) ^ (12 + 2 * i)) / ((2 : ℚ) ^ (12 + 2 * i) - 1) ≤
      4 * (4 ^ i * (3071 : ℚ) + 1) / (4 ^ (i + 1) * (3071 : ℚ) + 1) := by
  have hpow : (2 : ℚ) ^ (12 + 2 * i) = 4096 * 4 ^ i := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hpow]
  have h4i : (1 : ℚ) ≤ 4 ^ i := one_le_pow₀ (by norm_num)
  have h1 : (0 : ℚ) < 4096 * (4 : ℚ) ^ i - 1 := by linarith
  have h2 : (0 : ℚ) < 4 ^ (i + 1) * (3071 : ℚ) + 1 := by positivity
  rw [div_le_div_iff₀ h1 h2]
  have h4s : (4 : ℚ) ^ (i + 1) = 4 * 4 ^ i := by ring
  rw [h4s]
  nlinarith

/- Section 2: Unitary divisor product formula and elementary number theory helpers -/

lemma mem_udiv {n d : ℕ} :
    d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors ↔
      d ∣ n ∧ n ≠ 0 ∧ d.Coprime (n / d) := by
  simp [and_assoc]

lemma self_mem_udiv {n : ℕ} (hn : n ≠ 0) :
    n ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors := by
  rw [mem_udiv, Nat.div_self (Nat.pos_of_ne_zero hn)]
  exact ⟨dvd_rfl, hn, Nat.coprime_one_right n⟩

lemma proper_eq_erase (n : ℕ) :
    Erdos1052.properUnitaryDivisors n =
      (Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors).erase n := by
  ext d
  simp only [Erdos1052.properUnitaryDivisors, Finset.mem_filter, Finset.mem_Ico, Finset.mem_erase,
    Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, hd, hc⟩
    exact ⟨h2.ne, ⟨hd, by omega⟩, hc⟩
  · rintro ⟨hne, ⟨hd, hn⟩, hc⟩
    have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
    exact ⟨⟨Nat.pos_of_ne_zero hd0,
      lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hne⟩, hd, hc⟩

lemma sum_udiv_of_isUnitaryPerfect {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    0 < n ∧ ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d = 2 * n := by
  obtain ⟨hs, hpos⟩ := h
  refine ⟨hpos, ?_⟩
  rw [← Finset.sum_erase_add _ _ (self_mem_udiv hpos.ne'), ← proper_eq_erase, hs]
  ring

lemma factorization_of_mem_udiv {n d : ℕ}
    (h : d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors) (p : ℕ) :
    d.factorization p = if p ∈ d.primeFactors then n.factorization p else 0 := by
  obtain ⟨hd, hn, hc⟩ := mem_udiv.mp h
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  have hq : n / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) (Nat.pos_of_ne_zero hd0)).ne'
  have hmul : n = d * (n / d) := (Nat.mul_div_cancel' hd).symm
  split_ifs with hp
  · have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hnd : ¬ p ∣ n / d := by
      intro h'
      have := Nat.dvd_gcd hpd h'
      rw [hc.gcd_eq_one] at this
      exact hpp.not_dvd_one this
    conv_rhs => rw [hmul]
    rw [Nat.factorization_mul hd0 hq, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
  · by_contra h'
    exact hp (Nat.support_factorization d ▸ Finsupp.mem_support_iff.mpr h')

lemma ppart_ne_zero {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    ∏ p ∈ S, p ^ n.factorization p ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero

lemma factorization_ppart {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) (q : ℕ) :
    (∏ p ∈ S, p ^ n.factorization p).factorization q = if q ∈ S then n.factorization q else 0 := by
  rw [Nat.factorization_prod (fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by
    rw [(Nat.prime_of_mem_primeFactors (hS hp)).factorization_pow, Finsupp.single_apply])]
  exact Finset.sum_ite_eq' S q _

lemma primeFactors_ppart {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p).primeFactors = S := by
  ext q
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_ppart hS]
  split_ifs with h
  · simp only [h, iff_true]
    exact Finsupp.mem_support_iff.mp (by rw [Nat.support_factorization]; exact hS h)
  · simp [h]

lemma ppart_mem_udiv {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p) ∈
      Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors := by
  have h0 := ppart_ne_zero hS
  have hdvd : (∏ p ∈ S, p ^ n.factorization p) ∣ n := by
    rw [← Nat.factorization_le_iff_dvd h0 hn]
    intro q
    rw [factorization_ppart hS]
    split_ifs <;> simp
  refine mem_udiv.mpr ⟨hdvd, hn, Nat.coprime_of_dvd fun p hp h1 h2 => ?_⟩
  have hq : n / (∏ p ∈ S, p ^ n.factorization p) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero h0)).ne'
  have e1 := (hp.dvd_iff_one_le_factorization h0).mp h1
  have e2 := (hp.dvd_iff_one_le_factorization hq).mp h2
  rw [factorization_ppart hS] at e1
  rw [Nat.factorization_div hdvd, Finsupp.tsub_apply, factorization_ppart hS] at e2
  split_ifs at e1 e2 <;> omega

lemma eq_ppart_of_mem_udiv {n d : ℕ}
    (h : d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors) :
    d = ∏ p ∈ d.primeFactors, p ^ n.factorization p := by
  obtain ⟨hd, hn, -⟩ := mem_udiv.mp h
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  have hsub := Nat.primeFactors_mono hd hn
  exact Nat.eq_of_factorization_eq hd0 (ppart_ne_zero hsub) fun q => by
    rw [factorization_of_mem_udiv h, factorization_ppart hsub]

lemma prod_eq_two_mul {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) = 2 * n := by
  obtain ⟨hpos, hs⟩ := sum_udiv_of_isUnitaryPerfect h
  have hn := hpos.ne'
  suffices ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d =
      ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) by rw [← this]; exact hs
  rw [Finset.prod_one_add]
  exact Finset.sum_nbij' (fun d => d.primeFactors) (fun S => ∏ p ∈ S, p ^ n.factorization p)
    (fun d hd => Finset.mem_powerset.mpr (Nat.primeFactors_mono (mem_udiv.mp hd).1 hn))
    (fun S hS => ppart_mem_udiv hn (Finset.mem_powerset.mp hS))
    (fun d hd => (eq_ppart_of_mem_udiv hd).symm)
    (fun S hS => primeFactors_ppart (Finset.mem_powerset.mp hS))
    (fun d hd => eq_ppart_of_mem_udiv hd)

lemma eq_two_pow_of_no_odd_prime_dvd :
    ∀ N : ℕ, 1 ≤ N → (∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ N) → ∃ k : ℕ, N = 2 ^ k := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN hodd
    by_cases h1 : N = 1
    · exact ⟨0, by simp [h1]⟩
    · have hp : N.minFac.Prime := Nat.minFac_prime (by omega)
      have hdvd : N.minFac ∣ N := Nat.minFac_dvd N
      have heq2 : N.minFac = 2 := by
        by_contra hne
        exact hodd N.minFac hp hne hdvd
      have h2dvd : 2 ∣ N := heq2 ▸ hdvd
      obtain ⟨M, rfl⟩ := h2dvd
      have hM1 : 1 ≤ M := by omega
      have hMlt : M < 2 * M := by omega
      obtain ⟨k, hk⟩ :=
        ih M hMlt hM1 (fun r hr hr2 hrd => hodd r hr hr2 (dvd_mul_of_dvd_right hrd 2))
      exact ⟨k + 1, by rw [hk, pow_succ']⟩

lemma odd_of_mersenne_prime {k : ℕ} (hk : 3 ≤ k) (hp : (2 ^ k - 1).Prime) : Odd k := by
  by_contra heven
  rw [Nat.not_odd_iff_even] at heven
  obtain ⟨j, rfl⟩ := heven
  have hj : 2 ≤ j := by omega
  have h4 : 4 ≤ 2 ^ j :=
    le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hj)
  have hfac : 2 ^ (j + j) - 1 = (2 ^ j - 1) * (2 ^ j + 1) := by
    have hmul : 2 ^ (j + j) = 2 ^ j * 2 ^ j := pow_add 2 j j
    rw [hmul]
    set A := 2 ^ j
    have hA : 1 ≤ A := by omega
    zify [hA, show 1 ≤ A * A by nlinarith]
    ring
  rw [hfac] at hp
  rcases hp.eq_one_or_self_of_dvd (2 ^ j - 1) (dvd_mul_right _ _) with h | h
  · omega
  · set B := 2 ^ j - 1
    have hB : 3 ≤ B := by omega
    have hmul2 : B = B * (2 ^ j + 1) := h
    nlinarith

lemma mersenne_cases {k : ℕ} (hk : 2 ≤ k) (hp : (2 ^ k - 1).Prime) :
    k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 7 ∨ 13 ≤ k := by
  by_cases hk13 : 13 ≤ k
  · exact Or.inr (Or.inr (Or.inr (Or.inr hk13)))
  · have hlt : k < 13 := by omega
    interval_cases k <;> ((try norm_num at hp); (try simp))

lemma exists_prime_dvd_mod_three_eq_two :
    ∀ N : ℕ, N % 3 = 2 → ∃ p : ℕ, p.Prime ∧ p ∣ N ∧ p % 3 = 2 := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN
    set p := N.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hd : p ∣ N := Nat.minFac_dvd N
    obtain ⟨b, hb⟩ := hd
    have hmod : (p * b) % 3 = 2 := hb ▸ hN
    have hp_pos : 2 ≤ p := hp.two_le
    have hb_pos : 1 ≤ b := by
      rcases eq_or_ne b 0 with rfl | hb0
      · simp at hmod
      · omega
    have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by
      have : p % 3 ≠ 0 := by
        intro h0
        rw [Nat.mul_mod, h0] at hmod
        norm_num at hmod
      omega
    rcases hp3 with hp1 | hp2
    · have hb2 : b % 3 = 2 := by
        rw [Nat.mul_mod, hp1] at hmod
        omega
      have hblt : b < N := by nlinarith
      obtain ⟨q, hq, hqb, hq2⟩ := ih b hblt hb2
      exact ⟨q, hq, hb ▸ dvd_mul_of_dvd_right hqb p, hq2⟩
    · exact ⟨p, hp, hb ▸ dvd_mul_right p b, hp2⟩

lemma prime_mod_eight_eq_one_of_dvd_pow_four_add_one {x p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ x ^ 4 + 1) : p % 8 = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set y : ZMod p := (x : ZMod p)
  have hy4 : y ^ 4 = -1 := by
    have h0 : ((x ^ 4 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hne1 : (-1 : ZMod p) ≠ 1 := by
    intro heq
    have h20 : ((2 : ℕ) : ZMod p) = 0 := by
      have : (1 : ZMod p) + 1 = 0 := by
        calc (1 : ZMod p) + 1 = -1 + 1 := by rw [heq]
          _ = 0 := neg_add_cancel 1
      exact_mod_cast this
    have hp_dvd_2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h20
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two p hp_dvd_2 with h | h
    · exact hp.ne_one h
    · exact hp2 h
  have hy4_ne1 : y ^ 4 ≠ 1 := hy4 ▸ hne1
  have hy8 : y ^ 8 = 1 := by
    calc y ^ 8 = (y ^ 4) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [hy4]
      _ = 1 := by ring
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at hy4
    norm_num at hy4
  have hdvd8 : orderOf y ∣ 8 := orderOf_dvd_of_pow_eq_one hy8
  have hndvd4 : ¬ orderOf y ∣ 4 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hy4_ne1
  have hord8 : orderOf y = 8 := by
    have hle : orderOf y ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd8
    have hpos : 0 < orderOf y := Nat.pos_of_dvd_of_pos hdvd8 (by norm_num)
    interval_cases orderOf y <;> simp_all
  have hfermat : y ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hy0
  have h8dvd : 8 ∣ p - 1 := hord8 ▸ orderOf_dvd_of_pow_eq_one hfermat
  have hp_ge2 : 2 ≤ p := hp.two_le
  omega

/- Section 3: Algebraic context for a unitary perfect number 2^m * s with s odd squarefree -/

structure UPNCtx where
  m : ℕ
  P : Finset ℕ
  hm : 1 ≤ m
  hprime : ∀ p ∈ P, p.Prime ∧ p ≠ 2
  hbal : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p

namespace UPNCtx

lemma prime_of_mem (c : UPNCtx) {p : ℕ} (hp : p ∈ c.P) : p.Prime :=
  (c.hprime p hp).1

lemma ne_two_of_mem (c : UPNCtx) {p : ℕ} (hp : p ∈ c.P) : p ≠ 2 :=
  (c.hprime p hp).2

lemma three_le_of_mem (c : UPNCtx) {p : ℕ} (hp : p ∈ c.P) : 3 ≤ p := by
  have h1 := (c.prime_of_mem hp).two_le
  have h2 := c.ne_two_of_mem hp
  omega

lemma two_dvd_succ_of_mem (c : UPNCtx) {p : ℕ} (hp : p ∈ c.P) : 2 ∣ p + 1 := by
  rcases (c.prime_of_mem hp).eq_two_or_odd with h | h
  · exact absurd h (c.ne_two_of_mem hp)
  · omega

lemma hbal_rat (c : UPNCtx) :
    ((2 ^ c.m + 1 : ℚ) / 2 ^ c.m) * ∏ p ∈ c.P, (((p : ℚ) + 1) / (p : ℚ)) = 2 := by
  have hQ : (((2 ^ c.m + 1) * ∏ p ∈ c.P, (p + 1) : ℕ) : ℚ) =
      ((2 ^ (c.m + 1) * ∏ p ∈ c.P, p : ℕ) : ℚ) := by
    exact_mod_cast c.hbal
  push_cast at hQ
  have hp0 : ∏ p ∈ c.P, (p : ℚ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => by
      have := c.three_le_of_mem hp
      exact_mod_cast (by omega : p ≠ 0)
  have h20 : (2 : ℚ) ^ c.m ≠ 0 := by positivity
  rw [Finset.prod_div_distrib]
  field_simp
  rw [pow_succ'] at hQ
  linarith

lemma prod_subset_lt_two (c : UPNCtx) {T : Finset ℕ} (hT : T ⊆ c.P) :
    ∏ p ∈ T, (((p : ℚ) + 1) / (p : ℚ)) < 2 := by
  have hle : ∏ p ∈ T, (((p : ℚ) + 1) / (p : ℚ)) ≤ ∏ p ∈ c.P, (((p : ℚ) + 1) / (p : ℚ)) := by
    refine prod_rat_le_of_subset hT (fun p hp _ => ?_) (fun p hp => ?_)
    · have hp3 := c.three_le_of_mem hp
      have hp_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
      rw [le_div_iff₀ hp_pos]
      linarith
    · have hp3 := c.three_le_of_mem hp
      have hp_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
      positivity
  have hpos_prod : (0 : ℚ) < ∏ p ∈ c.P, (((p : ℚ) + 1) / (p : ℚ)) := by
    refine Finset.prod_pos fun p hp => ?_
    have hp3 := c.three_le_of_mem hp
    have hp_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
    positivity
  have hm_gt : (1 : ℚ) < (2 ^ c.m + 1 : ℚ) / 2 ^ c.m := by
    have h2pos : (0 : ℚ) < 2 ^ c.m := by positivity
    rw [lt_div_iff₀ h2pos]
    linarith
  have hlt : ∏ p ∈ c.P, (((p : ℚ) + 1) / (p : ℚ)) < 2 := by
    nlinarith [c.hbal_rat]
  exact lt_of_le_of_lt hle hlt

lemma eq_of_subset_of_rat_eq_two (c : UPNCtx) {T : Finset ℕ} (hT : T ⊆ c.P)
    (heq : ((2 ^ c.m + 1 : ℚ) / 2 ^ c.m) * ∏ p ∈ T, (((p : ℚ) + 1) / (p : ℚ)) = 2) :
    c.P = T := by
  by_contra hne
  have hex : ∃ q ∈ c.P, q ∉ T := by
    by_contra hall
    apply hne
    refine Finset.Subset.antisymm ?_ hT
    intro q hq
    by_contra hqT
    exact hall ⟨q, hq, hqT⟩
  obtain ⟨q, hqP, hqT⟩ := hex
  have hins : insert q T ⊆ c.P := Finset.insert_subset hqP hT
  have hle : ∏ p ∈ insert q T, (((p : ℚ) + 1) / (p : ℚ)) ≤
      ∏ p ∈ c.P, (((p : ℚ) + 1) / (p : ℚ)) := by
    refine prod_rat_le_of_subset hins (fun p hp _ => ?_) (fun p hp => ?_)
    · have hp3 := c.three_le_of_mem hp
      have hp_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
      rw [le_div_iff₀ hp_pos]
      linarith
    · have hp3 := c.three_le_of_mem hp
      have hp_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
      positivity
  rw [Finset.prod_insert hqT] at hle
  have hfac_pos : (0 : ℚ) < (2 ^ c.m + 1 : ℚ) / 2 ^ c.m := by positivity
  have hmul := mul_le_mul_of_nonneg_left hle hfac_pos.le
  rw [c.hbal_rat] at hmul
  have hrew : ((2 ^ c.m + 1 : ℚ) / 2 ^ c.m) *
      ((((q : ℚ) + 1) / (q : ℚ)) * ∏ p ∈ T, (((p : ℚ) + 1) / (p : ℚ))) =
      (((q : ℚ) + 1) / (q : ℚ)) * 2 := by
    calc ((2 ^ c.m + 1 : ℚ) / 2 ^ c.m) *
        ((((q : ℚ) + 1) / (q : ℚ)) * ∏ p ∈ T, (((p : ℚ) + 1) / (p : ℚ)))
      _ = (((q : ℚ) + 1) / (q : ℚ)) *
          (((2 ^ c.m + 1 : ℚ) / 2 ^ c.m) * ∏ p ∈ T, (((p : ℚ) + 1) / (p : ℚ))) := by ring
      _ = (((q : ℚ) + 1) / (q : ℚ)) * 2 := by rw [heq]
  rw [hrew] at hmul
  have hq3 := c.three_le_of_mem hqP
  have hq_pos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (by omega : 0 < q)
  have hgt : (1 : ℚ) < ((q : ℚ) + 1) / (q : ℚ) := by
    rw [lt_div_iff₀ hq_pos]
    linarith
  linarith

lemma odd_prime_mem_of_dvd_rhs (c : UPNCtx) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hd : q ∣ 2 ^ (c.m + 1) * ∏ p ∈ c.P, p) : q ∈ c.P := by
  rcases hq.dvd_mul.mp hd with h1 | h2
  · have hq_dvd_2 := hq.dvd_of_dvd_pow h1
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two q hq_dvd_2 with h | h
    · exact absurd h hq.ne_one
    · exact absurd h hq2
  · rw [hq.prime.dvd_finsetProd_iff] at h2
    obtain ⟨p, hpP, hqp⟩ := h2
    rcases (c.prime_of_mem hpP).eq_one_or_self_of_dvd q hqp with h | rfl
    · exact absurd h hq.ne_one
    · exact hpP

lemma not_sq_dvd_rhs (c : UPNCtx) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ^ 2 ∣ 2 ^ (c.m + 1) * ∏ p ∈ c.P, p := by
  intro hd
  have hq1 : q ∣ 2 ^ (c.m + 1) * ∏ p ∈ c.P, p :=
    (dvd_pow_self q (by norm_num)).trans hd
  have hqP : q ∈ c.P := c.odd_prime_mem_of_dvd_rhs hq hq2 hq1
  have hsplit : 2 ^ (c.m + 1) * ∏ p ∈ c.P, p =
      q * (2 ^ (c.m + 1) * ∏ p ∈ c.P.erase q, p) := by
    rw [← Finset.mul_prod_erase c.P (fun p => p) hqP]
    ring
  rw [sq, hsplit] at hd
  have hd' : q ∣ 2 ^ (c.m + 1) * ∏ p ∈ c.P.erase q, p :=
    (Nat.mul_dvd_mul_iff_left hq.pos).mp hd
  rcases hq.dvd_mul.mp hd' with h1 | h2
  · have hq_dvd_2 := hq.dvd_of_dvd_pow h1
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two q hq_dvd_2 with h | h
    · exact hq.ne_one h
    · exact hq2 h
  · rw [hq.prime.dvd_finsetProd_iff] at h2
    obtain ⟨p, hpE, hqp⟩ := h2
    have hpP : p ∈ c.P := Finset.mem_of_mem_erase hpE
    have hpne : p ≠ q := Finset.ne_of_mem_erase hpE
    rcases (c.prime_of_mem hpP).eq_one_or_self_of_dvd q hqp with h | h
    · exact hq.ne_one h
    · exact hpne h.symm

lemma ne_two_of_dvd_two_pow_add_one (c : UPNCtx) {q : ℕ} (hd : q ∣ 2 ^ c.m + 1) : q ≠ 2 := by
  rintro rfl
  have h2m : 2 ∣ 2 ^ c.m := dvd_pow_self 2 (by have := c.hm; omega)
  omega

lemma mem_of_dvd_two_pow_add_one (c : UPNCtx) {q : ℕ} (hq : q.Prime)
    (hd : q ∣ 2 ^ c.m + 1) : q ∈ c.P := by
  have hq2 := c.ne_two_of_dvd_two_pow_add_one hd
  refine c.odd_prime_mem_of_dvd_rhs hq hq2 ?_
  rw [← c.hbal]
  exact dvd_mul_of_dvd_left hd _

lemma mem_of_dvd_succ (c : UPNCtx) {p q : ℕ} (hp : p ∈ c.P) (hq : q.Prime) (hq2 : q ≠ 2)
    (hd : q ∣ p + 1) : q ∈ c.P := by
  refine c.odd_prime_mem_of_dvd_rhs hq hq2 ?_
  rw [← c.hbal]
  exact dvd_mul_of_dvd_right (hd.trans (Finset.dvd_prod_of_mem (fun r => r + 1) hp)) _

lemma not_sq_dvd_two_pow_add_one (c : UPNCtx) {q : ℕ} (hq : q.Prime) :
    ¬ q ^ 2 ∣ 2 ^ c.m + 1 := by
  intro hd
  have hq1 : q ∣ 2 ^ c.m + 1 := (dvd_pow_self q (by norm_num)).trans hd
  have hq2 := c.ne_two_of_dvd_two_pow_add_one hq1
  refine c.not_sq_dvd_rhs hq hq2 ?_
  rw [← c.hbal]
  exact dvd_mul_of_dvd_left hd _

lemma not_sq_dvd_succ (c : UPNCtx) {p q : ℕ} (hp : p ∈ c.P) (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ^ 2 ∣ p + 1 := by
  intro hd
  refine c.not_sq_dvd_rhs hq hq2 ?_
  rw [← c.hbal]
  exact dvd_mul_of_dvd_right (hd.trans (Finset.dvd_prod_of_mem (fun r => r + 1) hp)) _

lemma not_dvd_succ_of_dvd_two_pow_add_one (c : UPNCtx) {q p : ℕ} (hq : q.Prime)
    (hd1 : q ∣ 2 ^ c.m + 1) (hp : p ∈ c.P) : ¬ q ∣ p + 1 := by
  intro hd2
  have hq2 := c.ne_two_of_dvd_two_pow_add_one hd1
  refine c.not_sq_dvd_rhs hq hq2 ?_
  rw [← c.hbal, sq]
  exact mul_dvd_mul hd1 (hd2.trans (Finset.dvd_prod_of_mem (fun r => r + 1) hp))

lemma eq_of_dvd_succ (c : UPNCtx) {q p1 p2 : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hp1 : p1 ∈ c.P) (hp2 : p2 ∈ c.P) (hd1 : q ∣ p1 + 1) (hd2 : q ∣ p2 + 1) :
    p1 = p2 := by
  by_contra hne
  have hp2E : p2 ∈ c.P.erase p1 := Finset.mem_erase.mpr ⟨Ne.symm hne, hp2⟩
  have hprod_dvd : (p1 + 1) * (p2 + 1) ∣ ∏ r ∈ c.P, (r + 1) := by
    rw [← Finset.mul_prod_erase c.P (fun r => r + 1) hp1]
    exact mul_dvd_mul_left (p1 + 1) (Finset.dvd_prod_of_mem (fun r => r + 1) hp2E)
  refine c.not_sq_dvd_rhs hq hq2 ?_
  rw [← c.hbal, sq]
  exact dvd_mul_of_dvd_right ((mul_dvd_mul hd1 hd2).trans hprod_dvd) _

lemma exists_dvd_succ_of_not_dvd (c : UPNCtx) {r : ℕ} (hr : r ∈ c.P)
    (hnd : ¬ r ∣ 2 ^ c.m + 1) : ∃ p ∈ c.P, r ∣ p + 1 := by
  have hdvd_rhs : r ∣ 2 ^ (c.m + 1) * ∏ p ∈ c.P, p :=
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun p => p) hr) _
  rw [← c.hbal] at hdvd_rhs
  rcases (c.prime_of_mem hr).dvd_mul.mp hdvd_rhs with h1 | h2
  · exact absurd h1 hnd
  · rwa [(c.prime_of_mem hr).prime.dvd_finsetProd_iff] at h2

lemma two_mul_sub_one_le_of_dvd_succ (c : UPNCtx) {r p : ℕ} (hr : r ∈ c.P) (hp : p ∈ c.P)
    (hd : r ∣ p + 1) : 2 * r - 1 ≤ p := by
  have h2 : 2 ∣ p + 1 := c.two_dvd_succ_of_mem hp
  have hcop : Nat.Coprime 2 r := by
    rw [Nat.prime_two.coprime_iff_not_dvd]
    intro h2r
    rcases (c.prime_of_mem hr).eq_one_or_self_of_dvd 2 h2r with h | h
    · omega
    · exact c.ne_two_of_mem hr h.symm
  have hmul : 2 * r ∣ p + 1 := hcop.mul_dvd_of_dvd_of_dvd h2 hd
  have hle : 2 * r ≤ p + 1 := Nat.le_of_dvd (by omega) hmul
  omega

/- Section 4: Small m (1 <= m <= 9) classification -/

lemma classify_lt_ten (c : UPNCtx) (hlt : c.m < 10) :
    (c.m = 1 ∧ c.P = {3}) ∨ (c.m = 2 ∧ c.P = {3, 5}) ∨ (c.m = 6 ∧ c.P = {3, 5, 7, 13}) := by
  have hm_cases : c.m = 1 ∨ c.m = 2 ∨ c.m = 3 ∨ c.m = 4 ∨ c.m = 5 ∨
      c.m = 6 ∨ c.m = 7 ∨ c.m = 8 ∨ c.m = 9 := by
    have := c.hm
    omega
  rcases hm_cases with hm | hm | hm | hm | hm | hm | hm | hm | hm
  · -- m = 1
    have h3 : 3 ∈ c.P :=
      c.mem_of_dvd_two_pow_add_one (by norm_num) (by rw [hm]; norm_num)
    refine Or.inl ⟨hm, c.eq_of_subset_of_rat_eq_two (Finset.singleton_subset_iff.mpr h3) ?_⟩
    rw [hm]
    norm_num
  · -- m = 2
    have h5 : 5 ∈ c.P :=
      c.mem_of_dvd_two_pow_add_one (by norm_num) (by rw [hm]; norm_num)
    have h3 : 3 ∈ c.P := c.mem_of_dvd_succ h5 (by norm_num) (by norm_num) (by norm_num)
    have hsub : ({3, 5} : Finset ℕ) ⊆ c.P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    refine Or.inr (Or.inl ⟨hm, c.eq_of_subset_of_rat_eq_two hsub ?_⟩)
    rw [hm]
    norm_num
  · -- m = 3: 9 | 2^3 + 1
    exfalso
    exact c.not_sq_dvd_two_pow_add_one (q := 3) (by norm_num) (by rw [hm]; norm_num)
  · -- m = 4: 17 in P, 9 | 18
    exfalso
    have h17 : 17 ∈ c.P :=
      c.mem_of_dvd_two_pow_add_one (by norm_num) (by rw [hm]; norm_num)
    exact c.not_sq_dvd_succ h17 (q := 3) (by norm_num) (by norm_num) (by norm_num)
  · -- m = 5: 3 | 33 and 11 in P, 3 | 12
    exfalso
    have h11 : 11 ∈ c.P :=
      c.mem_of_dvd_two_pow_add_one (by norm_num) (by rw [hm]; norm_num)
    exact c.not_dvd_succ_of_dvd_two_pow_add_one (q := 3) (by norm_num)
      (by rw [hm]; norm_num) h11 (by norm_num)
  · -- m = 6
    have h5 : 5 ∈ c.P :=
      c.mem_of_dvd_two_pow_add_one (by norm_num) (by rw [hm]; norm_num)
    have h13 : 13 ∈ c.P :=
      c.mem_of_dvd_two_pow_add_one (by norm_num) (by rw [hm]; norm_num)
    have h3 : 3 ∈ c.P := c.mem_of_dvd_succ h5 (by norm_num) (by norm_num) (by norm_num)
    have h7 : 7 ∈ c.P := c.mem_of_dvd_succ h13 (by norm_num) (by norm_num) (by norm_num)
    have hsub : ({3, 5, 7, 13} : Finset ℕ) ⊆ c.P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    refine Or.inr (Or.inr ⟨hm, c.eq_of_subset_of_rat_eq_two hsub ?_⟩)
    rw [hm]
    norm_num
  · -- m = 7: 3 | 129, 43 in P, 11 in P, 3 | 12
    exfalso
    have h43 : 43 ∈ c.P :=
      c.mem_of_dvd_two_pow_add_one (by norm_num) (by rw [hm]; norm_num)
    have h11 : 11 ∈ c.P := c.mem_of_dvd_succ h43 (by norm_num) (by norm_num) (by norm_num)
    exact c.not_dvd_succ_of_dvd_two_pow_add_one (q := 3) (by norm_num)
      (by rw [hm]; norm_num) h11 (by norm_num)
  · -- m = 8: 257 in P, 43 in P, 11 in P, 3 | 258 and 3 | 12
    exfalso
    have h257 : 257 ∈ c.P :=
      c.mem_of_dvd_two_pow_add_one (by norm_num) (by rw [hm]; norm_num)
    have h43 : 43 ∈ c.P := c.mem_of_dvd_succ h257 (by norm_num) (by norm_num) (by norm_num)
    have h11 : 11 ∈ c.P := c.mem_of_dvd_succ h43 (by norm_num) (by norm_num) (by norm_num)
    have heq := c.eq_of_dvd_succ (q := 3) (by norm_num) (by norm_num)
      h257 h11 (by norm_num) (by norm_num)
    omega
  · -- m = 9: 9 | 513
    exfalso
    exact c.not_sq_dvd_two_pow_add_one (q := 3) (by norm_num) (by rw [hm]; norm_num)

/- Section 5: Bottom-up Mersenne forest, Graham partition F(q), and m >= 10 exclusion -/

noncomputable def f (c : UPNCtx) (p : ℕ) : ℕ :=
  if h : p ∈ c.P ∧ ∃ p' ∈ c.P, p ∣ p' + 1 then h.2.choose else 0

lemma f_of_not_mem (c : UPNCtx) {p : ℕ} (hp : p ∉ c.P) : c.f p = 0 := by
  simp [f, hp]

lemma f_zero (c : UPNCtx) : c.f 0 = 0 :=
  c.f_of_not_mem (by intro h; exact Nat.not_prime_zero (c.prime_of_mem h))

lemma f_spec_of_ne_zero (c : UPNCtx) {p : ℕ} (hne : c.f p ≠ 0) :
    p ∈ c.P ∧ c.f p ∈ c.P ∧ p ∣ c.f p + 1 := by
  unfold f at hne ⊢
  split_ifs at hne ⊢ with h
  · exact ⟨h.1, h.2.choose_spec.1, h.2.choose_spec.2⟩
  · exact absurd rfl hne

lemma f_mem_or_zero (c : UPNCtx) (p : ℕ) : c.f p = 0 ∨ c.f p ∈ c.P := by
  by_cases h0 : c.f p = 0
  · exact Or.inl h0
  · exact Or.inr (c.f_spec_of_ne_zero h0).2.1

lemma f_eq_of_dvd_succ (c : UPNCtx) {p p' : ℕ} (hp : p ∈ c.P) (hp' : p' ∈ c.P)
    (hd : p ∣ p' + 1) : c.f p = p' := by
  have hex : p ∈ c.P ∧ ∃ p'' ∈ c.P, p ∣ p'' + 1 := ⟨hp, p', hp', hd⟩
  have hf : c.f p = hex.2.choose := by simp [f, hex]
  rw [hf]
  exact c.eq_of_dvd_succ (c.prime_of_mem hp) (c.ne_two_of_mem hp)
    hex.2.choose_spec.1 hp' hex.2.choose_spec.2 hd

lemma f_eq_zero_of_dvd_two_pow_add_one (c : UPNCtx) {p : ℕ} (hp : p ∈ c.P)
    (hd : p ∣ 2 ^ c.m + 1) : c.f p = 0 := by
  unfold f
  split_ifs with h
  · exfalso
    obtain ⟨p', hp', hpd⟩ := h.2
    exact c.not_dvd_succ_of_dvd_two_pow_add_one (c.prime_of_mem hp) hd hp' hpd
  · rfl

lemma two_mul_sub_one_le_f (c : UPNCtx) {p : ℕ} (hmem : c.f p ∈ c.P) :
    2 * p - 1 ≤ c.f p := by
  have hne : c.f p ≠ 0 := by
    have := c.three_le_of_mem hmem
    omega
  obtain ⟨hp, hfp, hd⟩ := c.f_spec_of_ne_zero hne
  exact c.two_mul_sub_one_le_of_dvd_succ hp hfp hd

lemma lt_f_of_f_mem (c : UPNCtx) {p : ℕ} (hmem : c.f p ∈ c.P) : p < c.f p := by
  have hne : c.f p ≠ 0 := by have := c.three_le_of_mem hmem; omega
  have hp := (c.f_spec_of_ne_zero hne).1
  have hp3 := c.three_le_of_mem hp
  have hle := c.two_mul_sub_one_le_f hmem
  omega

lemma iterate_mem_downward (c : UPNCtx) {q i : ℕ} (hmem : c.f^[i + 1] q ∈ c.P) :
    c.f^[i] q ∈ c.P := by
  rw [Function.iterate_succ_apply'] at hmem
  by_contra hnot
  rw [c.f_of_not_mem hnot] at hmem
  exact Nat.not_prime_zero (c.prime_of_mem hmem)

lemma iterate_mem_of_le (c : UPNCtx) {q j : ℕ} (hj : c.f^[j] q ∈ c.P) :
    ∀ i ≤ j, c.f^[i] q ∈ c.P := by
  intro i hij
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => simpa using hj
  | succ d ih =>
    refine ih (c.iterate_mem_downward ?_)
    simpa [Nat.add_assoc] using hj

lemma iterate_strict_mono_of_mem (c : UPNCtx) {q j : ℕ} (hj : c.f^[j] q ∈ c.P) :
    ∀ {a b : ℕ}, a < b → b ≤ j → c.f^[a] q < c.f^[b] q := by
  intro a b hab hbj
  obtain ⟨d, hd_pos, rfl⟩ : ∃ d > 0, b = a + d := ⟨b - a, by omega, by omega⟩
  clear hab
  induction d with
  | zero => omega
  | succ d ih =>
    have hstep_mem : c.f^[a + d + 1] q ∈ c.P :=
      c.iterate_mem_of_le hj (a + d + 1) (by omega)
    have hlt : c.f^[a + d] q < c.f^[a + d + 1] q := by
      rw [Function.iterate_succ_apply']
      rw [Function.iterate_succ_apply'] at hstep_mem
      exact c.lt_f_of_f_mem hstep_mem
    rcases eq_or_lt_of_le (Nat.zero_le d) with rfl | hd'
    · simpa using hlt
    · exact lt_trans (ih hd' (by omega)) hlt

lemma iterate_index_le_card (c : UPNCtx) {q i : ℕ} (hi : c.f^[i] q ∈ c.P) :
    i < c.P.card + 1 := by
  have hinj : Set.InjOn (fun k => c.f^[k] q) (Finset.range (i + 1)) := by
    intro a ha b hb heq
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · exact absurd heq (c.iterate_strict_mono_of_mem hi hlt (by omega)).ne
    · rfl
    · exact absurd heq.symm (c.iterate_strict_mono_of_mem hi hgt (by omega)).ne
  have hsub : (Finset.range (i + 1)).image (fun k => c.f^[k] q) ⊆ c.P := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact c.iterate_mem_of_le hi k (by rw [Finset.mem_range] at hk; omega)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
  omega

def M (c : UPNCtx) : Finset ℕ :=
  c.P.filter (fun q => ∀ r ∈ c.P, ¬ r ∣ q + 1)

noncomputable def orbit (c : UPNCtx) (q : ℕ) : Finset ℕ :=
  ((Finset.range (c.P.card + 1)).image (fun i => c.f^[i] q)).filter (· ∈ c.P)

lemma mem_orbit_iff (c : UPNCtx) {q p : ℕ} :
    p ∈ c.orbit q ↔ p ∈ c.P ∧ ∃ i : ℕ, c.f^[i] q = p := by
  simp only [orbit, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨i, _, rfl⟩, hp⟩
    exact ⟨hp, i, rfl⟩
  · rintro ⟨hp, i, rfl⟩
    exact ⟨⟨i, c.iterate_index_le_card hp, rfl⟩, hp⟩

lemma le_of_mem_orbit (c : UPNCtx) {q p : ℕ} (hp : p ∈ c.orbit q) : q ≤ p := by
  obtain ⟨hpP, i, rfl⟩ := (c.mem_orbit_iff).mp hp
  rcases eq_or_lt_of_le (Nat.zero_le i) with rfl | hi
  · simp
  · exact (c.iterate_strict_mono_of_mem hpP hi le_rfl).le

lemma exists_mersenne_orbit (c : UPNCtx) :
    ∀ p : ℕ, p ∈ c.P → ∃ q ∈ c.M, p ∈ c.orbit q := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro hp
    by_cases hpM : p ∈ c.M
    · exact ⟨p, hpM, c.mem_orbit_iff.mpr ⟨hp, 0, rfl⟩⟩
    · simp only [M, Finset.mem_filter, hp, true_and] at hpM
      have hex : ∃ r ∈ c.P, r ∣ p + 1 := by
        by_contra hno
        exact hpM (fun r hr hrd => hno ⟨r, hr, hrd⟩)
      obtain ⟨r, hrP, hrd⟩ := hex
      have hrlp : r < p := by
        have hr3 := c.three_le_of_mem hrP
        have hle := c.two_mul_sub_one_le_of_dvd_succ hrP hp hrd
        omega
      obtain ⟨q, hqM, hrO⟩ := ih r hrlp hrP
      obtain ⟨_, i, rfl⟩ := c.mem_orbit_iff.mp hrO
      refine ⟨q, hqM, c.mem_orbit_iff.mpr ⟨hp, i + 1, ?_⟩⟩
      rw [Function.iterate_succ_apply']
      exact c.f_eq_of_dvd_succ hrP hp hrd

lemma mersenne_eq_two_pow_sub_one (c : UPNCtx) {q : ℕ} (hq : q ∈ c.M) :
    ∃ k ≥ 2, q = 2 ^ k - 1 := by
  obtain ⟨hqP, hno⟩ := Finset.mem_filter.mp hq
  have hq3 := c.three_le_of_mem hqP
  obtain ⟨k, hk⟩ := eq_two_pow_of_no_odd_prime_dvd (q + 1) (by omega) fun r hr hr2 hrd =>
    hno r (c.mem_of_dvd_succ hqP hr hr2 hrd) hrd
  have hk2 : 2 ≤ k := by
    by_cases hlt : k < 2
    · interval_cases k <;> omega
    · omega
  exact ⟨k, hk2, by omega⟩

lemma mersenne_mem_cases (c : UPNCtx) {q : ℕ} (hq : q ∈ c.M) :
    q = 3 ∨ q = 7 ∨ q = 31 ∨ q = 127 ∨ 8191 ≤ q := by
  have hqP : q ∈ c.P := (Finset.mem_filter.mp hq).1
  obtain ⟨k, hk2, rfl⟩ := c.mersenne_eq_two_pow_sub_one hq
  have hqp : (2 ^ k - 1).Prime := c.prime_of_mem hqP
  rcases mersenne_cases hk2 hqp with rfl | rfl | rfl | rfl | hk13
  · exact Or.inl (by norm_num)
  · exact Or.inr (Or.inl (by norm_num))
  · exact Or.inr (Or.inr (Or.inl (by norm_num)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by norm_num))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    have : 2 ^ 13 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk13
    omega

noncomputable def F (c : UPNCtx) (q : ℕ) : Finset ℕ :=
  (c.orbit q).filter (fun p => ∀ q' ∈ c.M, q' < q → p ∉ c.orbit q')

noncomputable def G (c : UPNCtx) (q : ℕ) : ℚ :=
  ∏ p ∈ c.F q, (((p : ℚ) + 1) / (p : ℚ))

noncomputable def Gext (c : UPNCtx) (q : ℕ) : ℚ :=
  if q ∈ c.M then c.G q else 1

lemma P_eq_biUnion_F (c : UPNCtx) : c.P = c.M.biUnion c.F := by
  ext p
  simp only [Finset.mem_biUnion, F, Finset.mem_filter]
  constructor
  · intro hp
    have hne : (c.M.filter (fun q => p ∈ c.orbit q)).Nonempty := by
      obtain ⟨q, hqM, hpO⟩ := c.exists_mersenne_orbit p hp
      exact ⟨q, Finset.mem_filter.mpr ⟨hqM, hpO⟩⟩
    set q0 := (c.M.filter (fun q => p ∈ c.orbit q)).min' hne
    have hq0_mem := Finset.min'_mem (c.M.filter (fun q => p ∈ c.orbit q)) hne
    obtain ⟨hq0M, hpO0⟩ := Finset.mem_filter.mp hq0_mem
    refine ⟨q0, hq0M, hpO0, fun q' hq'M hlt hpO' => ?_⟩
    have hle := Finset.min'_le (c.M.filter (fun q => p ∈ c.orbit q)) q'
      (Finset.mem_filter.mpr ⟨hq'M, hpO'⟩)
    omega
  · rintro ⟨q, _, hpO, _⟩
    exact (c.mem_orbit_iff.mp hpO).1

lemma prod_P_eq_prod_M_G (c : UPNCtx) :
    ∏ p ∈ c.P, (((p : ℚ) + 1) / (p : ℚ)) = ∏ q ∈ c.M, c.G q := by
  conv_lhs => rw [c.P_eq_biUnion_F]
  refine Finset.prod_biUnion ?_
  intro q1 hq1 q2 hq2 hne
  change Disjoint (c.F q1) (c.F q2)
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  simp only [F, Finset.mem_filter] at hp1 hp2
  rcases lt_trichotomy q1 q2 with hlt | rfl | hgt
  · exact hp2.2 q1 hq1 hlt hp1.1
  · exact hne rfl
  · exact hp1.2 q2 hq2 hgt hp2.1

lemma self_mem_F (c : UPNCtx) {q : ℕ} (hq : q ∈ c.M) : q ∈ c.F q := by
  obtain ⟨hqP, hno⟩ := Finset.mem_filter.mp hq
  refine Finset.mem_filter.mpr ⟨c.mem_orbit_iff.mpr ⟨hqP, 0, rfl⟩, ?_⟩
  intro q' _ hlt hqO'
  obtain ⟨_, i, hi⟩ := c.mem_orbit_iff.mp hqO'
  rcases eq_or_ne i 0 with rfl | hi0
  · simp only [Function.iterate_zero_apply] at hi
    omega
  · have hi_step : c.f (c.f^[i - 1] q') = q := by
      calc c.f (c.f^[i - 1] q') = c.f^[i - 1 + 1] q' :=
            (Function.iterate_succ_apply' c.f (i - 1) q').symm
        _ = c.f^[i] q' := by rw [show i - 1 + 1 = i by omega]
        _ = q := hi
    have hne0 : c.f (c.f^[i - 1] q') ≠ 0 := by
      rw [hi_step]
      have := c.three_le_of_mem hqP
      omega
    obtain ⟨hrP, _, hrd⟩ := c.f_spec_of_ne_zero hne0
    rw [hi_step] at hrd
    exact hno _ hrP hrd

lemma iterate_mem_F_downward (c : UPNCtx) {q i : ℕ} (hi : c.f^[i + 1] q ∈ c.F q) :
    c.f^[i] q ∈ c.F q := by
  obtain ⟨hO, hmin⟩ := Finset.mem_filter.mp hi
  have hp1 : c.f^[i + 1] q ∈ c.P := (c.mem_orbit_iff.mp hO).1
  have hp0 : c.f^[i] q ∈ c.P := c.iterate_mem_downward hp1
  refine Finset.mem_filter.mpr ⟨c.mem_orbit_iff.mpr ⟨hp0, i, rfl⟩, ?_⟩
  intro q' hq'M hlt hO'
  obtain ⟨_, j, hj⟩ := c.mem_orbit_iff.mp hO'
  have hj1 : c.f^[j + 1] q' = c.f^[i + 1] q := by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hj]
  exact hmin q' hq'M hlt (c.mem_orbit_iff.mpr ⟨hp1, j + 1, hj1⟩)

lemma F_eq_image_range_and_G (c : UPNCtx) {q : ℕ} (hq : q ∈ c.M) :
    1 ≤ (c.F q).card ∧
    (∀ i < (c.F q).card, c.f^[i] q ∈ c.F q) ∧
    (∀ i, i + 1 < (c.F q).card → 2 * c.f^[i] q - 1 ≤ c.f^[i + 1] q) ∧
    c.G q = ∏ i ∈ Finset.range (c.F q).card, (((c.f^[i] q : ℚ) + 1) / (c.f^[i] q : ℚ)) := by
  set I := (Finset.range (c.P.card + 1)).filter (fun i => c.f^[i] q ∈ c.F q)
  have hdown : ∀ i, i + 1 ∈ I → i ∈ I := by
    intro i hi
    obtain ⟨hi_r, hi_F⟩ := Finset.mem_filter.mp hi
    rw [Finset.mem_range] at hi_r
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), c.iterate_mem_F_downward hi_F⟩
  have hI_eq : I = Finset.range I.card := finset_eq_range_card_of_downward hdown
  have hF_img : c.F q = I.image (fun i => c.f^[i] q) := by
    ext p
    simp only [I, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hpF
      have hpO : p ∈ c.orbit q := Finset.mem_of_mem_filter p hpF
      obtain ⟨hpP, i, rfl⟩ := c.mem_orbit_iff.mp hpO
      exact ⟨i, ⟨c.iterate_index_le_card hpP, hpF⟩, rfl⟩
    · rintro ⟨i, ⟨_, hiF⟩, rfl⟩
      exact hiF
  have hinj : Set.InjOn (fun i => c.f^[i] q) I := by
    intro a ha b hb heq
    have haF : c.f^[a] q ∈ c.F q := (Finset.mem_filter.mp ha).2
    have hbF : c.f^[b] q ∈ c.F q := (Finset.mem_filter.mp hb).2
    have haP : c.f^[a] q ∈ c.P := (c.mem_orbit_iff.mp (Finset.mem_of_mem_filter _ haF)).1
    have hbP : c.f^[b] q ∈ c.P := (c.mem_orbit_iff.mp (Finset.mem_of_mem_filter _ hbF)).1
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · exact absurd heq (c.iterate_strict_mono_of_mem hbP hlt le_rfl).ne
    · rfl
    · exact absurd heq.symm (c.iterate_strict_mono_of_mem haP hgt le_rfl).ne
  have hcard : (c.F q).card = I.card := by
    rw [hF_img, Finset.card_image_of_injOn hinj]
  have h0_mem : 0 ∈ I := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    simpa using c.self_mem_F hq
  have h1le : 1 ≤ (c.F q).card := by
    rw [hcard]
    exact Finset.card_pos.mpr ⟨0, h0_mem⟩
  have hi_mem : ∀ i < (c.F q).card, c.f^[i] q ∈ c.F q := by
    intro i hi
    have hiI : i ∈ I := by
      rw [hI_eq, ← hcard]
      exact Finset.mem_range.mpr hi
    exact (Finset.mem_filter.mp hiI).2
  have hstep : ∀ i, i + 1 < (c.F q).card → 2 * c.f^[i] q - 1 ≤ c.f^[i + 1] q := by
    intro i hi
    have hF1 := hi_mem (i + 1) hi
    have hP1 : c.f^[i + 1] q ∈ c.P :=
      (c.mem_orbit_iff.mp (Finset.mem_of_mem_filter _ hF1)).1
    rw [Function.iterate_succ_apply'] at hP1 ⊢
    exact c.two_mul_sub_one_le_f hP1
  have hG : c.G q =
      ∏ i ∈ Finset.range (c.F q).card, (((c.f^[i] q : ℚ) + 1) / (c.f^[i] q : ℚ)) := by
    conv_lhs =>
      unfold G
      rw [hF_img, Finset.prod_image hinj, hI_eq, ← hcard]
  exact ⟨h1le, hi_mem, hstep, hG⟩

-- Lemma 2 of Graham 1989
lemma G_le_of_mersenne_pow (c : UPNCtx) {q k : ℕ} (hq : q ∈ c.M) (hk : 2 ≤ k)
    (heq : q = 2 ^ k - 1) :
    c.G q ≤ ((2 : ℚ) ^ (k - 1)) / ((2 : ℚ) ^ (k - 1) - 1) := by
  obtain ⟨h1le, _, hstep, hG⟩ := c.F_eq_image_range_and_G hq
  rw [hG]
  set d := 2 ^ (k - 1) - 1
  have h2k1 : 2 ≤ 2 ^ (k - 1) :=
    le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hd1 : 1 ≤ d := by omega
  have h0 : (c.F q).card = 0 ∨ 2 * d + 1 ≤ c.f^[0] q := by
    refine Or.inr ?_
    simp only [Function.iterate_zero_apply]
    have hpow : 2 * 2 ^ (k - 1) = 2 ^ k := by
      conv_rhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
    omega
  have hbound := prod_chain_bound hd1 h0 hstep
  refine hbound.trans ?_
  have hdQ : (d : ℚ) = (2 : ℚ) ^ (k - 1) - 1 := by
    have h1 : 1 ≤ 2 ^ (k - 1) := by omega
    simp [d, Nat.cast_sub h1]
  rw [hdQ]
  ring_nf
  exact le_rfl

lemma one_le_G (c : UPNCtx) (q : ℕ) : 1 ≤ c.G q := by
  unfold G
  refine Finset.one_le_prod fun p hp => ?_
  have hpP : p ∈ c.P := (c.mem_orbit_iff.mp (Finset.mem_of_mem_filter p hp)).1
  have hp3 := c.three_le_of_mem hpP
  have hp_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
  rw [le_div_iff₀ hp_pos]
  linarith

lemma one_le_Gext (c : UPNCtx) (q : ℕ) : 1 ≤ c.Gext q := by
  unfold Gext
  split_ifs with h
  · exact c.one_le_G q
  · exact le_rfl

lemma Gext_7_le (c : UPNCtx) : c.Gext 7 ≤ 4 / 3 := by
  unfold Gext
  split_ifs with h7
  · have h := c.G_le_of_mersenne_pow h7 (k := 3) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  · norm_num

lemma Gext_31_le (c : UPNCtx) : c.Gext 31 ≤ 16 / 15 := by
  unfold Gext
  split_ifs with h31
  · have h := c.G_le_of_mersenne_pow h31 (k := 5) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  · norm_num

-- Lemma 3 of Graham 1989
lemma prod_M_ge_8191_le (c : UPNCtx) :
    ∏ q ∈ c.M.filter (fun q => 8191 ≤ q), c.G q ≤ 3072 / 3071 := by
  set M8 := c.M.filter (fun q => 8191 ≤ q)
  -- For each q in M8, q = 2^(13 + 2 * idx q) - 1 where idx q = (Nat.log 2 (q + 1) - 13) / 2
  let idx : ℕ → ℕ := fun q => (Nat.log 2 (q + 1) - 13) / 2
  have hq_form : ∀ q ∈ M8, q = 2 ^ (13 + 2 * idx q) - 1 ∧
      c.G q ≤ 4 * (4 ^ idx q * (3071 : ℚ) + 1) / (4 ^ (idx q + 1) * (3071 : ℚ) + 1) := by
    intro q hq8
    obtain ⟨hqM, h8191⟩ := Finset.mem_filter.mp hq8
    obtain ⟨k, hk2, hqk⟩ := c.mersenne_eq_two_pow_sub_one hqM
    have hk13 : 13 ≤ k := by
      by_contra hlt
      have : 2 ^ k ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hqp : (2 ^ k - 1).Prime := hqk ▸ c.prime_of_mem (Finset.mem_of_mem_filter q hqM)
    have hodd : Odd k := odd_of_mersenne_prime (by omega) hqp
    have hq1 : q + 1 = 2 ^ k := by
      have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
      omega
    have hlog : Nat.log 2 (q + 1) = k := by
      rw [hq1, Nat.log_pow (by norm_num : 1 < 2)]
    have hk_idx : k = 13 + 2 * idx q := by
      simp only [idx, hlog]
      obtain ⟨t, ht⟩ := hodd
      omega
    refine ⟨hk_idx ▸ hqk, ?_⟩
    have hG := c.G_le_of_mersenne_pow hqM hk2 hqk
    have hk1 : k - 1 = 12 + 2 * idx q := by omega
    rw [hk1] at hG
    exact hG.trans (term_rho4_le (idx q))
  have hinj : Set.InjOn idx M8 := by
    intro q1 hq1 q2 hq2 heq
    rw [(hq_form q1 hq1).1, (hq_form q2 hq2).1, heq]
  set f4 : ℕ → ℚ := fun i => 4 * (4 ^ i * (3071 : ℚ) + 1) / (4 ^ (i + 1) * (3071 : ℚ) + 1)
  have h1 : ∏ q ∈ M8, c.G q ≤ ∏ q ∈ M8, f4 (idx q) :=
    Finset.prod_le_prod (fun q _ => by linarith [c.one_le_G q]) fun q hq => (hq_form q hq).2
  rw [← Finset.prod_image hinj] at h1
  set L := (M8.image idx).sup id + 1
  have hsub : M8.image idx ⊆ Finset.range L := by
    intro i hi
    rw [Finset.mem_range]
    have hle : i ≤ (M8.image idx).sup id := Finset.le_sup (f := id) hi
    exact Nat.lt_succ_of_le hle
  have h2 : ∏ i ∈ M8.image idx, f4 i ≤ ∏ i ∈ Finset.range L, f4 i := by
    refine prod_rat_le_of_subset hsub (fun i _ _ => ?_) (fun i _ => ?_)
    · simp only [f4]
      have hden : (0 : ℚ) < 4 ^ (i + 1) * (3071 : ℚ) + 1 := by positivity
      rw [le_div_iff₀ hden]
      have h4s : (4 : ℚ) ^ (i + 1) = 4 * 4 ^ i := by ring
      rw [h4s]
      linarith
    · simp only [f4]
      positivity
  exact (h1.trans h2).trans (prod_rho4_bound L)

-- General predecessor-cofactor helper for Lemma 4 and Case 3 subcases (ii)-(iv)
lemma cofactor_bound_or_two_pow (c : UPNCtx) {q i B : ℕ}
    (hq : q ∈ c.M) (hi1 : 1 ≤ i) (hiF : c.f^[i] q ∈ c.F q)
    (hB : ∀ q' ∈ c.M, q < q' → B ≤ q') :
    ∃ h : ℕ, c.f^[i] q + 1 = c.f^[i - 1] q * h ∧
      (2 * B ≤ h ∨ ∃ a ≥ 1, h = 2 ^ a) := by
  have hi_prev_F : c.f^[i - 1] q ∈ c.F q := by
    have h := hiF
    rw [show i = (i - 1) + 1 by omega] at h
    exact c.iterate_mem_F_downward h
  have hp_mem : c.f^[i] q ∈ c.P :=
    (c.mem_orbit_iff.mp (Finset.mem_of_mem_filter _ hiF)).1
  have hprev_mem : c.f^[i - 1] q ∈ c.P :=
    (c.mem_orbit_iff.mp (Finset.mem_of_mem_filter _ hi_prev_F)).1
  have hstep_eq : c.f (c.f^[i - 1] q) = c.f^[i] q := by
    conv_rhs => rw [show i = (i - 1) + 1 by omega, Function.iterate_succ_apply']
  have hdvd : c.f^[i - 1] q ∣ c.f^[i] q + 1 := by
    have hne : c.f (c.f^[i - 1] q) ≠ 0 := by
      rw [hstep_eq]
      have := c.three_le_of_mem hp_mem
      omega
    exact hstep_eq ▸ (c.f_spec_of_ne_zero hne).2.2
  obtain ⟨h, hh⟩ := hdvd
  refine ⟨h, hh, ?_⟩
  have hh_pos : 1 ≤ h := by
    rcases eq_or_ne h 0 with rfl | hh0
    · simp at hh
    · omega
  have h2_dvd_h : 2 ∣ h := by
    have h2_lhs : 2 ∣ c.f^[i - 1] q * h := hh ▸ c.two_dvd_succ_of_mem hp_mem
    rcases Nat.prime_two.dvd_mul.mp h2_lhs with h1 | h2
    · exfalso
      rcases (c.prime_of_mem hprev_mem).eq_one_or_self_of_dvd 2 h1 with h' | h'
      · omega
      · exact c.ne_two_of_mem hprev_mem h'.symm
    · exact h2
  by_cases hodd : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ h
  · obtain ⟨r, hr_prime, hr2, hrd⟩ := hodd
    refine Or.inl ?_
    have hrd_succ : r ∣ c.f^[i] q + 1 := hh ▸ dvd_mul_of_dvd_right hrd _
    have hr_ne_prev : r ≠ c.f^[i - 1] q := by
      rintro rfl
      refine c.not_sq_dvd_succ hp_mem hr_prime hr2 ?_
      rw [hh, sq]
      exact mul_dvd_mul_left _ hrd
    have hrP : r ∈ c.P := c.mem_of_dvd_succ hp_mem hr_prime hr2 hrd_succ
    have hfr : c.f r = c.f^[i] q := c.f_eq_of_dvd_succ hrP hp_mem hrd_succ
    obtain ⟨q', hq'M, hrO'⟩ := c.exists_mersenne_orbit r hrP
    obtain ⟨_, j, hj⟩ := c.mem_orbit_iff.mp hrO'
    have hpO' : c.f^[i] q ∈ c.orbit q' := by
      refine c.mem_orbit_iff.mpr ⟨hp_mem, j + 1, ?_⟩
      rw [Function.iterate_succ_apply', hj, hfr]
    have hnot_lt : ¬ q' < q := fun hlt => (Finset.mem_filter.mp hiF).2 q' hq'M hlt hpO'
    have hne_q : q' ≠ q := by
      intro hqq'
      subst hqq'
      have heq_iter : c.f^[j + 1] q' = c.f^[i] q' := by
        rw [Function.iterate_succ_apply', hj, hfr]
      have hidx_eq : j + 1 = i := by
        rcases lt_trichotomy (j + 1) i with hlt | heq | hgt
        · exact absurd heq_iter (c.iterate_strict_mono_of_mem hp_mem hlt le_rfl).ne
        · exact heq
        · have hj1P : c.f^[j + 1] q' ∈ c.P := heq_iter.symm ▸ hp_mem
          exact absurd heq_iter.symm (c.iterate_strict_mono_of_mem hj1P hgt le_rfl).ne
      have : j = i - 1 := by omega
      exact hr_ne_prev (hj.symm.trans (by rw [this]))
    have hq_lt : q < q' := by omega
    have hBr : B ≤ r := le_trans (hB q' hq'M hq_lt) (c.le_of_mem_orbit hrO')
    have hcop : Nat.Coprime 2 r := by
      rw [Nat.prime_two.coprime_iff_not_dvd]
      intro h2r
      rcases hr_prime.eq_one_or_self_of_dvd 2 h2r with h' | h'
      · omega
      · exact hr2 h'.symm
    have h2r_dvd : 2 * r ∣ h := hcop.mul_dvd_of_dvd_of_dvd h2_dvd_h hrd
    have h2r_le : 2 * r ≤ h := Nat.le_of_dvd (by omega) h2r_dvd
    omega
  · refine Or.inr ?_
    obtain ⟨a, ha⟩ := eq_two_pow_of_no_odd_prime_dvd h hh_pos fun r hr hr2 hrd =>
      hodd ⟨r, hr, hr2, hrd⟩
    have ha1 : 1 ≤ a := by
      rcases eq_or_ne a 0 with rfl | ha0
      · subst ha; omega
      · omega
    exact ⟨a, ha1, ha⟩

-- Lemma 4 of Graham 1989
lemma prod_M_ge_127_le (c : UPNCtx) :
    ∏ q ∈ c.M.filter (fun q => 127 ≤ q), c.G q ≤ 122 / 121 := by
  set M127 := c.M.filter (fun q => 127 ≤ q)
  set M8191 := c.M.filter (fun q => 8191 ≤ q)
  have hsplit : ∏ q ∈ M127, c.G q = c.Gext 127 * ∏ q ∈ M8191, c.G q := by
    have h1 := (Finset.prod_filter_mul_prod_filter_not M127 (fun q => 8191 ≤ q) c.G).symm
    have hflt1 : M127.filter (fun q => 8191 ≤ q) = M8191 := by
      ext q
      simp only [M127, M8191, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hqM, _⟩, h8⟩; exact ⟨hqM, h8⟩
      · rintro ⟨hqM, h8⟩; exact ⟨⟨hqM, by omega⟩, h8⟩
    rw [hflt1, mul_comm] at h1
    rw [h1]
    congr 1
    set Mmid := M127.filter (fun q => ¬ 8191 ≤ q)
    have hsub : Mmid ⊆ {127} := by
      intro q hq
      simp only [Mmid, M127, Finset.mem_filter, Finset.mem_singleton] at hq ⊢
      rcases c.mersenne_mem_cases hq.1.1 with rfl | rfl | rfl | rfl | hge <;> omega
    have hGeq : ∏ q ∈ Mmid, c.G q = ∏ q ∈ Mmid, c.Gext q := by
      refine Finset.prod_congr rfl fun q hq => ?_
      have hqM : q ∈ c.M := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
      simp [Gext, hqM]
    rw [hGeq, Finset.prod_subset hsub]
    · simp
    · intro q hq1 hnot
      rw [Finset.mem_singleton.mp hq1] at hnot ⊢
      unfold Gext
      split_ifs with h127M
      · exfalso
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨h127M, by norm_num⟩, by norm_num⟩)
      · rfl
  have hG127 : c.Gext 127 ≤ (128 / 127) * (16256 / 16255) := by
    unfold Gext
    split_ifs with h127
    · obtain ⟨h1le, hiF, hstep, hG⟩ := c.F_eq_image_range_and_G h127
      set K := (c.F 127).card
      have hK : K = 1 + (K - 1) := by omega
      rw [hG, hK, Finset.prod_range_add]
      simp only [Finset.prod_range_one, Function.iterate_zero_apply]
      have htail : ∏ i ∈ Finset.range (K - 1),
          (((c.f^[1 + i] 127 : ℚ) + 1) / (c.f^[1 + i] 127 : ℚ)) ≤ 16256 / 16255 := by
        have h0_tail : K - 1 = 0 ∨ 2 * 16255 + 1 ≤ c.f^[1 + 0] 127 := by
          by_cases hK1 : K - 1 = 0
          · exact Or.inl hK1
          · refine Or.inr ?_
            have h1_lt : 1 < K := by omega
            have h1F : c.f^[1] 127 ∈ c.F 127 := hiF 1 h1_lt
            have hp1_prime : (c.f^[1] 127).Prime :=
              c.prime_of_mem (c.mem_orbit_iff.mp (Finset.mem_of_mem_filter _ h1F)).1
            obtain ⟨h, hh, hcases⟩ := c.cofactor_bound_or_two_pow h127 le_rfl h1F
              (B := 8191) (fun q' hq'M hgt => by
                rcases c.mersenne_mem_cases hq'M with rfl | rfl | rfl | rfl | hge <;> omega)
            simp only [Nat.sub_self, Function.iterate_zero_apply, Nat.add_zero] at hh ⊢
            rcases hcases with hbig | ⟨a, ha1, rfl⟩
            · omega
            · by_cases ha8 : 8 ≤ a
              · have : 2 ^ 8 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha8
                omega
              · exfalso
                have ha_lt : a < 8 := by omega
                have hp_eq : c.f^[1] 127 = 127 * 2 ^ a - 1 := by omega
                rw [hp_eq] at hp1_prime
                interval_cases a <;> norm_num at hp1_prime
        have hbound := prod_chain_bound (p := fun i => c.f^[1 + i] 127) (d := 16255)
          (L := K - 1) (by norm_num) h0_tail (fun i hi => by
            have := hstep (1 + i) (by omega)
            simpa [Nat.add_assoc] using this)
        exact hbound.trans (by norm_num)
      have hnonneg : (0 : ℚ) ≤ ((127 : ℚ) + 1) / 127 := by norm_num
      have hmul := mul_le_mul_of_nonneg_left htail hnonneg
      norm_num at hmul ⊢
      exact hmul
    · norm_num
  have h8 := c.prod_M_ge_8191_le
  rw [hsplit]
  have hpos1 : (0 : ℚ) ≤ c.Gext 127 := by linarith [c.one_le_Gext 127]
  have hpos2 : (0 : ℚ) ≤ ∏ q ∈ M8191, c.G q :=
    Finset.prod_nonneg fun q _ => by linarith [c.one_le_G q]
  nlinarith

lemma prod_M_decomp (c : UPNCtx) :
    ∏ q ∈ c.M, c.G q =
      c.Gext 3 * c.Gext 7 * c.Gext 31 * ∏ q ∈ c.M.filter (fun q => 127 ≤ q), c.G q := by
  have h1 := (Finset.prod_filter_mul_prod_filter_not c.M (fun q => 127 ≤ q) c.G).symm
  rw [mul_comm] at h1
  rw [h1]
  congr 1
  set Msmall := c.M.filter (fun q => ¬ 127 ≤ q)
  have hsub : Msmall ⊆ {3, 7, 31} := by
    intro q hq
    obtain ⟨hqM, hlt⟩ := Finset.mem_filter.mp hq
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases c.mersenne_mem_cases hqM with rfl | rfl | rfl | rfl | hge <;> omega
  have hGeq : ∏ q ∈ Msmall, c.G q = ∏ q ∈ Msmall, c.Gext q := by
    refine Finset.prod_congr rfl fun q hq => ?_
    have hqM : q ∈ c.M := (Finset.mem_filter.mp hq).1
    simp [Gext, hqM]
  rw [hGeq, Finset.prod_subset hsub]
  · simp only [Finset.prod_insert (by decide : (3 : ℕ) ∉ ({7, 31} : Finset ℕ)),
      Finset.prod_insert (by decide : (7 : ℕ) ∉ ({31} : Finset ℕ)),
      Finset.prod_singleton]
    ring
  · intro q hq123 hnot
    unfold Gext
    split_ifs with hqM
    · exfalso
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq123
      refine hnot (Finset.mem_filter.mpr ⟨hqM, ?_⟩)
      rcases hq123 with rfl | rfl | rfl <;> norm_num
    · rfl

lemma three_mem_M_of_mem_P (c : UPNCtx) (h3 : 3 ∈ c.P) : 3 ∈ c.M ∧ c.F 3 = c.orbit 3 := by
  have h3M : 3 ∈ c.M := by
    refine Finset.mem_filter.mpr ⟨h3, fun r hr hrd => ?_⟩
    have hrp := c.prime_of_mem hr
    have hr3 := c.three_le_of_mem hr
    have hrle : r ≤ 4 := Nat.le_of_dvd (by norm_num) hrd
    interval_cases r <;> ((try norm_num at hrd); (try norm_num at hrp))
  refine ⟨h3M, ?_⟩
  ext p
  simp only [F, Finset.mem_filter, and_iff_left_iff_imp]
  intro _ q' hq'M hlt
  have hq'3 := c.three_le_of_mem (Finset.mem_of_mem_filter q' hq'M)
  omega

lemma orbit_eq_singleton_of_f_zero (c : UPNCtx) {q : ℕ} (hq : q ∈ c.P) (hf0 : c.f q = 0) :
    c.orbit q = {q} := by
  ext p
  rw [c.mem_orbit_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hpP, i, rfl⟩
    rcases eq_or_ne i 0 with rfl | hi0
    · rfl
    · exfalso
      have h0 : ∀ k ≥ 1, c.f^[k] q = 0 := by
        intro k hk
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
        clear hk
        induction d with
        | zero => simpa using hf0
        | succ d ih =>
          rw [show 1 + (d + 1) = (1 + d) + 1 by omega, Function.iterate_succ_apply',
            ih, c.f_zero]
      rw [h0 i (by omega)] at hpP
      exact Nat.not_prime_zero (c.prime_of_mem hpP)
  · rintro rfl
    exact ⟨hq, 0, rfl⟩

lemma orbit_eq_pair_of_f_f_zero (c : UPNCtx) {q p : ℕ} (hq : q ∈ c.P) (hp : p ∈ c.P)
    (hf1 : c.f q = p) (hf2 : c.f p = 0) : c.orbit q = {q, p} := by
  ext x
  rw [c.mem_orbit_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hxP, i, rfl⟩
    by_cases hi : i < 2
    · interval_cases i
      · exact Or.inl rfl
      · exact Or.inr hf1
    · exfalso
      have h0 : ∀ k ≥ 2, c.f^[k] q = 0 := by
        intro k hk
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
        clear hk
        induction d with
        | zero => simp [Function.iterate_succ_apply', hf1, hf2]
        | succ d ih =>
          rw [show 2 + (d + 1) = (2 + d) + 1 by omega, Function.iterate_succ_apply',
            ih, c.f_zero]
      rw [h0 i (by omega)] at hxP
      exact Nat.not_prime_zero (c.prime_of_mem hxP)
  · rintro (rfl | rfl)
    · exact ⟨hq, 0, rfl⟩
    · exact ⟨hp, 1, hf1⟩

-- Ruling out m >= 10 by Graham's three cases: m odd, m == 0 mod 4, m == 2 mod 4
lemma not_ge_ten (c : UPNCtx) : ¬ 10 ≤ c.m := by
  intro hm10
  have h2m_bound : ((2 ^ c.m + 1 : ℚ) / 2 ^ c.m) ≤ 1025 / 1024 := by
    have hpow : (1024 : ℚ) ≤ (2 : ℚ) ^ c.m := by
      have : (2 : ℚ) ^ 10 ≤ (2 : ℚ) ^ c.m := pow_le_pow_right₀ (by norm_num) hm10
      norm_num at this
      exact this
    have hpos : (0 : ℚ) < (2 : ℚ) ^ c.m := by positivity
    rw [div_le_div_iff₀ hpos (by norm_num)]
    linarith
  have hbal := c.hbal_rat
  rw [c.prod_P_eq_prod_M_G, c.prod_M_decomp] at hbal
  have hM127_le := c.prod_M_ge_127_le
  have hM127_nonneg : (0 : ℚ) ≤ ∏ q ∈ c.M.filter (fun q => 127 ≤ q), c.G q :=
    Finset.prod_nonneg fun q _ => by linarith [c.one_le_G q]
  have h7_le := c.Gext_7_le
  have h31_le := c.Gext_31_le
  have h7_pos : (0 : ℚ) ≤ c.Gext 7 := by linarith [c.one_le_Gext 7]
  have h31_pos : (0 : ℚ) ≤ c.Gext 31 := by linarith [c.one_le_Gext 31]
  have h3_pos : (0 : ℚ) ≤ c.Gext 3 := by linarith [c.one_le_Gext 3]
  have hm_mod4 : c.m % 2 = 1 ∨ c.m % 4 = 0 ∨ c.m % 4 = 2 := by omega
  rcases hm_mod4 with hmod | hmod | hmod
  · -- Case 1: m is odd -> 3 | 2^m + 1, Gext 3 = 4/3
    have h3_dvd : 3 ∣ 2 ^ c.m + 1 := by
      obtain ⟨k, hk⟩ : ∃ k, c.m = 2 * k + 1 := ⟨c.m / 2, by omega⟩
      rw [hk]
      have hmod3 : (2 ^ (2 * k + 1) + 1) % 3 = 0 := by
        rw [pow_succ, pow_mul]
        norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
      omega
    have h3P : 3 ∈ c.P := c.mem_of_dvd_two_pow_add_one (by norm_num) h3_dvd
    obtain ⟨h3M, hF3⟩ := c.three_mem_M_of_mem_P h3P
    have hG3 : c.Gext 3 ≤ 4 / 3 := by
      simp only [Gext, h3M, ↓reduceIte, G, hF3,
        c.orbit_eq_singleton_of_f_zero h3P (c.f_eq_zero_of_dvd_two_pow_add_one h3P h3_dvd)]
      norm_num
    exact five_factor_lt_two hbal h3_pos h7_pos h31_pos hM127_nonneg
      h2m_bound hG3 h7_le h31_le hM127_le (by norm_num)
  · -- Case 2: m == 0 mod 4 -> exists p | 2^m + 1 with p >= 41 and p == 2 mod 3
    obtain ⟨k, hk⟩ : ∃ k, c.m = 4 * k := ⟨c.m / 4, by omega⟩
    have hmod3 : (2 ^ c.m + 1) % 3 = 2 := by
      rw [hk, pow_mul]
      norm_num [Nat.add_mod, Nat.pow_mod]
    obtain ⟨p, hp_prime, hp_dvd, hp_mod3⟩ := exists_prime_dvd_mod_three_eq_two _ hmod3
    have hp2 : p ≠ 2 := c.ne_two_of_dvd_two_pow_add_one hp_dvd
    have hp_mod8 : p % 8 = 1 := by
      refine prime_mod_eight_eq_one_of_dvd_pow_four_add_one (x := 2 ^ k) hp_prime hp2 ?_
      have : (2 ^ k) ^ 4 = 2 ^ c.m := by rw [← pow_mul, mul_comm, ← hk]
      rwa [this]
    have hpP : p ∈ c.P := c.mem_of_dvd_two_pow_add_one hp_prime hp_dvd
    have hp_ne_17 : p ≠ 17 := by
      rintro rfl
      exact c.not_sq_dvd_succ hpP (q := 3) (by norm_num) (by norm_num) (by norm_num)
    have hp41 : 41 ≤ p := by omega
    have h3_dvd_p : 3 ∣ p + 1 := by omega
    have h3P : 3 ∈ c.P := c.mem_of_dvd_succ hpP (by norm_num) (by norm_num) h3_dvd_p
    obtain ⟨h3M, hF3⟩ := c.three_mem_M_of_mem_P h3P
    have hG3_le : c.Gext 3 ≤ (4 / 3) * (42 / 41) := by
      have horb := c.orbit_eq_pair_of_f_f_zero h3P hpP
        (c.f_eq_of_dvd_succ h3P hpP h3_dvd_p) (c.f_eq_zero_of_dvd_two_pow_add_one hpP hp_dvd)
      simp only [Gext, h3M, ↓reduceIte, G, hF3, horb]
      rw [Finset.prod_pair (by omega : 3 ≠ p)]
      have hp_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
      have hp_le : (((p : ℚ) + 1) / (p : ℚ)) ≤ 42 / 41 := by
        rw [div_le_div_iff₀ hp_pos (by norm_num)]
        have hpQ : (41 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp41
        linarith
      exact mul_le_mul (by norm_num) hp_le (by positivity) (by norm_num)
    exact five_factor_lt_two hbal h3_pos h7_pos h31_pos hM127_nonneg
      h2m_bound hG3_le h7_le h31_le hM127_le (by norm_num)
  · -- Case 3: m == 2 mod 4 -> 5 | 2^m + 1, F(3) = {3, 5}, Gext 3 = (4/3)*(6/5) = 8/5
    obtain ⟨k, hk⟩ : ∃ k, c.m = 4 * k + 2 := ⟨c.m / 4, by omega⟩
    have h5_dvd : 5 ∣ 2 ^ c.m + 1 := by
      have hmod5 : (2 ^ c.m + 1) % 5 = 0 := by
        rw [hk, pow_add, pow_mul]
        norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
      omega
    have h5P : 5 ∈ c.P := c.mem_of_dvd_two_pow_add_one (by norm_num) h5_dvd
    have h3P : 3 ∈ c.P := c.mem_of_dvd_succ h5P (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨h3M, hF3⟩ := c.three_mem_M_of_mem_P h3P
    have horb3 := c.orbit_eq_pair_of_f_f_zero h3P h5P
      (c.f_eq_of_dvd_succ h3P h5P (by norm_num))
      (c.f_eq_zero_of_dvd_two_pow_add_one h5P h5_dvd)
    have hG3 : c.Gext 3 ≤ (4 / 3) * (6 / 5) := by
      simp only [Gext, h3M, ↓reduceIte, G, hF3, horb3]
      rw [Finset.prod_pair (by decide : (3 : ℕ) ≠ 5)]
      norm_num
    by_cases h7P : 7 ∈ c.P
    · -- 7 in P -> 7 in M
      have h7M : 7 ∈ c.M := by
        refine Finset.mem_filter.mpr ⟨h7P, fun r hr hrd => ?_⟩
        have hrp := c.prime_of_mem hr
        have hr3 := c.three_le_of_mem hr
        have hrle : r ≤ 8 := Nat.le_of_dvd (by norm_num) hrd
        interval_cases r <;> ((try norm_num at hrd); (try norm_num at hrp))
      by_cases h13P : 13 ∈ c.P
      · -- 7 in P and 13 in P -> 31 not in P!
        have h31_not_P : 31 ∉ c.P := by
          intro h31P
          have hsub : ({3, 5, 7, 13, 31} : Finset ℕ) ⊆ c.P := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
          have hlt := c.prod_subset_lt_two hsub
          simp only [Finset.prod_insert (by decide : (3 : ℕ) ∉ ({5, 7, 13, 31} : Finset ℕ)),
            Finset.prod_insert (by decide : (5 : ℕ) ∉ ({7, 13, 31} : Finset ℕ)),
            Finset.prod_insert (by decide : (7 : ℕ) ∉ ({13, 31} : Finset ℕ)),
            Finset.prod_insert (by decide : (13 : ℕ) ∉ ({31} : Finset ℕ)),
            Finset.prod_singleton] at hlt
          norm_num at hlt
        have h31_not_M : 31 ∉ c.M := fun h => h31_not_P (Finset.mem_of_mem_filter 31 h)
        have hG31_le : c.Gext 31 ≤ 1 := by simp [Gext, h31_not_M]
        have hf7_13 : c.f 7 = 13 := c.f_eq_of_dvd_succ h7P h13P (by norm_num)
        have h13_in_F7 : 13 ∈ c.F 7 := by
          refine Finset.mem_filter.mpr ⟨c.mem_orbit_iff.mpr ⟨h13P, 1, hf7_13⟩, ?_⟩
          intro q' hq'M hlt hO'
          have hq'3 : q' = 3 := by
            rcases c.mersenne_mem_cases hq'M with rfl | rfl | rfl | rfl | hge <;> omega
          subst hq'3
          rw [horb3] at hO'
          simp at hO'
        by_cases h103P : 103 ∈ c.P
        · -- Subcase 3(iv): 7, 13, 103 in P -> 127 not in P, Gext 7 <= (8/7)*(14/13)*(104/103)*(412/411)
          have h127_not_P : 127 ∉ c.P := by
            intro h127P
            have hsub : ({3, 5, 7, 13, 103, 127} : Finset ℕ) ⊆ c.P := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
            have hlt := c.prod_subset_lt_two hsub
            simp only [Finset.prod_insert (by decide : (3 : ℕ) ∉ ({5, 7, 13, 103, 127} : Finset ℕ)),
              Finset.prod_insert (by decide : (5 : ℕ) ∉ ({7, 13, 103, 127} : Finset ℕ)),
              Finset.prod_insert (by decide : (7 : ℕ) ∉ ({13, 103, 127} : Finset ℕ)),
              Finset.prod_insert (by decide : (13 : ℕ) ∉ ({103, 127} : Finset ℕ)),
              Finset.prod_insert (by decide : (103 : ℕ) ∉ ({127} : Finset ℕ)),
              Finset.prod_singleton] at hlt
            norm_num at hlt
          have h127_not_M : 127 ∉ c.M := fun h => h127_not_P (Finset.mem_of_mem_filter 127 h)
          have hM127_le_3072 : ∏ q ∈ c.M.filter (fun q => 127 ≤ q), c.G q ≤ 3072 / 3071 := by
            have hM127_eq : c.M.filter (fun q => 127 ≤ q) = c.M.filter (fun q => 8191 ≤ q) := by
              ext q
              simp only [Finset.mem_filter]
              constructor
              · rintro ⟨hqM, hge⟩
                refine ⟨hqM, ?_⟩
                rcases c.mersenne_mem_cases hqM with rfl | rfl | rfl | rfl | h8
                · omega
                · omega
                · omega
                · exact absurd hqM h127_not_M
                · exact h8
              · rintro ⟨hqM, h8⟩
                exact ⟨hqM, by omega⟩
            rw [hM127_eq]
            exact c.prod_M_ge_8191_le
          have hf13_103 : c.f 13 = 103 := c.f_eq_of_dvd_succ h13P h103P (by norm_num)
          have hf2_7 : c.f^[2] 7 = 103 := by
            simp [Function.iterate_succ_apply', hf7_13, hf13_103]
          have h103_in_F7 : 103 ∈ c.F 7 := by
            refine Finset.mem_filter.mpr ⟨c.mem_orbit_iff.mpr ⟨h103P, 2, hf2_7⟩, ?_⟩
            intro q' hq'M hlt hO'
            have hq'3 : q' = 3 := by
              rcases c.mersenne_mem_cases hq'M with rfl | rfl | rfl | rfl | hge <;> omega
            subst hq'3
            rw [horb3] at hO'
            simp at hO'
          have hcard3 : 3 ≤ (c.F 7).card := by
            have hsub : ({7, 13, 103} : Finset ℕ) ⊆ c.F 7 := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl
              · exact c.self_mem_F h7M
              · exact h13_in_F7
              · exact h103_in_F7
            have hle := Finset.card_le_card hsub
            have h3c : ({7, 13, 103} : Finset ℕ).card = 3 := by decide
            omega
          have hG7_bound : c.Gext 7 ≤ (8 / 7) * (14 / 13) * (104 / 103) * (412 / 411) := by
            simp only [Gext, h7M, ↓reduceIte]
            obtain ⟨_, hiF, hstep, hG⟩ := c.F_eq_image_range_and_G h7M
            set K := (c.F 7).card
            have hK : K = 3 + (K - 3) := by omega
            rw [hG, hK, Finset.prod_range_add]
            have hpre : ∏ i ∈ Finset.range 3, (((c.f^[i] 7 : ℚ) + 1) / (c.f^[i] 7 : ℚ)) =
                (8 / 7) * (14 / 13) * (104 / 103) := by
              rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one]
              simp only [Function.iterate_zero_apply, Function.iterate_one, hf7_13, hf2_7]
              norm_num
            rw [hpre]
            have htail : ∏ i ∈ Finset.range (K - 3),
                (((c.f^[3 + i] 7 : ℚ) + 1) / (c.f^[3 + i] 7 : ℚ)) ≤ 412 / 411 := by
              have h0_tail : K - 3 = 0 ∨ 2 * 411 + 1 ≤ c.f^[3 + 0] 7 := by
                by_cases hK3 : K - 3 = 0
                · exact Or.inl hK3
                · refine Or.inr ?_
                  have h3F : c.f^[3] 7 ∈ c.F 7 := hiF 3 (by omega)
                  have hp3_prime : (c.f^[3] 7).Prime :=
                    c.prime_of_mem (c.mem_orbit_iff.mp (Finset.mem_of_mem_filter _ h3F)).1
                  obtain ⟨h, hh, hcases⟩ := c.cofactor_bound_or_two_pow h7M (by omega) h3F
                    (B := 8191) (fun q' hq'M hgt => by
                      rcases c.mersenne_mem_cases hq'M with rfl | rfl | rfl | rfl | hge
                      · omega
                      · omega
                      · exact absurd hq'M h31_not_M
                      · exact absurd hq'M h127_not_M
                      · exact hge)
                  simp only [show 3 - 1 = 2 by rfl, hf2_7, Nat.add_zero] at hh ⊢
                  rcases hcases with hbig | ⟨a, ha1, rfl⟩
                  · omega
                  · by_cases ha3 : 3 ≤ a
                    · have : 2 ^ 3 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha3
                      omega
                    · exfalso
                      have ha_lt : a < 3 := by omega
                      have hp_eq : c.f^[3] 7 = 103 * 2 ^ a - 1 := by omega
                      rw [hp_eq] at hp3_prime
                      interval_cases a <;> norm_num at hp3_prime
              have hbound := prod_chain_bound (p := fun i => c.f^[3 + i] 7) (d := 411)
                (L := K - 3) (by norm_num) h0_tail (fun i hi => by
                  have := hstep (3 + i) (by omega)
                  simpa [Nat.add_assoc] using this)
              exact hbound.trans (by norm_num)
            exact mul_le_mul_of_nonneg_left htail (by norm_num)
          exact five_factor_lt_two hbal h3_pos h7_pos h31_pos hM127_nonneg
            h2m_bound hG3 hG7_bound hG31_le hM127_le_3072 (by norm_num)
        · -- Subcase 3(iii): 7, 13 in P, 103 not in P -> Gext 7 <= (8/7)*(14/13)*(832/831)
          have hcard2 : 2 ≤ (c.F 7).card := by
            have hsub : ({7, 13} : Finset ℕ) ⊆ c.F 7 := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl
              · exact c.self_mem_F h7M
              · exact h13_in_F7
            have hle := Finset.card_le_card hsub
            have h2c : ({7, 13} : Finset ℕ).card = 2 := by decide
            omega
          have hG7_bound : c.Gext 7 ≤ (8 / 7) * (14 / 13) * (832 / 831) := by
            simp only [Gext, h7M, ↓reduceIte]
            obtain ⟨_, hiF, hstep, hG⟩ := c.F_eq_image_range_and_G h7M
            set K := (c.F 7).card
            have hK : K = 2 + (K - 2) := by omega
            rw [hG, hK, Finset.prod_range_add]
            have hpre : ∏ i ∈ Finset.range 2, (((c.f^[i] 7 : ℚ) + 1) / (c.f^[i] 7 : ℚ)) =
                (8 / 7) * (14 / 13) := by
              rw [Finset.prod_range_succ, Finset.prod_range_one]
              simp only [Function.iterate_zero_apply, Function.iterate_one, hf7_13]
              norm_num
            rw [hpre]
            have htail : ∏ i ∈ Finset.range (K - 2),
                (((c.f^[2 + i] 7 : ℚ) + 1) / (c.f^[2 + i] 7 : ℚ)) ≤ 832 / 831 := by
              have h0_tail : K - 2 = 0 ∨ 2 * 831 + 1 ≤ c.f^[2 + 0] 7 := by
                by_cases hK2 : K - 2 = 0
                · exact Or.inl hK2
                · refine Or.inr ?_
                  have h2F : c.f^[2] 7 ∈ c.F 7 := hiF 2 (by omega)
                  have hp2_mem : c.f^[2] 7 ∈ c.P :=
                    (c.mem_orbit_iff.mp (Finset.mem_of_mem_filter _ h2F)).1
                  have hp2_prime : (c.f^[2] 7).Prime := c.prime_of_mem hp2_mem
                  obtain ⟨h, hh, hcases⟩ := c.cofactor_bound_or_two_pow h7M (by omega) h2F
                    (B := 127) (fun q' hq'M hgt => by
                      rcases c.mersenne_mem_cases hq'M with rfl | rfl | rfl | rfl | hge
                      · omega
                      · omega
                      · exact absurd hq'M h31_not_M
                      · omega
                      · omega)
                  simp only [show 2 - 1 = 1 by rfl, Function.iterate_one, hf7_13, Nat.add_zero] at hh ⊢
                  rcases hcases with hbig | ⟨a, ha1, rfl⟩
                  · omega
                  · by_cases ha7 : 7 ≤ a
                    · have : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha7
                      omega
                    · exfalso
                      have ha_lt : a < 7 := by omega
                      have hp_eq : c.f^[2] 7 = 13 * 2 ^ a - 1 := by omega
                      interval_cases a
                      · rw [hp_eq] at hp2_prime; norm_num at hp2_prime
                      · rw [hp_eq] at hp2_prime; norm_num at hp2_prime
                      · norm_num at hp_eq; exact h103P (hp_eq ▸ hp2_mem)
                      · rw [hp_eq] at hp2_prime; norm_num at hp2_prime
                      · rw [hp_eq] at hp2_prime; norm_num at hp2_prime
                      · rw [hp_eq] at hp2_prime; norm_num at hp2_prime
              have hbound := prod_chain_bound (p := fun i => c.f^[2 + i] 7) (d := 831)
                (L := K - 2) (by norm_num) h0_tail (fun i hi => by
                  have := hstep (2 + i) (by omega)
                  simpa [Nat.add_assoc] using this)
              exact hbound.trans (by norm_num)
            exact mul_le_mul_of_nonneg_left htail (by norm_num)
          exact five_factor_lt_two hbal h3_pos h7_pos h31_pos hM127_nonneg
            h2m_bound hG3 hG7_bound hG31_le hM127_le (by norm_num)
      · -- Subcase 3(ii): 7 in P and 13 not in P -> Gext 7 <= (8/7)*(112/111)
        have hG7_bound : c.Gext 7 ≤ (8 / 7) * (112 / 111) := by
          simp only [Gext, h7M, ↓reduceIte]
          obtain ⟨h1le, hiF, hstep, hG⟩ := c.F_eq_image_range_and_G h7M
          set K := (c.F 7).card
          have hK : K = 1 + (K - 1) := by omega
          rw [hG, hK, Finset.prod_range_add]
          simp only [Finset.prod_range_one, Function.iterate_zero_apply]
          have htail : ∏ i ∈ Finset.range (K - 1),
              (((c.f^[1 + i] 7 : ℚ) + 1) / (c.f^[1 + i] 7 : ℚ)) ≤ 112 / 111 := by
            have h0_tail : K - 1 = 0 ∨ 2 * 111 + 1 ≤ c.f^[1 + 0] 7 := by
              by_cases hK1 : K - 1 = 0
              · exact Or.inl hK1
              · refine Or.inr ?_
                have h1F : c.f^[1] 7 ∈ c.F 7 := hiF 1 (by omega)
                have hp1_mem : c.f^[1] 7 ∈ c.P :=
                  (c.mem_orbit_iff.mp (Finset.mem_of_mem_filter _ h1F)).1
                have hp1_prime : (c.f^[1] 7).Prime := c.prime_of_mem hp1_mem
                obtain ⟨h, hh, hcases⟩ := c.cofactor_bound_or_two_pow h7M le_rfl h1F
                  (B := 31) (fun q' hq'M hgt => by
                    rcases c.mersenne_mem_cases hq'M with rfl | rfl | rfl | rfl | hge <;> omega)
                simp only [Nat.sub_self, Function.iterate_zero_apply, Nat.add_zero] at hh ⊢
                rcases hcases with hbig | ⟨a, ha1, rfl⟩
                · omega
                · by_cases ha5 : 5 ≤ a
                  · have : 2 ^ 5 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha5
                    omega
                  · exfalso
                    have ha_lt : a < 5 := by omega
                    have hp_eq : c.f^[1] 7 = 7 * 2 ^ a - 1 := by omega
                    interval_cases a
                    · norm_num at hp_eq; exact h13P (hp_eq ▸ hp1_mem)
                    · rw [hp_eq] at hp1_prime; norm_num at hp1_prime
                    · rw [hp_eq] at hp1_prime; norm_num at hp1_prime
                    · rw [hp_eq] at hp1_prime; norm_num at hp1_prime
            have hbound := prod_chain_bound (p := fun i => c.f^[1 + i] 7) (d := 111)
              (L := K - 1) (by norm_num) h0_tail (fun i hi => by
                have := hstep (1 + i) (by omega)
                simpa [Nat.add_assoc] using this)
            exact hbound.trans (by norm_num)
          have hmul := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℚ) ≤ ((7 : ℚ) + 1) / 7)
          exact hmul.trans (by norm_num)
        exact five_factor_lt_two hbal h3_pos h7_pos h31_pos hM127_nonneg
          h2m_bound hG3 hG7_bound h31_le hM127_le (by norm_num)
    · -- Subcase 3(i): 7 not in P -> Gext 7 = 1
      have h7_not_M : 7 ∉ c.M := fun h => h7P (Finset.mem_of_mem_filter 7 h)
      have hG7_le : c.Gext 7 ≤ 1 := by simp [Gext, h7_not_M]
      exact five_factor_lt_two hbal h3_pos h7_pos h31_pos hM127_nonneg
        h2m_bound hG3 hG7_le h31_le hM127_le (by norm_num)

end UPNCtx

end Erdos1052H1

/- Main Theorem: Graham 1989 -/

theorem prove_Erdos1052_H1 :
    ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → Squarefree (n / 2 ^ padicValNat 2 n) →
      n = 6 ∨ n = 60 ∨ n = 87360 := by
  intro n hn hsq
  have hn_pos : 0 < n := hn.2
  have hn0 : n ≠ 0 := hn_pos.ne'
  set m := padicValNat 2 n
  set s := n / 2 ^ m
  have h2m_dvd : 2 ^ m ∣ n := pow_padicValNat_dvd
  have hn_eq : n = 2 ^ m * s := (Nat.mul_div_cancel' h2m_dvd).symm
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hn_eq
    exact hn0 hn_eq
  have hs_not_even : ¬ 2 ∣ s := by
    intro h2s
    obtain ⟨t, ht⟩ := h2s
    have hdvd : 2 ^ (m + 1) ∣ n := by
      refine ⟨t, ?_⟩
      rw [hn_eq, ht, pow_succ]
      ring
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hle := (padicValNat_dvd_iff_le hn0).mp hdvd
    omega
  set P := s.primeFactors
  have h2_not_P : 2 ∉ P := by
    intro h2P
    exact hs_not_even (Nat.dvd_of_mem_primeFactors h2P)
  have hP_prime : ∀ p ∈ P, p.Prime ∧ p ≠ 2 := by
    intro p hp
    exact ⟨Nat.prime_of_mem_primeFactors hp, fun h => h2_not_P (h ▸ hp)⟩
  have hs_fac_one : ∀ p ∈ P, s.factorization p = 1 := by
    intro p hp
    have hpp := (hP_prime p hp).1
    have hpos : 0 < s.factorization p :=
      hpp.factorization_pos_of_dvd hs0 (Nat.dvd_of_mem_primeFactors hp)
    have hle1 : s.factorization p ≤ 1 := by
      by_contra hgt
      have hge2 : 2 ≤ s.factorization p := by omega
      have hsq_dvd : p * p ∣ s := by
        have h1 : p ^ 2 ∣ p ^ s.factorization p := Nat.pow_dvd_pow p hge2
        have h2 : p ^ s.factorization p ∣ s := Nat.ordProj_dvd s p
        simpa [sq] using h1.trans h2
      have hunit : IsUnit p := hsq p hsq_dvd
      exact hpp.ne_one (Nat.isUnit_iff.mp hunit)
    omega
  have hs_prod : ∏ p ∈ P, p = s := by
    have hself := Erdos1052H1.eq_ppart_of_mem_udiv (Erdos1052H1.self_mem_udiv hs0)
    conv_rhs => rw [hself]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [hs_fac_one p hp, pow_one]
  -- Rule out m = 0 (odd unitary perfect numbers do not exist)
  have hm_pos : 1 ≤ m := by
    by_contra hm0_lt
    have hm0 : m = 0 := by omega
    have hns : n = s := by rw [hn_eq, hm0, pow_zero, one_mul]
    have hprod := Erdos1052H1.prod_eq_two_mul hn
    rw [hns] at hprod
    have hprod_s : ∏ p ∈ P, (1 + p) = 2 * s := by
      rw [← hprod]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [hs_fac_one p hp, pow_one]
    by_cases hP_empty : P = ∅
    · rw [hP_empty] at hprod_s hs_prod
      simp at hprod_s hs_prod
      omega
    · obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hP_empty
      rw [← Finset.mul_prod_erase P (fun p => 1 + p) hp0] at hprod_s
      by_cases hP'_empty : P.erase p0 = ∅
      · rw [hP'_empty] at hprod_s
        have hs_p0 : s = p0 := by
          rw [← hs_prod, ← Finset.mul_prod_erase P (fun p => p) hp0, hP'_empty]
          simp
        simp [hs_p0] at hprod_s
        have hp0_ge2 := (hP_prime p0 hp0).1.two_le
        omega
      · obtain ⟨p1, hp1E⟩ := Finset.nonempty_iff_ne_empty.mpr hP'_empty
        have hp1 : p1 ∈ P := Finset.mem_of_mem_erase hp1E
        rw [← Finset.mul_prod_erase (P.erase p0) (fun p => 1 + p) hp1E] at hprod_s
        have h2_0 : 2 ∣ 1 + p0 := by
          rcases (hP_prime p0 hp0).1.eq_two_or_odd with h | h
          · exact absurd h (hP_prime p0 hp0).2
          · omega
        have h2_1 : 2 ∣ 1 + p1 := by
          rcases (hP_prime p1 hp1).1.eq_two_or_odd with h | h
          · exact absurd h (hP_prime p1 hp1).2
          · omega
        have h4_dvd : 4 ∣ 2 * s := by
          rw [← hprod_s, ← mul_assoc]
          exact dvd_mul_of_dvd_left (mul_dvd_mul h2_0 h2_1) _
        exact hs_not_even (by omega)
  -- Establish n.primeFactors = insert 2 P and build UPNCtx
  have hn_pf : n.primeFactors = insert 2 P := by
    ext q
    simp only [P, Nat.mem_primeFactors, Finset.mem_insert]
    constructor
    · rintro ⟨hq, hqn, _⟩
      by_cases hq2 : q = 2
      · exact Or.inl hq2
      · refine Or.inr ⟨hq, ?_, hs0⟩
        rw [hn_eq] at hqn
        rcases hq.dvd_mul.mp hqn with h1 | h2
        · exfalso
          have hq_dvd_2 := hq.dvd_of_dvd_pow h1
          rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two q hq_dvd_2 with h | h
          · exact hq.ne_one h
          · exact hq2 h
        · exact h2
    · rintro (rfl | ⟨hq, hqs, _⟩)
      · exact ⟨Nat.prime_two,
          hn_eq ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) s, hn0⟩
      · exact ⟨hq, hn_eq ▸ dvd_mul_of_dvd_right hqs (2 ^ m), hn0⟩
  have h2m_ne0 : 2 ^ m ≠ 0 := by positivity
  have hn_fac2 : n.factorization 2 = m := by
    rw [hn_eq, Nat.factorization_mul h2m_ne0 hs0, Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hs_not_even, add_zero]
  have hn_fac_odd : ∀ p ∈ P, n.factorization p = 1 := by
    intro p hp
    have hp2 := (hP_prime p hp).2
    rw [hn_eq, Nat.factorization_mul h2m_ne0 hs0, Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_of_ne hp2,
      zero_add, hs_fac_one p hp]
  have hbal : (2 ^ m + 1) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * ∏ p ∈ P, p := by
    have hprod := Erdos1052H1.prod_eq_two_mul hn
    rw [hn_pf, Finset.prod_insert h2_not_P, hn_fac2] at hprod
    have hcongr : ∏ p ∈ P, (1 + p ^ n.factorization p) = ∏ p ∈ P, (p + 1) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [hn_fac_odd p hp, pow_one, add_comm]
    rw [hcongr, add_comm 1 (2 ^ m)] at hprod
    rw [hprod, hn_eq, hs_prod, pow_succ']
    ring
  let ctx : Erdos1052H1.UPNCtx :=
    { m := m
      P := P
      hm := hm_pos
      hprime := hP_prime
      hbal := hbal }
  have hlt10 : ctx.m < 10 := by
    by_contra hge
    exact ctx.not_ge_ten (by omega)
  rcases ctx.classify_lt_ten hlt10 with ⟨hm1, hP1⟩ | ⟨hm2, hP2⟩ | ⟨hm6, hP6⟩
  · refine Or.inl ?_
    change m = 1 at hm1
    change P = {3} at hP1
    rw [hn_eq, ← hs_prod, hm1, hP1]
    norm_num
  · refine Or.inr (Or.inl ?_)
    change m = 2 at hm2
    change P = {3, 5} at hP2
    rw [hn_eq, ← hs_prod, hm2, hP2]
    norm_num
  · refine Or.inr (Or.inr ?_)
    change m = 6 at hm6
    change P = {3, 5, 7, 13} at hP6
    rw [hn_eq, ← hs_prod, hm6, hP6]
    norm_num

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1.H1 :=
  prove_Erdos1052_H1
