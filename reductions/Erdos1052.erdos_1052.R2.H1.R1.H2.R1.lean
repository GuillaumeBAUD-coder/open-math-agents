import OMAReductions.R_Erdos1052_erdos_1052_R2_H1_R1

/-!
# Core-sink versus mixed-shift decomposition of the simple-shift core GCD

Reduction of `Erdos1052.erdos_1052.R2.H1.R1.H2` (uniform bound on `gcd(c, prod_{p in S} (p + 1))`
over all unitary perfect numbers `n` with at least four simple odd prime factors, where `c` is
the repeated odd core).

Using the unitary divisor-sum balance equation `prod_{q | n} (1 + q^{v_q(n)}) = 2 * n`, we prove:
1. Exact 2-adic budget bound: `S.card + R.card <= n.factorization 2 + 1`, forcing
   `4 <= n.factorization 2` whenever `4 <= S.card` and `R.Nonempty`.
2. Odd-part reduction: since `c` is odd, `gcd(c, prod_{p in S} (p + 1))` equals
   `gcd(c, prod_{p in S} ordCompl[2] (p + 1))`, and simple Mersenne primes
   (`ordCompl[2] (p + 1) = 1`) contribute `1` and drop out completely.
3. Exact dependency-graph dichotomy (`sink_or_feeds_simple`): for every simple prime `p in S`,
   either `ordCompl[2] (p + 1) | c` (every odd prime factor of `p + 1` divides `c` with
   multiplicity at most `v_q(c)`, so `p` feeds only the repeated core) or there exists a simple
   prime `r in S` with `r | p + 1` (a mixed shift feeding both `S` and possibly `c`).
   Indeed, `ordCompl[2] (p + 1) | c * prod_{r in S} r` and no prime of `c` belongs to `S`, so
   failure of `ordCompl[2] (p + 1) | c` forces an odd prime divisor `r | p + 1` outside `c`,
   which must lie in `S`.

This splits `gcd(c, prod_{p in S} (p + 1))` multiplicatively into two independent subproblems:
- `H1`: uniform bound on the pure core-sink contribution
  `gcd(c, prod_{p in S, 1 < ordCompl[2](p+1) and ordCompl[2](p+1) | c} ordCompl[2](p+1))`.
- `H2`: uniform bound on the mixed-shift contribution
  `gcd(c, prod_{p in S, exists r in S, r | p + 1} ordCompl[2](p+1))`.
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H1_R1_H2_R1

open scoped BigOperators
open OMA.R_Erdos1052_erdos_1052_R2

/-- Uniform bound on the pure core-sink contribution to `gcd(c, prod_{p in S} (p + 1))`. -/
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    let S := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)
    let R := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
    let c := ∏ p ∈ R, p ^ n.factorization p
    4 ≤ S.card → R.Nonempty → 4 ≤ n.factorization 2 →
      Nat.gcd c (∏ p ∈ S.filter (fun p => 1 < ordCompl[2] (p + 1) ∧ ordCompl[2] (p + 1) ∣ c),
        ordCompl[2] (p + 1)) ≤ A

/-- Uniform bound on the mixed-shift contribution to `gcd(c, prod_{p in S} (p + 1))`
from simple primes `p in S` whose shift `p + 1` feeds at least one prime `r in S`. -/
def H2 : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    let S := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)
    let R := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
    let c := ∏ p ∈ R, p ^ n.factorization p
    4 ≤ S.card → R.Nonempty → 4 ≤ n.factorization 2 →
      Nat.gcd c (∏ p ∈ S.filter (fun p => ∃ r ∈ S, r ∣ p + 1),
        ordCompl[2] (p + 1)) ≤ B

/-- Exact 2-adic count bound `S.card + R.card <= n.factorization 2 + 1`. -/
theorem odd_prime_count_le_v2_succ {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) :
    (n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)).card +
    (n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)).card ≤
      n.factorization 2 + 1 := by
  obtain ⟨hpos, hsum⟩ := sum_udiv_of_isUnitaryPerfect hn
  rw [sum_udiv_eq_prod hpos.ne'] at hsum
  let S := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)
  let R := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
  let O := n.primeFactors.erase 2
  have hO_eq : O = S ∪ R := by
    ext p
    simp only [O, S, R, Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
    tauto
  have hdisj : Disjoint S R := Finset.disjoint_left.mpr fun p hpS hpR =>
    (Finset.mem_filter.mp hpR).2.2 (Finset.mem_filter.mp hpS).2.2
  have hcard : S.card + R.card = O.card := by
    rw [hO_eq, Finset.card_union_of_disjoint hdisj]
  have htwo_dvd_O : 2 ^ O.card ∣ ∏ p ∈ O, (1 + p ^ n.factorization p) := by
    rw [← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun p hpO => by
      obtain ⟨hp2, hpf⟩ := Finset.mem_erase.mp hpO
      have hodd : Odd p := (Nat.prime_of_mem_primeFactors hpf).odd_of_ne_two hp2
      exact (odd_one.add_odd hodd.pow).two_dvd
  have hO_dvd_all : (∏ p ∈ O, (1 + p ^ n.factorization p)) ∣ 2 * n := by
    rw [← hsum]
    exact Finset.prod_dvd_prod_of_subset O n.primeFactors _ (Finset.erase_subset 2 _)
  have hpow_dvd : 2 ^ O.card ∣ 2 * n := htwo_dvd_O.trans hO_dvd_all
  have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero _ (by decide))
    (mul_ne_zero (by decide) hpos.ne')).mpr hpow_dvd 2
  rw [Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_mul (by decide) hpos.ne', Finsupp.add_apply,
    Nat.prime_two.factorization_self] at hle
  change S.card + R.card ≤ n.factorization 2 + 1
  omega

/-- The repeated odd core `c` is odd and positive. -/
theorem core_odd {n : ℕ} :
    Odd (∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1),
      p ^ n.factorization p) := by
  exact Finset.prod_induction (fun p => p ^ n.factorization p) Odd
    (fun _ _ => Odd.mul) odd_one fun p hp => by
      obtain ⟨hpf, hp2, _⟩ := Finset.mem_filter.mp hp
      exact ((Nat.prime_of_mem_primeFactors hpf).odd_of_ne_two hp2).pow

/-- Valuation of the repeated odd core `c` at any prime `q`. -/
theorem factorization_core {n q : ℕ} :
    (∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1),
      p ^ n.factorization p).factorization q =
      if q ∈ n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1) then
        n.factorization q
      else 0 := by
  exact factorization_ppart (Finset.filter_subset _ _) q

/-- Every odd prime factor of `n` lies in either `S` or `R`, and `p + 1` divides `2 * n`
for every `p in S`. -/
theorem shift_ordCompl_dvd_n {n p : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hpS : p ∈ n.primeFactors.filter (fun q => q ≠ 2 ∧ n.factorization q = 1)) :
    ordCompl[2] (p + 1) ∣ n := by
  obtain ⟨hpos, hsum⟩ := sum_udiv_of_isUnitaryPerfect hn
  rw [sum_udiv_eq_prod hpos.ne'] at hsum
  obtain ⟨hpf, _, hval1⟩ := Finset.mem_filter.mp hpS
  have hdvd1 : 1 + p ^ n.factorization p ∣ 2 * n := by
    rw [← hsum]
    exact Finset.dvd_prod_of_mem (fun q => 1 + q ^ n.factorization q) hpf
  rw [hval1, pow_one, add_comm] at hdvd1
  have hord : ordCompl[2] (p + 1) ∣ 2 * n := (Nat.ordCompl_dvd (p + 1) 2).trans hdvd1
  have hcop : (ordCompl[2] (p + 1)).Coprime 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_ordCompl Nat.prime_two (by omega : p + 1 ≠ 0))).symm
  exact hcop.dvd_of_dvd_mul_left hord

/-- Dependency-graph dichotomy: for every simple prime `p in S` of a unitary perfect number `n`,
either `ordCompl[2] (p + 1)` divides the repeated odd core `c`, or there is a simple prime
`r in S` dividing `p + 1`. -/
theorem sink_or_feeds_simple {n p : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hpS : p ∈ n.primeFactors.filter (fun q => q ≠ 2 ∧ n.factorization q = 1)) :
    let S := n.primeFactors.filter (fun q => q ≠ 2 ∧ n.factorization q = 1)
    let R := n.primeFactors.filter (fun q => q ≠ 2 ∧ n.factorization q ≠ 1)
    let c := ∏ q ∈ R, q ^ n.factorization q
    ordCompl[2] (p + 1) ∣ c ∨ ∃ r ∈ S, r ∣ p + 1 := by
  let S := n.primeFactors.filter (fun q => q ≠ 2 ∧ n.factorization q = 1)
  let R := n.primeFactors.filter (fun q => q ≠ 2 ∧ n.factorization q ≠ 1)
  let c := ∏ q ∈ R, q ^ n.factorization q
  change ordCompl[2] (p + 1) ∣ c ∨ ∃ r ∈ S, r ∣ p + 1
  obtain ⟨hpos, _⟩ := sum_udiv_of_isUnitaryPerfect hn
  have hc_pos : 0 < c := core_odd.pos
  have hord_pos : 0 < ordCompl[2] (p + 1) := Nat.ordCompl_pos 2 (by omega)
  have hord_dvd_n : ordCompl[2] (p + 1) ∣ n := shift_ordCompl_dvd_n hn hpS
  by_cases hdvd : ordCompl[2] (p + 1) ∣ c
  · exact Or.inl hdvd
  · right
    have hnotle : ¬ ∀ q, (ordCompl[2] (p + 1)).factorization q ≤ c.factorization q := fun h =>
      hdvd ((Nat.factorization_le_iff_dvd hord_pos.ne' hc_pos.ne').mp h)
    push Not at hnotle
    obtain ⟨r, hr_gt⟩ := hnotle
    have hr_pos : 0 < (ordCompl[2] (p + 1)).factorization r := by omega
    have hr_pf : r ∈ (ordCompl[2] (p + 1)).primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      omega
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_pf
    have hr_dvd_ord : r ∣ ordCompl[2] (p + 1) := Nat.dvd_of_mem_primeFactors hr_pf
    have hr_ne2 : r ≠ 2 := fun h2 =>
      Nat.not_dvd_ordCompl Nat.prime_two (by omega : p + 1 ≠ 0) (h2 ▸ hr_dvd_ord)
    have hr_dvd_n : r ∣ n := hr_dvd_ord.trans hord_dvd_n
    have hr_n_pf : r ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hr_prime, hr_dvd_n, hpos.ne'⟩
    have hr_val_le : (ordCompl[2] (p + 1)).factorization r ≤ n.factorization r :=
      (Nat.factorization_le_iff_dvd hord_pos.ne' hpos.ne').mpr hord_dvd_n r
    have hr_notR : r ∉ R := by
      intro hrR
      have hcval : c.factorization r = n.factorization r := by
        dsimp [c]
        rw [factorization_core, if_pos hrR]
      omega
    have hr_val1 : n.factorization r = 1 := by
      by_contra hne1
      exact hr_notR (Finset.mem_filter.mpr ⟨hr_n_pf, hr_ne2, hne1⟩)
    exact ⟨r, Finset.mem_filter.mpr ⟨hr_n_pf, hr_ne2, hr_val1⟩,
      hr_dvd_ord.trans (Nat.ordCompl_dvd (p + 1) 2)⟩

/-- Stripping powers of `2` from every shift `p + 1` leaves `gcd(c, prod_{p in S} (p + 1))`
unchanged because `c` is odd. -/
theorem gcd_core_shifts_eq_ordCompl {n : ℕ} {S : Finset ℕ} :
    let c := ∏ q ∈ n.primeFactors.filter (fun q => q ≠ 2 ∧ n.factorization q ≠ 1),
      q ^ n.factorization q
    Nat.gcd c (∏ p ∈ S, (p + 1)) = Nat.gcd c (∏ p ∈ S, ordCompl[2] (p + 1)) := by
  let c := ∏ q ∈ n.primeFactors.filter (fun q => q ≠ 2 ∧ n.factorization q ≠ 1),
    q ^ n.factorization q
  change Nat.gcd c (∏ p ∈ S, (p + 1)) = Nat.gcd c (∏ p ∈ S, ordCompl[2] (p + 1))
  have hsplit : (∏ p ∈ S, (p + 1)) =
      2 ^ (∑ p ∈ S, (p + 1).factorization 2) * ∏ p ∈ S, ordCompl[2] (p + 1) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => (Nat.ordProj_mul_ordCompl_eq_self (p + 1) 2).symm
  rw [hsplit]
  have hcop : c.Coprime (2 ^ (∑ p ∈ S, (p + 1).factorization 2)) :=
    (Nat.coprime_two_right.mpr core_odd).pow_right _
  rw [Nat.gcd_comm, hcop.symm.gcd_mul_left_cancel _, Nat.gcd_comm]

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H1_R1.H2 := by
  classical
  intro h1 h2
  obtain ⟨A, hA⟩ := h1
  obtain ⟨B, hB⟩ := h2
  refine ⟨max 1 (A * B), fun n hn hS => ?_⟩
  let S := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)
  let R := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
  let c := ∏ p ∈ R, p ^ n.factorization p
  change Nat.gcd c (∏ p ∈ S, (p + 1)) ≤ max 1 (A * B)
  by_cases hR : R.Nonempty
  · have hbud := odd_prime_count_le_v2_succ hn
    have hRpos : 1 ≤ R.card := Finset.card_pos.mpr hR
    have ha4 : 4 ≤ n.factorization 2 := by
      change 4 ≤ S.card at hS
      change S.card + R.card ≤ n.factorization 2 + 1 at hbud
      omega
    rw [gcd_core_shifts_eq_ordCompl]
    let S_sink := S.filter (fun p => 1 < ordCompl[2] (p + 1) ∧ ordCompl[2] (p + 1) ∣ c)
    let S_mix := S.filter (fun p => ∃ r ∈ S, r ∣ p + 1)
    let S_mers := S.filter (fun p => ordCompl[2] (p + 1) = 1)
    have hprod_dvd : (∏ p ∈ S, ordCompl[2] (p + 1)) ∣
        (∏ p ∈ S_sink, ordCompl[2] (p + 1)) * (∏ p ∈ S_mix, ordCompl[2] (p + 1)) := by
      have hsub : S \ S_mers ⊆ S_sink ∪ S_mix := by
        intro p hp
        obtain ⟨hpS, hpNotM⟩ := Finset.mem_sdiff.mp hp
        have hpos : 0 < ordCompl[2] (p + 1) := Nat.ordCompl_pos 2 (by omega)
        have hne1 : ordCompl[2] (p + 1) ≠ 1 := fun h1 => hpNotM (Finset.mem_filter.mpr ⟨hpS, h1⟩)
        rcases sink_or_feeds_simple hn hpS with hsink | hmix
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpS, by omega, hsink⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpS, hmix⟩)
      have hmers_prod : ∏ p ∈ S_mers, ordCompl[2] (p + 1) = 1 :=
        Finset.prod_eq_one fun p hp => (Finset.mem_filter.mp hp).2
      have hS_eq : ∏ p ∈ S, ordCompl[2] (p + 1) = ∏ p ∈ S \ S_mers, ordCompl[2] (p + 1) := by
        have h := Finset.prod_sdiff (Finset.filter_subset (fun p => ordCompl[2] (p + 1) = 1) S)
          (f := fun p => ordCompl[2] (p + 1))
        change (∏ p ∈ S \ S_mers, ordCompl[2] (p + 1)) * (∏ p ∈ S_mers, ordCompl[2] (p + 1)) =
          ∏ p ∈ S, ordCompl[2] (p + 1) at h
        rw [hmers_prod, mul_one] at h
        exact h.symm
      rw [hS_eq]
      have hd1 : (∏ p ∈ S \ S_mers, ordCompl[2] (p + 1)) ∣
          ∏ p ∈ S_sink ∪ S_mix, ordCompl[2] (p + 1) :=
        Finset.prod_dvd_prod_of_subset _ _ _ hsub
      have hd2 : (∏ p ∈ S_sink ∪ S_mix, ordCompl[2] (p + 1)) ∣
          (∏ p ∈ S_sink, ordCompl[2] (p + 1)) * (∏ p ∈ S_mix, ordCompl[2] (p + 1)) := by
        rw [← Finset.prod_union_inter]
        exact dvd_mul_right _ _
      exact hd1.trans hd2
    have hpos_rhs : 0 < Nat.gcd c (∏ p ∈ S_sink, ordCompl[2] (p + 1)) *
        Nat.gcd c (∏ p ∈ S_mix, ordCompl[2] (p + 1)) :=
      Nat.mul_pos (Nat.gcd_pos_of_pos_left _ core_odd.pos)
        (Nat.gcd_pos_of_pos_left _ core_odd.pos)
    have hgcd_dvd : Nat.gcd c (∏ p ∈ S, ordCompl[2] (p + 1)) ∣
        Nat.gcd c (∏ p ∈ S_sink, ordCompl[2] (p + 1)) *
        Nat.gcd c (∏ p ∈ S_mix, ordCompl[2] (p + 1)) :=
      (Nat.gcd_dvd_gcd_of_dvd_right c hprod_dvd).trans (gcd_mul_dvd_mul_gcd c _ _)
    have hgcd_le := Nat.le_of_dvd hpos_rhs hgcd_dvd
    have h1' : Nat.gcd c (∏ p ∈ S_sink, ordCompl[2] (p + 1)) ≤ A := hA n hn hS hR ha4
    have h2' : Nat.gcd c (∏ p ∈ S_mix, ordCompl[2] (p + 1)) ≤ B := hB n hn hS hR ha4
    exact (hgcd_le.trans (Nat.mul_le_mul h1' h2')).trans (le_max_right _ _)
  · have hRempty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
    have hc1 : c = 1 := by simp [c, hRempty]
    rw [hc1, Nat.gcd_one_left]
    exact le_max_left _ _

end OMA.R_Erdos1052_erdos_1052_R2_H1_R1_H2_R1
