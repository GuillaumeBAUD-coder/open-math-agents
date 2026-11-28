import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1

/-!
# Prime factors of the odd exponent in the kernel 3^11 case

Among the prime factors of a = v₂(n), counted with multiplicity, at most seven
are 3 or congruent to 2 modulo 3. Each factor 3 consumes one extra power of 3
in 2^a+1. For a factor congruent to 2 modulo 3, the corresponding quotient of
successive power sums contributes a fresh prime q congruent to 2 modulo 3.
Its successor consumes a power of 3. The forced successors of 17 and 83
already consume three powers, and 2^a+1 always consumes one.

It suffices to bound the product of the prime factors of a congruent to 1
modulo 3 and, independently, the size of a single prime factor congruent to
2 modulo 3. Both bounds are open.
-/

-- Credit: @Pixelstorm44
namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1_H1_R2


open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (exists_quot_mod exists_prime_mod3
  facts S_sq prime_dvd_prime_pow kernel_balance_one three_dvd_two_pow_add_one)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 (budget_kernel3)

private theorem lift_odd {d m : ℕ} (hm : Odd m) (hd : d ∣ m) :
    2 ^ d + 1 ∣ 2 ^ m + 1 := by
  obtain ⟨k, rfl⟩ := hd
  have hk := hm.of_dvd_nat (dvd_mul_left k d)
  simpa [pow_mul] using hk.nat_add_dvd_pow_add_pow (2 ^ d) 1

/-- Each successive factor either supplies another 3 to the power sum
or introduces a fresh prime divisor congruent to 2 modulo 3. -/
private theorem layers {m : ℕ} (hm : Odd m)
    (hsq : ∀ q, q.Prime → q % 3 = 2 → ¬ q*q ∣ 2^m + 1)
    (L : List ℕ) (hd : L.prod ∣ m) (hL : ∀ p ∈ L, p % 3 ≠ 1) :
    ∃ (k : ℕ) (S : Finset ℕ), k + S.card = L.length ∧
      3^(1+k) ∣ 2^L.prod + 1 ∧
      ∀ q ∈ S, q.Prime ∧ q % 3 = 2 ∧ q ∣ 2^L.prod + 1 := by
  induction L with
  | nil => exact ⟨0, ∅, by simp, by decide, by simp⟩
  | cons p L ih =>
    have htail : L.prod ∣ m := (dvd_mul_left L.prod p).trans hd
    have hp : Odd p := hm.of_dvd_nat ((dvd_mul_right p L.prod).trans hd)
    have ht : Odd L.prod := hm.of_dvd_nat htail
    obtain ⟨k,S,hcard,hpow,hS⟩ := ih htail (fun r hr => hL r (List.mem_cons_of_mem _ hr))
    obtain ⟨Q,hQ,hmod⟩ := exists_quot_mod (z := 2^L.prod) hp
    have eqn : 2^(p :: L).prod + 1 = (2^L.prod + 1)*Q := by
      rw [List.prod_cons, mul_comm p, pow_mul, Nat.add_comm _ 1]
      exact hQ
    have hbase : 3 ∣ 2^L.prod + 1 := three_dvd_two_pow_add_one (Nat.odd_iff.mp ht)
    have hc : Q % 3 = p % 3 := Nat.ModEq.of_dvd hbase hmod
    have hne := hL p (List.mem_cons_self ..)
    by_cases hzero : p % 3 = 0
    · refine ⟨k+1, S, by simp; omega, ?_, ?_⟩
      · rw [eqn, show 1 + (k+1) = (1+k)+1 by omega, pow_succ]
        exact mul_dvd_mul hpow (Nat.dvd_of_mod_eq_zero (hc.trans hzero))
      · intro q hq
        obtain ⟨hq1,hq2,hq3⟩ := hS q hq
        exact ⟨hq1,hq2,hq3.trans (eqn ▸ dvd_mul_right _ _)⟩
    · have htwo : Q % 3 = 2 := hc.trans (by omega)
      obtain ⟨q,hprime,hqQ,hq2⟩ := exists_prime_mod3 Q htwo
      have hnew : q ∉ S := by
        intro hq
        apply hsq q hprime hq2
        apply Dvd.dvd.trans _ (lift_odd hm hd)
        rw [eqn]
        exact mul_dvd_mul (hS q hq).2.2 hqQ
      refine ⟨k, insert q S, by simp [hnew]; omega, ?_, ?_⟩
      · exact hpow.trans (eqn ▸ dvd_mul_right _ _)
      · intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact ⟨hprime,hq2,hqQ.trans (eqn ▸ dvd_mul_left _ _)⟩
        · obtain ⟨hr1,hr2,hr3⟩ := hS r hr
          exact ⟨hr1,hr2,hr3.trans (eqn ▸ dvd_mul_right _ _)⟩

private theorem partition_product (L : List ℕ) :
    (L.filter (fun p => p % 3 != 1)).prod * (L.filter (fun p => p % 3 == 1)).prod = L.prod := by
  induction L with
  | nil => simp
  | cons p L ih =>
    by_cases hp : p % 3 = 1 <;> simp [hp, ih, mul_left_comm, mul_assoc]

private theorem budget {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hm : Odd m) :
    (m.primeFactorsList.filter (fun p => p % 3 != 1)).length ≤ 7 := by
  let L := m.primeFactorsList.filter (fun p => p % 3 != 1)
  have hm0 : m ≠ 0 := by have := Nat.odd_iff.mp hm; omega
  have hfac := Nat.prod_primeFactorsList hm0
  have hd : L.prod ∣ m := ⟨_, (partition_product m.primeFactorsList |>.trans hfac).symm⟩
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hodd : ¬2 ∣ 2^m+1 := by
    have := dvd_pow_self 2 hm0
    omega
  have hsq : ∀ q, q.Prime → q % 3 = 2 → ¬ q*q ∣ 2^m + 1 := by
    intro q hq hr h
    have hqd := (dvd_mul_right q q).trans h
    exact S_sq hP hK E hq (by rintro rfl; exact hodd hqd) (hnz (by omega))
      ((h.trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _))
  obtain ⟨k,S,hcard,hpow,hS⟩ := layers hm hsq L hd (by
    intro p hp
    exact bne_iff_ne.mp (List.mem_filter.mp hp).2)
  have hsum := lift_odd hm hd
  have hSP : S ⊆ P := by
    intro q hq
    obtain ⟨hq1,hq2,hq3⟩ := hS q hq
    exact S2 q hq1 (by rintro rfl; exact hodd (hq3.trans hsum)) (hnz (by omega)) (hq3.trans hsum)
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  let X : Finset ℕ := {17,83}
  have hXP : X ⊆ P := by
    intro q hq
    simp only [X, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact g17
    · exact g83
  have hdisj : Disjoint S X := by
    rw [Finset.disjoint_left]
    intro q hq hx
    have hqd := (hS q hq).2.2.trans hsum
    simp only [X, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) hqd 67 g67 (by norm_num)
    · exact S4 83 (by norm_num) (by norm_num) (hnz (by norm_num)) hqd 331 g331 (by norm_num)
  have h3S : 3^S.card ∣ ∏ q ∈ S, (q+1) := by
    rw [← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun q hq => by have := (hS q hq).2.1; omega)
  have h3X : 3^3 ∣ ∏ q ∈ X, (q+1) := by norm_num [X, Finset.prod_insert]
  change L.length ≤ 7
  by_contra! hgt
  apply budget_kernel3 hP h3P E (Finset.union_subset hSP hXP)
  rw [Finset.prod_union hdisj]
  apply Dvd.dvd.trans (pow_dvd_pow 3 (show 11+1 ≤ (1+k)+(S.card+3) by omega))
  rw [pow_add, pow_add 3 S.card]
  exact mul_dvd_mul (hpow.trans hsum) (mul_dvd_mul h3S h3X)

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 11 →
    padicValNat 2 n % 2 = 1 →
    262 ≤ padicValNat 2 n →
    (∀ d, 1 ≤ d → d ≤ 400 → d ∉ ({1, 2, 3, 5, 7, 8, 9, 11, 13, 269, 271, 311, 313, 347, 353, 383} : Finset ℕ) →
      padicValNat 2 n % (2 * d) ≠ d) →
    (((padicValNat 2 n).primeFactors.filter (fun p => p % 3 = 2)).card ≤ 7) →
    ((padicValNat 2 n).primeFactorsList.filter (fun p => p % 3 != 1)).length ≤ 7 →
    ((padicValNat 2 n).primeFactorsList.filter (fun p => p % 3 == 1)).prod ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 11 →
    padicValNat 2 n % 2 = 1 →
    262 ≤ padicValNat 2 n →
    (∀ d, 1 ≤ d → d ≤ 400 → d ∉ ({1, 2, 3, 5, 7, 8, 9, 11, 13, 269, 271, 311, 313, 347, 353, 383} : Finset ℕ) →
      padicValNat 2 n % (2 * d) ≠ d) →
    (((padicValNat 2 n).primeFactors.filter (fun p => p % 3 = 2)).card ≤ 7) →
    ((padicValNat 2 n).primeFactorsList.filter (fun p => p % 3 != 1)).length ≤ 7 →
    ∀ p ∈ (padicValNat 2 n).primeFactorsList, p % 3 = 2 → p ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1.H1 := by
  rintro ⟨A,h1⟩ ⟨B,h2⟩
  refine ⟨(max 3 B)^7*A, fun n h hiff he hodd hlo hsieve hdistinct => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) := by simp
  rw [he] at E
  rw [ha] at E
  let m := padicValNat 2 n
  have hm0 : m ≠ 0 := by dsimp [m]; omega
  have hlen := budget hP h3P E (Nat.odd_iff.mpr hodd)
  have hone := h1 n h hiff he hodd hlo hsieve hdistinct hlen
  have htwo := h2 n h hiff he hodd hlo hsieve hdistinct hlen
  let L := m.primeFactorsList.filter (fun p => p % 3 != 1)
  have hcap : ∀ p ∈ L, p ≤ max 3 B := by
    intro p hp
    obtain ⟨hmem,hr⟩ := List.mem_filter.mp hp
    have hne := bne_iff_ne.mp hr
    by_cases ht : p % 3 = 2
    · exact (htwo p hmem ht).trans (le_max_right _ _)
    · have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
      have hp3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (Nat.prime_of_mem_primeFactorsList hmem)).mp hd
      omega
  have hb := (List.prod_le_pow_card L _ hcap).trans
    (Nat.pow_le_pow_right (by omega : 0 < max 3 B) hlen)
  calc
    m = L.prod * (m.primeFactorsList.filter (fun p => p % 3 == 1)).prod :=
      ((partition_product _).trans (Nat.prod_primeFactorsList hm0)).symm
    _ ≤ (max 3 B)^7 * A := Nat.mul_le_mul hb hone

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1_H1_R2
