import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R3

/-!
# A finite sieve for the suppliers of simple Mersenne primes

For a fixed odd core, assign each simple Mersenne prime above three to the
fixed unitary divisor sum or to a shifted prime containing it. Two quantities
remain to bound: the number of occupied shifts outside a freely chosen
finite odd-prime sieve, and the largest number of Mersenne divisors of one
shift. Each sieve prime r removes at most v_r(c)+1 shifts by the balance
equation. This estimate is uniform in the exponent and the completion.

The core factorization and Mersenne tracing lemmas below are from the first
reduction by Progren and the proof by witeg4, reused under the project license.
-/
-- uses note #128653
-- uses note #155458

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R2

open OMA.R_Erdos1052_erdos_1052_R2_H2_R3 hiding H1 H2 main

/-- Only occupied shifts avoiding a fixed list of odd prime divisors count. -/
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ (T : Finset ℕ) (B : ℕ), (∀ r ∈ T, r.Prime ∧ r ≠ 2) ∧
      ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      (S.filter (fun p =>
        (S.filter (fun q => 3 < q ∧ ordCompl[2] (1+q) = 1 ∧ q ∣ 1+p)).Nonempty ∧
        ∀ r ∈ T, ¬ r ∣ 1+p)).card ≤ B

/-- Uniformly bound the number of simple Mersenne divisors of one shifted prime. -/
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ L : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      ∀ p ∈ S,
        (S.filter (fun q => 3 < q ∧ ordCompl[2] (1+q) = 1 ∧ q ∣ 1+p)).card ≤ L

theorem sigma_power_two_times {a c : ℕ} (ha : 0 < a) (hc : Odd c) :
    (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) =
      (2 ^ a + 1) * (∏ p ∈ c.primeFactors, (1 + p ^ c.factorization p)) := by
  have hb : (2 : ℕ) ^ a ≠ 0 := pow_ne_zero _ (by decide)
  have hc0 : c ≠ 0 := hc.pos.ne'
  have h2c : ¬ 2 ∣ c := by obtain ⟨i, hi⟩ := hc; omega
  have h2 : 2 ∉ c.primeFactors := fun h => h2c (Nat.dvd_of_mem_primeFactors h)
  have hfac (p : ℕ) : (2 ^ a * c).factorization p =
      (if 2 = p then a else 0) + c.factorization p := by
    rw [Nat.factorization_mul hb hc0, Nat.prime_two.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.single_apply, eq_comm]
  have h2val : c.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2c
  rw [Nat.primeFactors_mul hb hc0, Nat.primeFactors_prime_pow ha.ne' Nat.prime_two,
    Finset.singleton_union, Finset.prod_insert h2, hfac]
  simp only [if_true, h2val, add_zero, Nat.add_comm 1 (2 ^ a)]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have he : 2 ≠ p := fun e => h2 (e ▸ hp)
  rw [hfac, if_neg he, zero_add]

/-- A Mersenne prime `q > 3` cannot divide `2 ^ a + 1` (from desk note #128653 by `@witeg4`). -/
private theorem mersenne_not_dvd_seed {q k a : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (hk : q + 1 = 2 ^ k) : ¬ q ∣ 2 ^ a + 1 := by
  have hform : q = mersenne k := by unfold mersenne; omega
  have hkp : k.Prime := Nat.Prime.of_mersenne (hform ▸ hq)
  have hk2 : k ≠ 2 := by rintro rfl; norm_num at hk; omega
  have hko := hkp.odd_of_ne_two hk2
  intro hd
  have hqz := ZMod.natCast_self q
  have he : (2 : ZMod q) ^ k = 1 := by
    simpa [hqz] using congrArg (fun t : ℕ => (t : ZMod q)) hk.symm
  have hz : (2 : ZMod q) ^ a + 1 = 0 := by
    simpa using (ZMod.natCast_eq_zero_iff _ q).mpr hd
  have hn : (2 : ZMod q) ^ a = -1 := by linear_combination hz
  have bad : (1 : ZMod q) = -1 := calc
    1 = ((2 : ZMod q) ^ k) ^ a := by simp [he]
    _ = ((2 : ZMod q) ^ a) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = -1 := by rw [hn, hko.neg_one_pow]
  have two : (2 : ZMod q) = 0 := by linear_combination bad
  have hdiv : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using two)
  have := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

/-- Every Mersenne prime `q > 3` in `S` divides either `σ*(c)` or `1 + p` for a strictly larger
non-Mersenne prime `p ∈ S` (from desk note #128653 by `@witeg4`). -/
private theorem mersenne_trace_factor {q k a σ b : ℕ} {S : Finset ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (hk : q + 1 = 2 ^ k) (hqS : q ∈ S) (hodd : ∀ p ∈ S, Odd p)
    (hbal : ((2 ^ a + 1) * σ) * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p)) :
    q ∣ σ ∨ ∃ p ∈ S, q < p ∧ q ∣ (1 + p) ∧ ordCompl[2] (1 + p) ≠ 1 := by
  have hprod : q ∣ ∏ p ∈ S, p := Finset.dvd_prod_of_mem id hqS
  have hd := dvd_mul_of_dvd_right hprod (2 * b)
  rw [← hbal] at hd
  rcases hq.dvd_mul.mp hd with hleft | hright
  · exact Or.inl ((hq.dvd_mul.mp hleft).resolve_left (mersenne_not_dvd_seed hq hq3 hk))
  · obtain ⟨p, hp, hdp⟩ := (hq.prime.dvd_finsetProd_iff _).mp hright
    have hlo := Nat.le_of_dvd (by omega : 0 < 1 + p) hdp
    have hqo := hq.odd_of_ne_two (by omega)
    have hpo := hodd p hp
    have hlt : q < p := by
      by_contra! h
      have eq : q = p ∨ q = 1 + p := by omega
      rcases eq with rfl | h'
      · have : q ∣ 1 := (Nat.dvd_add_iff_left (dvd_refl q)).mpr hdp
        exact hq.not_dvd_one this
      · obtain ⟨i, hi⟩ := hpo
        obtain ⟨j, hj⟩ := hqo
        omega
    refine Or.inr ⟨p, hp, hlt, hdp, ?_⟩
    intro h1
    have hpow := Nat.ordProj_mul_ordCompl_eq_self (1 + p) 2
    rw [h1, mul_one] at hpow
    rw [← hpow] at hdp
    have hq2 := hq.dvd_of_dvd_pow hdp
    have := Nat.le_of_dvd (by decide : 0 < 2) hq2
    omega

private theorem odd_demands_divide {a c : ℕ} {S : Finset ℕ}
    (hbal : (∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p))*
      (∏ q ∈ S, (1+q)) = 2*(2^a*c)*(∏ q ∈ S, q)) :
    (∏ q ∈ S, ordCompl[2] (1+q)) ∣ c*∏ q ∈ S, q := by
  have hd := Finset.prod_dvd_prod_of_dvd (s:=S) (fun q : ℕ => ordCompl[2] (1+q))
    (fun q => 1+q) (fun q _ => Nat.ordCompl_dvd (1+q) 2)
  have hm := hd.trans (dvd_mul_left (∏ q ∈ S, (1+q))
    (∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p)))
  rw [hbal, show 2*(2^a*c)*(∏ q ∈ S, q) = 2^(a+1)*(c*∏ q ∈ S, q) by rw [pow_succ]; ac_rfl] at hm
  have hcop : (∏ q ∈ S, ordCompl[2] (1+q)).Coprime 2 :=
    Nat.coprime_prod_left_iff.mpr fun q _ =>
      (Nat.prime_two.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl Nat.prime_two (by omega : 1+q≠0))).symm
  exact (hcop.pow_right (a+1)).dvd_of_dvd_mul_left hm


/-- Each odd prime in the sieve consumes at most its supply from the fixed
core plus one copy from the squarefree completion. -/
private theorem sieve_union_bound {a c : ℕ} {S T : Finset ℕ} (hc : c ≠ 0)
    (hp : ∀ q ∈ S, q.Prime) (hT : ∀ r ∈ T, r.Prime ∧ r ≠ 2)
    (hbal : (∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p)) *
      (∏ p ∈ S, (1+p)) = 2*(2^a*c)*(∏ p ∈ S, p)) :
    (T.biUnion (fun r => S.filter (fun p => r ∣ 1+p))).card ≤
      ∑ r ∈ T, (c.factorization r + 1) := by
  classical
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
  intro r hr
  obtain ⟨prime, odd⟩ := hT r hr
  have hnot : ¬ 2 ∣ r := fun h => odd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two prime).mp h).symm
  have sub : S.filter (fun p => r ∣ 1+p) ⊆
      S.filter (fun p => r ∣ ordCompl[2] (1+p)) := by
    intro x hx
    obtain ⟨hxs, hdiv⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxs, Nat.dvd_ordCompl_of_dvd_not_dvd hdiv hnot⟩
  have budget := demand_budget hc hp
    (d := fun p => ordCompl[2] (1+p))
    (fun p _ => (Nat.ordCompl_pos 2 (by omega : 1+p ≠ 0)).ne')
    (odd_demands_divide hbal) prime
  calc
    _ ≤ _ := Finset.card_le_card sub
    _ ≤ c.factorization r + (if r ∈ S then 1 else 0) := budget
    _ ≤ c.factorization r + 1 := by split_ifs <;> omega


/-- A simple prime has at most one supplier. Picking one Mersenne divisor
from each occupied shift therefore injects the shifts into the Mersenne primes. -/
theorem occupied_le_mersenne {a c : ℕ} {S : Finset ℕ} (hc : c ≠ 0)
    (hp : ∀ q ∈ S, q.Prime ∧ ¬q ∣ 2^a*c)
    (hint : ∀ q ∈ S, 3 ≤ q)
    (hbal : (∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p)) *
      (∏ p ∈ S, (1+p)) = 2*(2^a*c)*(∏ p ∈ S, p)) :
    (S.filter (fun p =>
      (S.filter (fun q => 3 < q ∧ ordCompl[2] (1+q) = 1 ∧ q ∣ 1+p)).Nonempty)).card ≤
        (S.filter (fun q => ordCompl[2] (1+q) = 1)).card := by
  classical
  let F (p : ℕ) := S.filter (fun q => 3 < q ∧ ordCompl[2] (1+q) = 1 ∧ q ∣ 1+p)
  let P := S.filter (fun p => (F p).Nonempty)
  let M := S.filter (fun q => ordCompl[2] (1+q) = 1)
  have inhabited (p : P) : (F p).Nonempty := (Finset.mem_filter.mp p.property).2
  choose f hf using inhabited
  have data (p : P) : f p ∈ S ∧ 3 < f p ∧ ordCompl[2] (1+f p) = 1 ∧ f p ∣ 1+p.val :=
    Finset.mem_filter.mp (hf p)
  let g (p : P) : M := ⟨f p, Finset.mem_filter.mpr ⟨(data p).1,(data p).2.2.1⟩⟩
  apply Finset.card_le_card_of_injective (f := g)
  intro p t eq
  have same : f p = f t := congrArg Subtype.val eq
  have hfp := (hp _ (data p).1).1
  have outside : ¬ f p ∣ c := fun h => (hp _ (data p).1).2 (dvd_mul_of_dvd_right h _)
  have nottwo : ¬ 2 ∣ f p := fun h => by
    have id := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hfp).mp h
    have := hint _ (data p).1
    omega
  have budget := demand_budget hc (fun q h => (hp q h).1)
    (d := fun q => ordCompl[2] (1+q))
    (fun q _ => (Nat.ordCompl_pos 2 (by omega : 1+q ≠ 0)).ne')
    (odd_demands_divide hbal) hfp
  rw [Nat.factorization_eq_zero_of_not_dvd outside, if_pos (data p).1, zero_add] at budget
  apply Subtype.ext
  apply Finset.card_le_one.mp budget
  · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp p.property).1,
      Nat.dvd_ordCompl_of_dvd_not_dvd (data p).2.2.2 nottwo⟩
  · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp t.property).1,
      Nat.dvd_ordCompl_of_dvd_not_dvd (same ▸ (data t).2.2.2) nottwo⟩

/-- The two estimates are also necessary. An empty sieve works in the forward
direction, since distinct occupied shifts use distinct simple primes. -/
theorem estimates_necessary (h : OMA.R_Erdos1052_erdos_1052_R2_H2_R3.H1) : H1 ∧ H2 := by
  classical
  constructor
  · intro c hc hpower
    obtain ⟨K,hK⟩ := h c hc hpower
    refine ⟨∅,K,by simp,?_⟩
    intro a S b u ha hsize hint hp hbal
    have hocc := occupied_le_mersenne hc.pos.ne' hp
      (fun q hq => (Finset.mem_Icc.mp (hint hq)).1) hbal
    simpa only [Finset.notMem_empty, false_implies, implies_true, and_true] using
      hocc.trans (hK a S ha hsize hint hp hbal)
  · intro c hc hpower
    obtain ⟨K,hK⟩ := h c hc hpower
    refine ⟨K,?_⟩
    intro a S b u ha hsize hint hp hbal p _
    apply le_trans _ (hK a S ha hsize hint hp hbal)
    apply Finset.card_le_card
    intro q hq
    obtain ⟨hqs,_,hm,_⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hqs,hm⟩

/-- The core, the surviving shifts, and the union of excluded shifts account
for every Mersenne prime. Each shift covers at most L primes. -/
theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R3.H1 := by
  classical
  intro hsieve hload c hc hpower
  obtain ⟨T,B,hT,hsieve⟩ := hsieve c hc hpower
  obtain ⟨L,hload⟩ := hload c hc hpower
  let σ := ∏ p ∈ c.primeFactors, (1 + p ^ c.factorization p)
  let C := ∑ r ∈ T, (c.factorization r + 1)
  refine ⟨1 + σ.primeFactors.card + (B+C)*L, ?_⟩
  intro a S b u ha hsize hint hp hbal
  let F (p : ℕ) := S.filter (fun q => 3 < q ∧ ordCompl[2] (1+q) = 1 ∧ q ∣ 1+p)
  let P := S.filter (fun p => (F p).Nonempty)
  let G := S.filter (fun p => (F p).Nonempty ∧ ∀ r ∈ T, ¬ r ∣ 1+p)
  let D := T.biUnion (fun r => S.filter (fun p => r ∣ 1+p))
  have hG : G.card ≤ B := hsieve a S ha hsize hint hp hbal
  have hD : D.card ≤ C := sieve_union_bound hc.pos.ne' (fun q hq => (hp q hq).1) hT hbal
  have split : P ⊆ G ∪ D := by
    intro p h
    obtain ⟨hS, hf⟩ := Finset.mem_filter.mp h
    by_cases clean : ∀ r ∈ T, ¬ r ∣ 1+p
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,hf,clean⟩)
    · push Not at clean
      obtain ⟨r,hr,hdiv⟩ := clean
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨r,hr,Finset.mem_filter.mpr ⟨hS,hdiv⟩⟩)
  have hP : P.card ≤ B+C :=
    (Finset.card_le_card split).trans ((Finset.card_union_le G D).trans (Nat.add_le_add hG hD))
  have cover : S.filter (fun q => ordCompl[2] (1+q)=1) ⊆
      (({3} : Finset ℕ) ∪ σ.primeFactors) ∪ P.biUnion F := by
    intro q hq
    obtain ⟨hqs, hm⟩ := Finset.mem_filter.mp hq
    by_cases small : q = 3
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simpa using small))
    have h3 : 3 < q := lt_of_le_of_ne (Finset.mem_Icc.mp (hint hqs)).1 (Ne.symm small)
    have odd : ∀ p ∈ S, Odd p := fun p h =>
      (hp p h).1.odd_of_ne_two (by have := (Finset.mem_Icc.mp (hint h)).1; omega)
    have proj := Nat.ordProj_mul_ordCompl_eq_self (1+q) 2
    rw [hm,mul_one] at proj
    have hbal' : ((2 ^ a + 1)*σ)*(∏ p ∈ S, (1+p)) =
        (2*(2^a*c))*(∏ p ∈ S, p) := by
      simpa only [u, b, sigma_power_two_times (by omega : 0<a) hc, σ] using hbal
    obtain core | ⟨p,hpS,_,hd,_⟩ := mersenne_trace_factor (hp q hqs).1 h3
      (by simpa only [Nat.add_comm 1 q] using proj.symm) hqs odd hbal'
    · have hσ : σ ≠ 0 := (Finset.prod_pos (fun p _ => by omega)).ne'
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Nat.mem_primeFactors.mpr ⟨(hp q hqs).1, core, hσ⟩))
    · have hF : q ∈ F p := Finset.mem_filter.mpr ⟨hqs,h3,hm,hd⟩
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨p,Finset.mem_filter.mpr ⟨hpS,⟨q,hF⟩⟩,hF⟩)
  have hFib : (P.biUnion F).card ≤ (B+C)*L := calc
    _ ≤ ∑ p ∈ P, (F p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, L := Finset.sum_le_sum (fun p h =>
      hload a S ha hsize hint hp hbal p (Finset.mem_filter.mp h).1)
    _ = P.card * L := by simp
    _ ≤ _ := Nat.mul_le_mul_right L hP
  have hbase := Finset.card_union_le ({3} : Finset ℕ) σ.primeFactors
  rw [Finset.card_singleton] at hbase
  exact (Finset.card_le_card cover).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hbase hFib))

end OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R2
