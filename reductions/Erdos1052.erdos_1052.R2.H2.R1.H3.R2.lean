import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R1

/-!
# The widths and lengths of chains of shifted primes

Write d(q) for the odd part of q+1. Within the simple-prime support,
each d(q) which is itself in the support has at most one predecessor.
The number of chain endpoints is bounded by twice the number of
Mersenne primes in the support plus twice the number of prime factors
of the fixed core, counted with multiplicity (ubuwaits, R2.H2.R3).
We ask for a bound on the number of Mersenne primes and independently
for a bound on the time until iteration of d leaves the simple support.
The latter permits every power of two in the relations q+1 = 2^j r.

Together these give a bound on support cardinality. For each fixed
cardinality, Dickson's lemma applied to the tuple of primes shows
that the increasing sequence of required abundancy ratios can hit
the products of reciprocal shifts only finitely often. No bound on
the primes, on the multipliers, or on the seed factorization is used.
Both hypotheses are restricted to cores surviving the 7,13 collision.
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R1_H3_R2

/-- A bound on the number of simple Mersenne primes, as in the Mersenne
condition in R2.H2.R3, here restricted to surviving multi-prime cores. -/
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    2 ≤ c.primeFactors.card →
    (¬ (¬7 ∣ c ∧ ¬13 ∣ c ∧
      91 ∣ ∏ p ∈ c.primeFactors, (1+p^c.factorization p))) →
    ∃ M : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*∏ p ∈ S, p →
      (S.filter (fun q => ordCompl[2] (1+q) = 1)).card ≤ M

/-- Uniformly bound the number of consecutive simple-prime steps under the
odd-part map. A priori each single chain terminates since its primes decrease. -/
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    2 ≤ c.primeFactors.card →
    (¬ (¬7 ∣ c ∧ ¬13 ∣ c ∧
      91 ∣ ∏ p ∈ c.primeFactors, (1+p^c.factorization p))) →
    ∃ L : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*∏ p ∈ S, p →
      ∀ p ∈ S, ∃ n ≤ L, (fun q : ℕ => ordCompl[2] (1+q))^[n] p ∉ S

/-- An odd prime away from the core has room for at most one occurrence
on the numerator side of a unitary-perfect balance. -/
theorem no_external_square {c a p L : ℕ} {S : Finset ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpc : ¬p ∣ c)
    (hS : ∀ q ∈ S, q.Prime)
    (balance : L = 2 ^ (a + 1) * c * ∏ q ∈ S, q) :
    ¬p * p ∣ L := by
  intro hd
  rw [balance] at hd
  have hc : p.Coprime (2 ^ (a + 1) * c) :=
    (((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right _).mul_right
      (hp.coprime_iff_not_dvd.mpr hpc)
  have hs : p * p ∣ ∏ q ∈ S, q := (hc.mul_left hc).dvd_of_dvd_mul_left hd
  have hmem : p ∈ S := by
    obtain ⟨q, hq, hdq⟩ := (hp.prime.dvd_finsetProd_iff _).mp
      ((dvd_mul_right p p).trans hs)
    rwa [(Nat.prime_dvd_prime_iff_eq hp (hS q hq)).mp hdq]
  rw [← Finset.mul_prod_erase S (fun q => q) hmem] at hs
  have hrem := Nat.dvd_of_mul_dvd_mul_left hp.pos hs
  obtain ⟨q, hq, hdq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hrem
  exact (Finset.ne_of_mem_erase hq)
    ((Nat.prime_dvd_prime_iff_eq hp (hS q (Finset.mem_of_mem_erase hq))).mp hdq).symm
/-- A prime demanded by the numerator outside the core must belong to S. -/
theorem demanded_mem {c a p L : ℕ} {S : Finset ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpc : ¬p ∣ c)
    (hS : ∀ q ∈ S, q.Prime) (h : p ∣ L)
    (balance : L = 2 ^ (a + 1) * c * ∏ q ∈ S, q) : p ∈ S := by
  rw [balance] at h
  have hc : p.Coprime (2 ^ (a + 1) * c) :=
    (((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right _).mul_right
      (hp.coprime_iff_not_dvd.mpr hpc)
  obtain ⟨q, hq, hdq⟩ := (hp.prime.dvd_finsetProd_iff _).mp (hc.dvd_of_dvd_mul_left h)
  rwa [(Nat.prime_dvd_prime_iff_eq hp (hS q hq)).mp hdq]

/-- If two fixed numerator primes collide through a shift, every exponent fails. -/
theorem shifted_collision {a c K p q z : ℕ} {S : Finset ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpc : ¬p ∣ c) (hpK : p ∣ K)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqc : ¬q ∣ c) (hqK : q ∣ K)
    (hpq : p ∣ 1+q) (hS : ∀ r ∈ S, r.Prime) :
    z*K*(∏ r ∈ S, (1+r)) ≠ 2*(2^a*c)*∏ r ∈ S, r := by
  intro balance
  rw [show 2*(2^a*c) = 2^(a+1)*c by rw [pow_succ]; ac_rfl] at balance
  have hm := demanded_mem hq hq2 hqc hS ((hqK.mul_left _).mul_right _) balance
  have hd := hpq.trans (Finset.dvd_prod_of_mem (fun r : ℕ => 1+r) hm)
  exact no_external_square hp hp2 hpc hS balance (mul_dvd_mul (hpK.mul_left _) hd)

/-- All exponents fail whenever 7 and 13 divide K but neither divides c. -/
theorem seven_thirteen_collision {a c K z : ℕ} {S : Finset ℕ}
    (h7 : ¬7 ∣ c) (h13 : ¬13 ∣ c) (hK : 91 ∣ K)
    (hS : ∀ r ∈ S, r.Prime) :
    z*K*(∏ r ∈ S, (1+r)) ≠ 2*(2^a*c)*∏ r ∈ S, r :=
  shifted_collision (by decide : Nat.Prime 7) (by decide) h7
    ((by decide : 7 ∣ 91).trans hK) (by decide : Nat.Prime 13) (by decide)
    h13 ((by decide : 13 ∣ 91).trans hK) (by decide) hS

/-- An injective transition inside a finite support decomposes it into chains.
If each point exits within L steps, the exits and their distances index the support. -/
theorem card_of_bounded_chains (S : Finset ℕ) (d : ℕ → ℕ) (L : ℕ)
    (inj : ∀ x ∈ S, ∀ y ∈ S, d x ∈ S → d x = d y → x = y)
    (depth : ∀ x ∈ S, ∃ n ≤ L, d^[n] x ∉ S) :
    S.card ≤ (L+1) * (S.filter (fun q => d q ∉ S)).card := by
  classical
  let E := S.filter (fun q => d q ∉ S)
  let parent (y : ℕ) := if h : ∃ x ∈ S, d x = y then h.choose else y
  have back {x : ℕ} (hx : x ∈ S) (hd : d x ∈ S) : parent (d x) = x := by
    have h : ∃ t ∈ S, d t = d x := ⟨x, hx, rfl⟩
    rw [show parent (d x) = h.choose by simp [parent, h]]
    exact inj _ h.choose_spec.1 _ hx (by rwa [h.choose_spec.2]) h.choose_spec.2
  have reach (n : ℕ) : ∀ x ∈ S, d^[n] x ∉ S →
      ∃ k ≤ n, ∃ e ∈ E, parent^[k] e = x := by
    induction n with
    | zero => intro x hx he; exact False.elim (he hx)
    | succ n ih =>
      intro x hx he
      by_cases hd : d x ∈ S
      · obtain ⟨k, hk, e, heE, hback⟩ := ih _ hd (by
          simpa only [Function.iterate_succ_apply] using he)
        refine ⟨k+1, by omega, e, heE, ?_⟩
        rw [Function.iterate_succ_apply', hback, back hx hd]
      · exact ⟨0, Nat.zero_le _, x, Finset.mem_filter.mpr ⟨hx, hd⟩, rfl⟩
  let intervals := Finset.range (L+1) ×ˢ E
  have sub : S ⊆ intervals.image (fun pair => parent^[pair.1] pair.2) := by
    intro x hx
    obtain ⟨n, hn, he⟩ := depth x hx
    obtain ⟨k, hk, e, heE, eq⟩ := reach n x hx he
    exact Finset.mem_image.mpr ⟨(k,e), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), heE⟩, eq⟩
  exact (Finset.card_le_card sub).trans ((Finset.card_image_le).trans
    (by simp [intervals, E]))

/-- Along a strictly increasing sequence, only finitely many terms can be
products of k reciprocal shifts. Dickson's lemma applies to the k denominators. -/
theorem finite_fixed_length_ratios (k : ℕ) {f : ℕ → ℚ} (hf : StrictMono f) :
    {a : ℕ | ∃ v : Fin k → ℕ, (∀ j, 0 < v j) ∧
      f a = ∏ j, (1 + 1 / (v j : ℚ))}.Finite := by
  classical
  by_contra hi
  obtain ⟨g, hg, h⟩ := Nat.exists_strictMono_subsequence (fun N => by
    obtain ⟨a, ha, hNa⟩ := (Set.Infinite.exists_gt hi N)
    exact ⟨a, hNa, ha⟩)
  choose v hv heq using h
  obtain ⟨i, j, hij, hle⟩ := wellQuasiOrdered_le v
  have hprod : (∏ t, (1 + 1 / (v j t : ℚ))) ≤ ∏ t, (1 + 1 / (v i t : ℚ)) := by
    refine Finset.prod_le_prod (fun t _ => by positivity) fun t _ => ?_
    have hpos : 0 < (v i t : ℚ) := by exact_mod_cast hv i t
    have hden : (v i t : ℚ) ≤ (v j t : ℚ) := by exact_mod_cast hle t
    exact add_le_add_right (one_div_le_one_div_of_le hpos hden) _
  exact (hf (hg hij)).not_ge (by simpa only [heq] using hprod)

/-- A fixed upper bound on the number of positive terms suffices.
The values of individual denominators may grow without bound. -/
theorem finite_bounded_support_ratios (B : ℕ) {f : ℕ → ℚ} (hf : StrictMono f) :
    {a : ℕ | ∃ S : Finset ℕ, S.card ≤ B ∧ (∀ p ∈ S, 0 < p) ∧
      f a = ∏ p ∈ S, (1 + 1 / (p : ℚ))}.Finite := by
  classical
  apply (Set.finite_iUnion (fun k : Fin (B+1) => finite_fixed_length_ratios k.val hf)).subset
  rintro a ⟨S, hcard, hpos, heq⟩
  let k : Fin (B+1) := ⟨S.card, by omega⟩
  apply Set.mem_iUnion.mpr
  refine ⟨k, S.orderEmbOfFin rfl, fun j => hpos _ (S.orderEmbOfFin_mem rfl j), ?_⟩
  rw [heq]
  conv_lhs => rw [← S.map_orderEmbOfFin_univ (k := S.card) rfl, Finset.prod_map]
  rfl

/-- The balance in a fixed core makes the required ratio strictly increasing with a. -/
theorem strictMono_core_ratio {K c : ℕ} (hc : 0 < c) (hK : 0 < K) :
    StrictMono (fun a : ℕ => (2*(c:ℚ)/(K:ℚ)) * (2:ℚ)^a / (2^a+1)) := by
  intro i j hij
  have hpow : (2:ℚ)^i < 2^j := pow_lt_pow_right₀ (by norm_num) hij
  have hcoef : 0 < 2*(c:ℚ)/(K:ℚ) := by positivity
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_lt_mul_of_pos_left hpow hcoef]

-- The following demand counts and numerator identities are from R2.H2.R3 by @ubuwaits.
open ArithmeticFunction

private theorem omega_prod (s : Finset ℕ) (d : ℕ → ℕ) (hd : ∀ q ∈ s, d q ≠ 0) :
    cardFactors (∏ q ∈ s, d q) = ∑ q ∈ s, cardFactors (d q) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert q s hq ih =>
    rw [Finset.prod_insert hq, Finset.sum_insert hq, cardFactors_mul (hd q (by simp))
      (Finset.prod_ne_zero_iff.mpr fun r hr => hd r (by simp [hr])), ih (fun r hr => hd r (by simp [hr]))]

private theorem omega_mono {x y : ℕ} (hy : y ≠ 0) (hd : x ∣ y) :
    cardFactors x ≤ cardFactors y := by
  obtain ⟨z,rfl⟩ := hd
  rw [cardFactors_mul (left_ne_zero_of_mul hy) (right_ne_zero_of_mul hy)]
  omega

private theorem product_valuation (S : Finset ℕ) (hp : ∀ q ∈ S, q.Prime) (p : ℕ) :
    (∏ q ∈ S, q).factorization p = if p∈S then 1 else 0 := by
  rw [Nat.factorization_prod (fun q hq => (hp q hq).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun q hq => by rw [(hp q hq).factorization, Finsupp.single_apply])]
  exact Finset.sum_ite_eq' S p _

/-- The number of shifts divisible by a given prime is limited by its supply in c and S. -/
theorem demand_budget {c : ℕ} {S : Finset ℕ} {d : ℕ → ℕ} (hc : c ≠ 0)
    (hp : ∀ q ∈ S, q.Prime) (hd : ∀ q ∈ S, d q ≠ 0)
    (balance : (∏ q ∈ S, d q) ∣ c * ∏ q ∈ S, q) {p : ℕ} (prime : p.Prime) :
    (S.filter (fun q => p ∣ d q)).card ≤ c.factorization p + (if p∈S then 1 else 0) := by
  classical
  have hS := Finset.prod_ne_zero_iff.mpr (fun q hq => (hp q hq).ne_zero)
  have hD := Finset.prod_ne_zero_iff.mpr hd
  have val := (Nat.factorization_le_iff_dvd hD (mul_ne_zero hc hS)).mpr balance p
  rw [Nat.factorization_mul hc hS, Finsupp.add_apply,
    product_valuation S hp,
    Nat.factorization_prod hd, Finsupp.finsetSum_apply] at val
  apply le_trans _ val
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro q hq
  split_ifs with h
  · exact (prime.dvd_iff_one_le_factorization (hd q hq)).mp h
  · omega

/-- Unary shifts with an ordinary predecessor are injective, including across unused branches. -/
theorem demand_inj {c : ℕ} {S : Finset ℕ} {d : ℕ → ℕ} (hc : c ≠ 0)
    (hp : ∀ q ∈ S, q.Prime) (hout : ∀ q ∈ S, ¬q ∣ c)
    (hd : ∀ q ∈ S, d q ≠ 0) (balance : (∏ q ∈ S, d q) ∣ c * ∏ q ∈ S, q)
    {q r : ℕ} (hq : q∈S) (hr : r∈S) (hm : d q∈S) (he : d q=d r) : q=r := by
  classical
  have h := demand_budget hc hp hd balance (hp _ hm)
  rw [Nat.factorization_eq_zero_of_not_dvd (hout _ hm), if_pos hm] at h
  apply Finset.card_le_one.mp h q (Finset.mem_filter.mpr ⟨hq,dvd_rfl⟩) r
    (Finset.mem_filter.mpr ⟨hr,he ▸ dvd_rfl⟩)

/-- Each composite shift spends at least one extra prime factor, and each
single outside prime spends a factor of c. -/
theorem nonordinary_demands {c : ℕ} {S : Finset ℕ} {d : ℕ → ℕ} (hc : c ≠ 0)
    (hp : ∀ q ∈ S, q.Prime) (hd : ∀ q ∈ S, d q ≠ 0)
    (balance : (∏ q ∈ S, d q) ∣ c * ∏ q ∈ S, q) :
    (S.filter (fun q => d q∉S)).card ≤
      2*cardFactors c + 2*(S.filter (fun q => d q=1)).card := by
  classical
  let V := S.filter (fun q => (d q).Prime ∧ d q∉S)
  have hV : V ⊆ S := Finset.filter_subset ..
  have div := (Finset.prod_dvd_prod_of_subset V S d hV).trans balance
  have cop : (∏ q ∈ V, d q).Coprime (∏ p ∈ S, p) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro q hq
    obtain ⟨hprime,hout⟩ := (Finset.mem_filter.mp hq).2
    apply Nat.coprime_prod_right_iff.mpr
    intro r hr
    apply hprime.coprime_iff_not_dvd.mpr
    intro h
    exact hout (((hp _ hr).dvd_iff_eq hprime.ne_one).mp h ▸ hr)
  have hVC := omega_mono hc (cop.dvd_of_dvd_mul_right div)
  rw [omega_prod V d (fun q hq => hd q (hV hq))] at hVC
  have vone : ∑ q ∈ V, cardFactors (d q) = V.card := by
    exact (Finset.sum_congr rfl (fun q hq =>
      cardFactors_apply_prime (Finset.mem_filter.mp hq).2.1)).trans (by simp)
  rw [vone] at hVC
  have hsp := Finset.prod_ne_zero_iff.mpr (fun q hq => (hp q hq).ne_zero)
  have budget := omega_mono (mul_ne_zero hc hsp) balance
  rw [omega_prod S d hd, cardFactors_mul hc hsp,
    omega_prod S (fun q => q) (fun q hq => (hp q hq).ne_zero)] at budget
  have ones : ∑ q ∈ S, cardFactors q = S.card :=
    (Finset.sum_congr rfl (fun q hq => cardFactors_apply_prime (hp q hq))).trans (by simp)
  rw [ones] at budget
  have point (q : ℕ) (hq : q∈S) :
      (if d q∉S then 1 else 0) + 1 ≤ cardFactors (d q) +
      2*(if d q=1 then 1 else 0) + (if (d q).Prime ∧ d q∉S then 1 else 0) := by
    have zero := @cardFactors_eq_zero_iff_eq_zero_or_one (d q)
    have one := @cardFactors_eq_one_iff_prime (d q)
    have hz := hd q hq
    split_ifs <;> grind
  have hand := Finset.sum_le_sum point
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    ←Finset.mul_sum, ←Finset.card_filter] at hand
  dsimp only [V] at hVC
  omega
private theorem sigma_power_two_times {a c : ℕ} (ha : 0 < a) (hc : Odd c) (hc0 : c ≠ 0) :
    (∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p)) = (2^a+1)*(∏ p ∈ c.primeFactors, (1+p^c.factorization p)) := by
  have hb : (2:ℕ)^a ≠ 0 := pow_ne_zero _ (by decide)
  have h2c : ¬2 ∣ c := by obtain ⟨i,hi⟩ := hc; omega
  have h2 : 2 ∉ c.primeFactors := fun h => h2c (Nat.dvd_of_mem_primeFactors h)
  have hfac (p : ℕ) : (2^a*c).factorization p =
      (if 2=p then a else 0) + c.factorization p := by
    rw [Nat.factorization_mul hb hc0,Nat.prime_two.factorization_pow]
    simp [Finsupp.single_apply,eq_comm]
  have h2val : c.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2c
  rw [Nat.primeFactors_mul hb hc0,Nat.primeFactors_prime_pow ha.ne' Nat.prime_two,
    Finset.singleton_union,Finset.prod_insert h2,hfac]
  simp only [if_true,h2val,add_zero,Nat.add_comm 1 (2^a)]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have he : 2 ≠ p := fun e => h2 (e ▸ hp)
  rw [hfac, if_neg he, zero_add]
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

/-- Translate the balanced product into the increasing rational ratio. -/
theorem ratio_of_balance {c K a : ℕ} {S : Finset ℕ}
    (hK : 0 < K) (pos : ∀ p ∈ S, 0 < p)
    (bal : (2^a+1)*K*(∏ p ∈ S, (1+p)) = 2*(2^a*c)*(∏ p ∈ S, p)) :
    (2*(c:ℚ)/(K:ℚ))*(2:ℚ)^a/(2^a+1) = ∏ p ∈ S, (1+1/(p:ℚ)) := by
  have hcast : ((2:ℚ)^a+1)*K*(∏ p ∈ S, (1+(p:ℚ))) =
      2*(2^a*(c:ℚ))*(∏ p ∈ S, (p:ℚ)) := by
    simpa only [Nat.cast_mul, Nat.cast_prod, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
      Nat.cast_ofNat] using congrArg (Nat.cast : ℕ → ℚ) bal
  have hden : (∏ p ∈ S, (p:ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => by exact_mod_cast (pos p hp).ne')
  have hpterm (p : ℕ) (hp : p ∈ S) : 1+1/(p:ℚ) = (1+p)/(p:ℚ) := by
    have hn : (p:ℚ) ≠ 0 := by exact_mod_cast (pos p hp).ne'
    field_simp
    ring
  rw [Finset.prod_congr rfl hpterm, Finset.prod_div_distrib]
  have hnK : (K:ℚ) ≠ 0 := by exact_mod_cast hK.ne'
  have hseed : (2:ℚ)^a+1 ≠ 0 := by positivity
  field_simp [hnK, hden, hseed]
  linarith only [hcast]

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R1.H3 := by
  classical
  intro h₁ h₂ c hc powerful multi
  let K := ∏ p ∈ c.primeFactors, (1+p^c.factorization p)
  have hK : 0 < K := Finset.prod_pos (fun p _ => by omega)
  by_cases excluded : ¬7 ∣ c ∧ ¬13 ∣ c ∧ 91 ∣ K
  · apply Set.finite_empty.subset
    rintro a ⟨ha,S,_,_,hs,bal⟩
    rw [sigma_power_two_times (by omega) hc hc.pos.ne'] at bal
    exact (seven_thirteen_collision excluded.1 excluded.2.1 excluded.2.2
      (fun p hp => (hs p hp).1) bal).elim
  obtain ⟨M, hM⟩ := h₁ c hc powerful multi excluded
  obtain ⟨L, hL⟩ := h₂ c hc powerful multi excluded
  let B := (L+1)*(2*ArithmeticFunction.cardFactors c+2*M)
  apply (finite_bounded_support_ratios B (strictMono_core_ratio hc.pos hK)).subset
  rintro a ⟨ha,S,hcard,hsub,hs,bal⟩
  have ms := hM a S ha hcard hsub hs bal
  have chain := hL a S ha hcard hsub hs bal
  let d (p : ℕ) := ordCompl[2] (1+p)
  have hprime (p : ℕ) (hp : p∈S) := (hs p hp).1
  have hout (p : ℕ) (hp : p∈S) (hd : p ∣ c) : False :=
    (hs p hp).2 (dvd_mul_of_dvd_right hd _)
  have hn (p : ℕ) (_ : p∈S) : d p ≠ 0 := (Nat.ordCompl_pos 2 (by omega : 1+p ≠ 0)).ne'
  have divides := odd_demands_divide bal
  have ends := nonordinary_demands hc.pos.ne' hprime hn divides
  have bounded := card_of_bounded_chains S d L (fun _ hx _ hy hm he =>
    demand_inj hc.pos.ne' hprime hout hn divides hx hy hm he) chain
  have size : S.card ≤ B := bounded.trans (Nat.mul_le_mul_left _ (ends.trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 ms) _)))
  have pos := fun p hp => (hprime p hp).pos
  refine ⟨S, size, pos, ratio_of_balance hK pos ?_⟩
  rwa [sigma_power_two_times (by omega) hc hc.pos.ne'] at bal

end OMA.R_Erdos1052_erdos_1052_R2_H2_R1_H3_R2
