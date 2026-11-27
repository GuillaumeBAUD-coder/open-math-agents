import FormalConjectures.OEIS.«242174»
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Algebra.BigOperators.ModEq

/-! Primitive prime divisors of fourth-order Franel numbers.
Credit: @marcusbuffett. -/

namespace OMA.R_OeisA242174_conjecture_1_R1

open OeisA242174 Finset

private theorem fpos (r n : ℕ) : 0 < franel r n := by
  have hh := Finset.single_le_sum (f := fun k => n.choose k ^ r)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.zero_lt_succ n))
  change 1 ≤ _
  simpa [franel] using hh

private theorem primitive_iff (r n : ℕ) :
    (primitivePrimeDivisorFranel r n).Prime ↔
      ∃ p : ℕ, p.Prime ∧ p ∣ franel r n ∧ ∀ k, 0 < k → k < n → ¬p ∣ franel r k := by
  let l := (franel r n).primeFactorsList.filter (fun p =>
    (List.range' 1 (n-1)).all (fun k => !(p ∣ franel r k)))
  have hmem (p : ℕ) : p ∈ l ↔
      p.Prime ∧ p ∣ franel r n ∧ ∀ k, 0 < k → k < n → ¬p ∣ franel r k := by
    simp only [l,List.mem_filter,Nat.mem_primeFactorsList (fpos r n).ne', List.all_eq_true,
      Bool.not_eq_true',decide_eq_false_iff_not]
    constructor
    · rintro ⟨⟨hp,hd⟩,hh⟩
      exact ⟨hp,hd,fun k hk hkn => hh k (by simp only [List.mem_range'_1]; omega)⟩
    · rintro ⟨hp,hd,hh⟩
      refine ⟨⟨hp,hd⟩,?_⟩
      intro k hk
      simp only [List.mem_range'_1] at hk
      exact hh k (by omega) (by omega)
  change (l.head?.getD 1).Prime ↔ _
  cases hl : l with
  | nil =>
    simp only [List.head?_nil,Option.getD_none,Nat.not_prime_one,false_iff,not_exists]
    intro p h
    have hh := (hmem p).mpr h
    simp [hl] at hh
  | cons q qs =>
    have hh := (hmem q).mp (by simp [hl])
    exact ⟨fun _ => ⟨q,hh⟩,fun _ => hh.1⟩

private theorem extend_sum (r n N : ℕ) (hr : 0 < r) (hn : n < N) :
    franel r n = ∑ k ∈ range N, n.choose k ^ r := by
  apply sum_subset (range_mono hn)
  intro k _ hk
  simp only [mem_range,not_lt] at hk
  simp [Nat.choose_eq_zero_of_lt (show n < k by omega),hr.ne']

private theorem sum_blocks (f : ℕ → ℕ) (a p : ℕ) :
    (∑ k ∈ range (a*p), f k) = ∑ i ∈ range a, ∑ j ∈ range p, f (i*p+j) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_mul,sum_range_add,ih,sum_range_succ]

/-- Lucas factorization of a complete Franel sum at the last base-p digit. -/
theorem digit_step (r p n : ℕ) (hr : 0 < r) (hp : p.Prime) :
    franel r n ≡ franel r (n/p) * franel r (n%p) [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have hrem := Nat.mod_lt n hp.pos
  have hn : n < (n/p+1)*p := by
    rw [Nat.add_mul,one_mul,Nat.mul_comm (n/p) p]
    have := Nat.mod_add_div n p
    omega
  rw [extend_sum _ _ _ hr hn,sum_blocks,extend_sum _ (n%p) p hr hrem]
  change _ ≡ (∑ i ∈ range (n/p+1), (n/p).choose i^r) * _ [MOD p]
  rw [sum_mul]
  apply Nat.ModEq.sum
  intro i _
  rw [mul_sum]
  apply Nat.ModEq.sum
  intro j hj
  have h := (Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := n) (k := i*p+j) (p := p)).pow r
  have hjp := mem_range.mp hj
  simpa only [Nat.mul_add_mod_self_right,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hjp,Nat.mul_add_div hp.pos,
    Nat.div_eq_of_lt hjp,Nat.add_zero,mul_pow,Nat.mul_comm] using h

/-- Divisibility by a prime is equivalent to a zero Franel digit. -/
theorem prime_dvd_iff_digit (r p n : ℕ) (hr : 0 < r) (hp : p.Prime) :
    p ∣ franel r n ↔ ∃ d ∈ Nat.digits p n, p ∣ franel r d := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simp [hn,franel,hp.not_dvd_one]
    · have hdiv := (digit_step r p n hr hp).dvd_iff (dvd_refl p)
      rw [hdiv,hp.dvd_mul,ih (n/p) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp.one_lt),
        Nat.digits_def' hp.one_lt (n := n) (Nat.pos_of_ne_zero hn)]
      simp only [List.mem_cons]
      grind

/-- A primitive prime always exceeds its index. -/
theorem primitive_gt (r n p : ℕ) (hr : 0 < r) (hn : 0 < n) (hp : p.Prime)
    (hpn : p ∣ franel r n) (hfirst : ∀ k, 0 < k → k < n → ¬p ∣ franel r k) : n < p := by
  by_contra! hle
  have hdiv := ((digit_step r p n hr hp).dvd_iff (dvd_refl p)).mp hpn
  have h0 : ¬p ∣ franel r 0 := by simpa [franel] using hp.not_dvd_one
  rcases hp.dvd_mul.mp hdiv with hd | hd
  · exact hfirst _ (Nat.div_pos hle hp.pos) (Nat.div_lt_self hn hp.one_lt) hd
  · have hrem := Nat.mod_lt n hp.pos
    by_cases hz : n%p = 0
    · exact h0 (hz ▸ hd)
    · exact hfirst _ (Nat.pos_of_ne_zero hz) (by omega) hd

/-- Reflect a row near p-1 into a fixed-degree polynomial in its column. -/
private theorem reflected (p j k : ℕ) (hp : p.Prime) (hj : j < p) (hk : k < p) :
    (((p-1-j).choose k : ℕ) : ZMod p) = (-1)^k * (((k+j).choose j : ℕ) : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  let n := p-1-j
  have hn : n+1+j = p := by dsimp [n]; omega
  have hc : (n : ZMod p)+1+(j : ZMod p)=0 := by
    have hh : ((n+1+j : ℕ) : ZMod p) = 0 := by rw [hn,ZMod.natCast_self]
    push_cast at hh
    exact hh
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < p := by omega
    have hk0 : ((k+1 : ℕ) : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos k) hk)
    have hstep : ((n.choose (k+1) : ℕ) : ZMod p) * (k+1) =
        (n.choose k : ZMod p) * ((n : ZMod p)-k) := by
      by_cases hkn : k ≤ n
      · have hh := congrArg (fun t : ℕ => (t : ZMod p)) (Nat.choose_succ_right_eq n k)
        push_cast [hkn] at hh
        exact hh
      · rw [Nat.choose_eq_zero_of_lt (by omega : n < k+1),Nat.choose_eq_zero_of_lt (by omega : n < k)]
        simp
    have haux := Nat.choose_mul_succ_eq (k+j) j
    have hsmall : k+j+1-j = k+1 := by omega
    rw [hsmall,show k+j+1 = k+1+j by omega] at haux
    have haux' := congrArg (fun t : ℕ => (t : ZMod p)) haux
    push_cast at haux'
    apply mul_right_cancel₀ (b := (k : ZMod p)+1) (by simpa using hk0)
    change (n.choose (k+1) : ZMod p) * _ = _
    rw [hstep,show (n.choose k : ZMod p) = _ from ih hk',pow_succ]
    linear_combination (-1 : ZMod p)^k * haux'.symm + (-1 : ZMod p)^k * ((k+j).choose j : ZMod p) * hc

private theorem polynomial_sum (p : ℕ) (hp : p.Prime) (P : Polynomial (ZMod p))
    (hP : P.natDegree < p-1) : ∑ k ∈ range p, P.eval (k : ZMod p) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hsum (t : ℕ) (ht : t < p-1) : ∑ k ∈ range p, (k : ZMod p)^t = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    have hh := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) t (by simpa using ht)
    rw [← (ZMod.finEquiv p).toEquiv.sum_comp] at hh
    have hcast (i : Fin p) : (ZMod.finEquiv p) i = ((i : ℕ) : ZMod p) := by
      cases p with
      | zero => exact (hp.ne_zero rfl).elim
      | succ q =>
        apply Fin.ext
        change i.val = ((i.val : ℕ) : ZMod (q+1)).val
        rw [ZMod.val_natCast,Nat.mod_eq_of_lt i.isLt]
    simpa [hcast] using hh
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [sum_comm]
  apply sum_eq_zero
  intro t ht
  rw [← mul_sum,hsum t (by have := mem_range.mp ht; omega),mul_zero]

/-- An entire interval of the highest one-digit indices is divisible by p
for even order. The length bound comes from summing a polynomial of degree r*j. -/
theorem upper_digit_zero (r p j : ℕ) (hr : 0 < r) (he : Even r) (hp : p.Prime)
    (hj : j < p) (hdeg : j*r < p-1) : p ∣ franel r (p-1-j) := by
  have : Fact p.Prime := ⟨hp⟩
  let Q : Polynomial (ZMod p) := ∏ i ∈ range j, (Polynomial.X + Polynomial.C (1+(i : ZMod p)))
  have hQ (k : ℕ) : Q.eval (k : ZMod p) = (j.factorial : ZMod p)*((k+j).choose j : ZMod p) := by
    have hh := congrArg (fun t : ℕ => (t : ZMod p)) (Nat.ascFactorial_eq_factorial_mul_choose k j)
    rw [Nat.ascFactorial_eq_prod_range] at hh
    push_cast at hh
    simpa [Q,Polynomial.eval_prod,add_assoc] using hh
  have hdQ : Q.natDegree ≤ j := by
    dsimp [Q]
    apply (Polynomial.natDegree_prod_le ..).trans
    calc
      _ ≤ ∑ _i ∈ range j, 1 := sum_le_sum (fun _ _ => (Polynomial.natDegree_X_add_C _).le)
      _ = j := by simp
  have hpow : (Q^r).natDegree < p-1 :=
    Polynomial.natDegree_pow_le.trans_lt (by nlinarith [Nat.mul_le_mul_left r hdQ])
  have hsum := polynomial_sum p hp (Q^r) hpow
  simp only [Polynomial.eval_pow] at hsum
  simp_rw [hQ,mul_pow] at hsum
  rw [← mul_sum] at hsum
  have hfac : (j.factorial : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr
    (fun hd => hj.not_ge (hp.dvd_factorial.mp hd))
  have hz := (mul_eq_zero.mp hsum).resolve_left (pow_ne_zero _ hfac)
  apply (ZMod.natCast_eq_zero_iff ..).mp
  rw [extend_sum r (p-1-j) p hr (by omega)]
  push_cast
  convert hz using 1
  apply sum_congr rfl
  intro k hk
  rw [reflected p j k hp hj (mem_range.mp hk),mul_pow,← pow_mul,Nat.mul_comm k r,pow_mul,he.neg_one_pow,one_pow,one_mul]

/-- Exact count of the nonzero residues among all words of a given length. -/
theorem nonzero_count (r p t : ℕ) (hr : 0 < r) (hp : p.Prime) :
    ((range (p^t)).filter fun n => ¬p ∣ franel r n).card =
      ((range p).filter fun d => ¬p ∣ franel r d).card^t := by
  let good (n : ℕ) := if p ∣ franel r n then 0 else 1
  have hgood (q d : ℕ) (hd : d < p) : good (q*p+d) = good q * good d := by
    have h := (digit_step r p (q*p+d) hr hp).dvd_iff (dvd_refl p)
    have hquo : (q*p+d)/p = q := by rw [Nat.mul_comm q p,Nat.mul_add_div hp.pos,Nat.div_eq_of_lt hd,Nat.add_zero]
    simp only [hquo,
      Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hd,hp.dvd_mul] at h
    simp only [good,h]
    split_ifs <;> simp_all
  have hcard (N : ℕ) : ((range N).filter fun n => ¬p ∣ franel r n).card =
      ∑ n ∈ range N, good n := by
    rw [Finset.card_filter]
    simp [good,ite_not]
  simp only [hcard]
  induction t with
  | zero => simp [good,franel,hp.not_dvd_one]
  | succ t ih =>
    rw [pow_succ,pow_succ,sum_blocks,← ih,sum_mul]
    apply sum_congr rfl
    intro q hq
    rw [mul_sum]
    exact sum_congr rfl (fun d hd => hgood q d (mem_range.mp hd))

/-- Only the digits strictly below the forced terminal interval can be nonzero. -/
theorem nonzero_count_bound (r p t : ℕ) (hr : 0 < r) (he : Even r) (hp : p.Prime) :
    ((range (p^t)).filter fun n => ¬p ∣ franel r n).card ≤
      (p-1-(p-2)/r)^t := by
  rw [nonzero_count r p t hr hp]
  apply Nat.pow_le_pow_left
  have hsub : (range p).filter (fun d => ¬p ∣ franel r d) ⊆ range (p-1-(p-2)/r) := by
    intro d hd
    obtain ⟨hdp,hn⟩ := mem_filter.mp hd
    have hlt := mem_range.mp hdp
    apply mem_range.mpr
    by_contra! hnot
    have hle : p-1-d ≤ (p-2)/r := by omega
    have hmul := Nat.mul_le_mul_right r hle
    have hdiv := Nat.div_mul_le_self (p-2) r
    have hprime := hp.two_le
    have hz := upper_digit_zero r p (p-1-d) hr he hp (by omega) (by omega)
    rw [show p-1-(p-1-d) = d by omega] at hz
    exact hn hz
  simpa using Finset.card_le_card hsub

theorem primitive_location (r n p : ℕ) (hr : 0 < r) (he : Even r) (hp : p.Prime)
    (hn : 1 < n) (hd : p ∣ franel r n) (hfirst : ∀ k, 0 < k → k < n → ¬p ∣ franel r k) :
    p-1 ≤ (p-n)*r := by
  have hlt := primitive_gt r n p hr (by omega) hp hd hfirst
  by_contra! hx
  have h := upper_digit_zero r p (p-n) hr he hp (by omega) hx
  rw [show p-1-(p-n) = n-1 by omega] at h
  exact hfirst (n-1) (by omega) (by omega) h

/-- Every prime is represented, so infinitely many distinct indices have a
primitive prime divisor for each positive even order. -/
theorem arbitrarily_late (r B : ℕ) (hr : 0 < r) (he : Even r) :
    ∃ n > B, (primitivePrimeDivisorFranel r n).Prime := by
  let P := ∏ i ∈ range (B+1), franel r i
  have hP : 0 < P := Finset.prod_pos (fun i _ => fpos r i)
  obtain ⟨p,hpP,hp⟩ := Nat.exists_infinite_primes (P+2)
  have hdiv : p ∣ franel r (p-1) := by
    simpa using upper_digit_zero r p 0 hr he hp hp.pos (by have := hp.two_le; omega)
  have hex : ∃ k, p ∣ franel r k := ⟨_,hdiv⟩
  let n := Nat.find hex
  have hn : p ∣ franel r n := Nat.find_spec hex
  have hnb : B < n := by
    by_contra! hl
    have hd : franel r n ∣ P := Finset.dvd_prod_of_mem _ (mem_range.mpr (by omega : n < B+1))
    exact (Nat.not_dvd_of_pos_of_lt hP (by omega : P < p)) (hn.trans hd)
  exact ⟨n,hnb,(primitive_iff r n).mpr ⟨p,hp,hn,fun k _ hk => Nat.find_min hex hk⟩⟩

private theorem choose_down (n k : ℕ) :
    (((n+1).choose k : ℕ) : ℤ)*((n:ℤ)+1-k) = (n.choose k : ℤ)*(n+1) := by
  by_cases hk : k ≤ n+1
  · have h := congrArg (fun t : ℕ => (t:ℤ)) (Nat.choose_mul_succ_eq n k).symm
    push_cast [hk] at h
    exact h
  · simp [Nat.choose_eq_zero_of_lt (by omega : n+1 < k),Nat.choose_eq_zero_of_lt (by omega : n < k)]

private theorem choose_across (n k : ℕ) :
    (n.choose k : ℤ)*((n:ℤ)-k) = ((n.choose (k+1) : ℕ) : ℤ)*(k+1) := by
  by_cases hk : k ≤ n
  · have h := congrArg (fun t : ℕ => (t:ℤ)) (Nat.choose_succ_right_eq n k).symm
    push_cast [hk] at h; exact h
  · simp [Nat.choose_eq_zero_of_lt (by omega : n < k),Nat.choose_eq_zero_of_lt (by omega : n < k+1)]

/-- The three-term recurrence for fourth-order Franel numbers, verified by a
polynomial telescoping certificate. -/
theorem fourth_order_recurrence (n : ℕ) :
    (n+2)^3 * franel 4 (n+2) =
      2*(2*(n+1)+1)*(3*(n+1)^2+3*(n+1)+1)*franel 4 (n+1) +
      4*(n+1)*(4*(n+1)-1)*(4*(n+1)+1)*franel 4 n := by
  let m : ℤ := n+1
  let N : ℤ := m+1
  let A := 2*(2*m+1)*(3*m^2+3*m+1)
  let D := 4*(4*m-1)*(4*m+1)
  let S (k : ℤ) := -5*N^3*(N-1)*(15*N^2-20*N+7) +
    k*(4*N^2*(65*N^3-136*N^2+93*N-21) +
    k*(-2*N*(11*N-7)*(17*N^2-20*N+5) +
    k*(4*(69*N^3-103*N^2+45*N-5) +
    k*(-2*(4*N-3)*(13*N-5) + k*4*(4*N-3)))))
  let B (q k : ℕ) : ℤ := q.choose k
  let G (k : ℕ) := S k * (k:ℤ)^4 * (B (n+2) k)^4
  have term (k : ℕ) :
      N^4*m^3*(N^3*(B (n+2) k)^4 - A*(B (n+1) k)^4 - D*m*(B n k)^4) =
      G (k+1)-G k := by
    have h1 : B (n+2) k*(N-k) = B (n+1) k * N := by
      simpa [B,N,m] using choose_down (n+1) k
    have h2 : B (n+1) k*(m-k) = B n k*m := choose_down n k
    have h3 : B (n+2) k*(N-k)*(m-k) = B n k*m*N := by
      rw [h1]; linear_combination N*h2
    have ha : B (n+2) k*(N-k) = B (n+2) (k+1)*((k:ℤ)+1) := by
      simpa [B,N,m,add_assoc] using choose_across (n+2) k
    calc
      _ = N^7*m^3*(B (n+2) k)^4 - A*m^3*(B (n+1) k*N)^4 - D*(B n k*m*N)^4 := by ring
      _ = (S ((k:ℤ)+1)*(N-k)^4-S k*(k:ℤ)^4)*(B (n+2) k)^4 := by
        rw [← h1,← h3]
        dsimp [S,N,A,D]
        ring
      _ = S ((k:ℤ)+1)*(B (n+2) k*(N-k))^4 - S k*(k:ℤ)^4*(B (n+2) k)^4 := by ring
      _ = G (k+1)-G k := by rw [ha]; dsimp [G]; ring
  have hz := Finset.sum_congr (s₁ := range (n+3)) rfl (fun k _ => term k)
  rw [sum_range_sub] at hz
  have hright : G (n+3) - G 0 = 0 := by simp [G,B]
  rw [hright,← mul_sum] at hz
  have hnonzero : N^4*m^3 ≠ 0 := by dsimp [N,m]; positivity
  have hrec := (mul_eq_zero.mp hz).resolve_left hnonzero
  simp only [sum_sub_distrib,← mul_sum] at hrec
  have hsum (a : ℕ) (hal : a < n+3) :
      (∑ k ∈ range (n+3), (B a k)^4) = (franel 4 a : ℤ) := by
    rw [extend_sum 4 a (n+3) (by decide) hal]
    push_cast; rfl
  rw [hsum _ (by omega),hsum _ (by omega),hsum _ (by omega)] at hrec
  zify [show 1 ≤ 4*(n+1) by omega]
  dsimp [N,m,A,D] at hrec
  linarith only [hrec]

/-- Above the singular coefficients of the recurrence, a prime cannot divide
two consecutive fourth-order Franel numbers. -/
theorem consecutive (n p : ℕ) (hp : p.Prime) (hl : 4*n+1 < p) :
    ¬ (p ∣ franel 4 n ∧ p ∣ franel 4 (n+1)) := by
  induction n with
  | zero => simp [franel,hp.not_dvd_one]
  | succ n ih =>
    rintro ⟨h1,h2⟩
    have hsum := (dvd_mul_of_dvd_right h2 ((n+2)^3))
    rw [fourth_order_recurrence] at hsum
    have hd := (Nat.dvd_add_right (dvd_mul_of_dvd_right h1 _)).mp hsum
    have non (v : ℕ) (hv : 0 < v) (hu : v < p) := Nat.not_dvd_of_pos_of_lt hv hu
    have hcoef : ¬p ∣ 4*(n+1)*(4*(n+1)-1)*(4*(n+1)+1) := by
      simp only [hp.dvd_mul,not_or]
      exact ⟨⟨⟨non _ (by decide) (by omega),non _ (by omega) (by omega)⟩,
        non _ (by omega) (by omega)⟩,non _ (by omega) (by omega)⟩
    exact ih (by omega) ⟨(hp.dvd_mul.mp hd).resolve_left hcoef,h1⟩

private theorem coprime_witness (n C P b : ℕ) (hc : C=franel 4 n)
    (hP : ∀ k, 0 < k → k < n → franel 4 k ∣ P)
    (hb : 1 < b) (hbc : b ∣ C) (hg : b.Coprime (P % C)) : (a n).Prime := by
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (n := b) (by omega)
  apply (primitive_iff 4 n).mpr
  have hpC := hd.trans hbc
  refine ⟨p,hp,hc ▸ hpC,?_⟩
  intro k hk hkn hpk
  have hpP := hpk.trans (hP k hk hkn)
  have hpr := ((Nat.mod_modEq P C).dvd_iff hpC).mpr hpP
  exact hp.coprime_iff_not_dvd.mp (hg.of_dvd_left hd) hpr

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
/-- Kernel verification of the finite prefix, without factoring Franel numbers.
At each step a cofactor is greater than one and coprime to the earlier product. -/
theorem finite_prefix (k : ℕ) (hk : 0 < k) (hk' : k ≤ 1024) : (a k).Prime := by
  let scan : ℕ → ℕ × ℕ × ℕ × Bool := Nat.rec (1,2,1,true) fun j st =>
    let n := j+1
    let C := st.2.1
    let P := st.2.2.1
    let g := P%C
    let u := C / C.gcd g
    let b := u / u.gcd g
    let next := (2*(2*n+1)*(3*n^2+3*n+1)*C + 4*n*(4*n-1)*(4*n+1)*st.1) / (n+1)^3
    (C,next,P*C,st.2.2.2 && decide (1<b ∧ b ∣ C ∧ b.Coprime g))
  have inv (j : ℕ) :
      (scan j).1 = franel 4 j ∧ (scan j).2.1 = franel 4 (j+1) ∧
      (scan j).2.2.1 = (∏ k ∈ range (j+1), franel 4 k) ∧
      ((scan j).2.2.2 = true → ∀ t, 0 < t → t ≤ j → (a t).Prime) := by
    induction j with
    | zero => exact ⟨by decide +revert,by decide +revert,by decide +revert,fun _ t ht h => by omega⟩
    | succ j ih =>
      obtain ⟨hu,hv,hP,hi⟩ := ih
      let C := (scan j).2.1
      let P := (scan j).2.2.1
      let u := C/C.gcd (P%C)
      let b := u/u.gcd (P%C)
      refine ⟨hv,?_,?_,?_⟩
      · change _ / (j+2)^3 = franel 4 (j+2)
        apply Nat.div_eq_of_eq_mul_left (by positivity)
        change 2*(2*(j+1)+1)*(3*(j+1)^2+3*(j+1)+1)*(scan j).2.1 +
          4*(j+1)*(4*(j+1)-1)*(4*(j+1)+1)*(scan j).1 = _
        rw [hu,hv]
        rw [Nat.mul_comm (franel 4 (j+2))]
        exact (fourth_order_recurrence j).symm
      · change (scan j).2.2.1*(scan j).2.1 = _
        rw [prod_range_succ,hP,hv]
      · intro h t ht hle
        change ((scan j).2.2.2 && decide (1<b ∧ b ∣ C ∧ b.Coprime (P%C))) = true at h
        obtain ⟨hold,hcheck⟩ := Bool.and_eq_true_iff.mp h
        rcases Nat.lt_or_eq_of_le hle with hlt | rfl
        · exact hi hold t ht (by omega)
        · obtain ⟨hbig,hd,hg⟩ := of_decide_eq_true hcheck
          apply coprime_witness (j+1) C P b hv _ hbig hd hg
          intro i _ hil
          rw [show P = _ from hP]
          exact dvd_prod_of_mem _ (mem_range.mpr hil)
  exact (inv 1024).2.2.2 (by decide +kernel) k hk hk'

/-- Smooth case. If all divisors are below the recurrence cutoff, locate a
first occurrence in the short interval left by the polynomial bound. -/
def H1 : Prop := ∀ n : ℕ, 1024 < n →
  (∀ p : ℕ, p.Prime → p ∣ OeisA242174.franel 4 n → p ≤ 4*(n-1)+1) →
  ∃ p : ℕ, p.Prime ∧ 4*n ≤ 3*p+1 ∧ p ≤ 4*(n-1)+1 ∧ p ∣ OeisA242174.franel 4 n ∧
    ∀ k : ℕ, 0 < k → k < n → ¬p ∣ OeisA242174.franel 4 k

/-- Large-factor case. Once the finite short interval has failed, distinguish
a large divisor from factors occurring before the penultimate term.
The penultimate term cannot contain it by the recurrence. -/
def H2 : Prop := ∀ n : ℕ, 1024 < n →
  (∃ q : ℕ, q.Prime ∧ 4*(n-1)+1 < q ∧ q ∣ OeisA242174.franel 4 n) →
  (∀ p : ℕ, p.Prime → 4*n ≤ 3*p+1 → p ≤ 4*(n-1)+1 → p ∣ OeisA242174.franel 4 n →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ p ∣ OeisA242174.franel 4 k) →
  ∃ p : ℕ, p.Prime ∧ 4*(n-1)+1 < p ∧ p ∣ OeisA242174.franel 4 n ∧
    ∀ k : ℕ, 0 < k → k+1 < n → ¬p ∣ OeisA242174.franel 4 k

theorem main : H1 → H2 → type_of% @OeisA242174.conjecture_1 := by
  intro hs hl n hn
  by_cases hcut : n ≤ 1024
  · exact finite_prefix _ hn hcut
  have hN : 1024 < n := by omega
  apply (primitive_iff 4 n).mpr
  by_cases small : ∃ p : ℕ, p.Prime ∧ 4*n ≤ 3*p+1 ∧ p ≤ 4*(n-1)+1 ∧ p ∣ franel 4 n ∧
      ∀ k, 0 < k → k < n → ¬p ∣ franel 4 k
  · obtain ⟨p,hp,_,_,hd,he⟩ := small
    exact ⟨p,hp,hd,he⟩
  by_cases large : ∃ q : ℕ, q.Prime ∧ 4*(n-1)+1 < q ∧ q ∣ franel 4 n
  · have hold (p : ℕ) (hp : p.Prime) (hlo : 4*n ≤ 3*p+1) (hhi : p ≤ 4*(n-1)+1)
        (hd : p ∣ franel 4 n) : ∃ k : ℕ, 0 < k ∧ k < n ∧ p ∣ franel 4 k := by
      by_contra! hno
      exact small ⟨p,hp,hlo,hhi,hd,hno⟩
    obtain ⟨p,hp,hbig,hd,hprev⟩ := hl n hN large hold
    refine ⟨p,hp,hd,?_⟩
    intro k hk hkn hpk
    by_cases hpre : k+1<n
    · exact hprev k hk hpre hpk
    have he : k+1=n := by omega
    exact consecutive k p hp (by rwa [show k=n-1 by omega]) ⟨hpk,he ▸ hd⟩
  · apply False.elim
    apply small
    apply hs n hN
    intro p hp hd
    by_contra! hbig
    exact large ⟨p,hp,hbig,hd⟩

/-- Both residual hypotheses are also necessary. -/
theorem necessary (hall : type_of% @OeisA242174.conjecture_1) : H1 ∧ H2 := by
  have fresh (n : ℕ) (hn : 1024 < n) :
      ∃ p : ℕ, p.Prime ∧ 4*n ≤ 3*p+1 ∧ p ∣ franel 4 n ∧
        ∀ k, 0 < k → k < n → ¬p ∣ franel 4 k := by
    obtain ⟨p,hp,hd,hprev⟩ := (primitive_iff 4 n).mp (hall n (by omega))
    have hnp := primitive_gt 4 n p (by decide) (by omega) hp hd hprev
    have hloc := primitive_location 4 n p (by decide) (by decide) hp (by omega) hd hprev
    exact ⟨p,hp,by omega,hd,hprev⟩
  constructor
  · intro n hn hs
    obtain ⟨p,hp,hlo,hd,hprev⟩ := fresh n hn
    exact ⟨p,hp,hlo,hs p hp hd,hd,hprev⟩
  · intro n hn _ hshort
    obtain ⟨p,hp,hlo,hd,hprev⟩ := fresh n hn
    refine ⟨p,hp,?_,hd,fun k hk hkn => hprev k hk (by omega)⟩
    by_contra! hle
    obtain ⟨k,hk,hkn,hpk⟩ := hshort p hp hlo hle hd
    exact hprev k hk hkn hpk

end OMA.R_OeisA242174_conjecture_1_R1

