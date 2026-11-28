import OMAReductions.R_Erdos1052_erdos_1052_R2

/-!
Write the exponent as a = 2^k d, d odd. The two tests below apply
separately to the Fermat number x = 2^(2^k)+1 and the integer
y = (2^a+1)/x. Neither test needs the unknown set of simple primes.

The first test permits any multiplicative majorant fixed at 2 that
does not decrease on replacing an odd prime p by p+1. One such
majorant replaces p recursively by the prime factors of p+1, ending
with a power of 2. Its ratio to its argument bounds the cumulative
expansion. The second test permits a factor of two at one marked
prime and ignores factors of 2. Taking twice to the power of the
number of visits to the marked prime in that recursion detects
collisions. A simple prime can spend this extra factor only once.

H1 asks for a bound on the dyadic index from x alone. For each fixed
index, H2 asks for a bound on the odd multiplier from y alone.
-/

-- Credit: @Pixelstorm44
namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R4

def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    {k : ℕ | let x := 2^(2^k : ℕ) + 1
      (∀ f : ℕ →* ℕ, f 2 = 2 → (∀ n, n ≤ f n) →
        (∀ p, Nat.Prime p → 3 ≤ p → f p ≤ f (1+p)) →
        f x ≤ 2 * f c * x) ∧
      (∀ (r : ℕ) (g : ℕ →* ℕ), g 2 = 1 → (∀ n, 0 < n → 0 < g n) →
        (∀ p, Nat.Prime p → 3 ≤ p →
          g p ≤ (if p = r then 2 else 1) * g (1+p)) →
        g x ≤ 2 * g c)}.Finite

def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∀ k : ℕ, {d : ℕ | Odd d ∧
      let x := (2^((2^k)*d) + 1) / (2^(2^k : ℕ) + 1)
      (∀ f : ℕ →* ℕ, f 2 = 2 → (∀ n, n ≤ f n) →
        (∀ p, Nat.Prime p → 3 ≤ p → f p ≤ f (1+p)) →
        f x ≤ 2 * f c * x) ∧
      (∀ (r : ℕ) (g : ℕ →* ℕ), g 2 = 1 → (∀ n, 0 < n → 0 < g n) →
        (∀ p, Nat.Prime p → 3 ≤ p →
          g p ≤ (if p = r then 2 else 1) * g (1+p)) →
        g x ≤ 2 * g c)}.Finite

theorem numerator_factor {a c : ℕ} (ha : 0 < a) (hc : Odd c) :
    2^a + 1 ∣ ∏ q ∈ (2^a*c).primeFactors, (1 + q^(2^a*c).factorization q) := by
  have hc0 := hc.pos.ne'
  have hpow : (2:ℕ)^a ≠ 0 := by positivity
  have h2c : ¬ 2 ∣ c := by
    obtain ⟨j,hj⟩ := hc
    omega
  have hv : (2^a*c).factorization 2 = a := by
    rw [Nat.factorization_mul hpow hc0, Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd h2c,
      add_zero]
  have hm : 2 ∈ (2^a*c).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.prime_two, dvd_mul_of_dvd_left (dvd_pow_self 2 ha.ne') c, mul_ne_zero hpow hc0⟩
  simpa [hv, Nat.add_comm] using Finset.dvd_prod_of_mem
    (fun q : ℕ => 1+q^(2^a*c).factorization q) hm

theorem marked_product (S : Finset ℕ) (r : ℕ) :
    (∏ p ∈ S, (if p = r then 2 else 1 : ℕ)) ≤ 2 := by
  classical
  by_cases hr : r ∈ S
  · rw [← Finset.mul_prod_erase S _ hr]
    simp [Finset.prod_eq_one (fun p (hp : p ∈ S.erase r) =>
      if_neg (Finset.mem_erase.mp hp).1)]
  · rw [Finset.prod_eq_one (fun p hp => if_neg (show p ≠ r from fun e => hr (e ▸ hp)))]
    decide

theorem divisor_tests {a c u x : ℕ} {S : Finset ℕ} (hu : u ≠ 0)
    (hx : x ∣ 2^a+1) (hdiv : 2^a+1 ∣ u)
    (hp : ∀ p ∈ S, Nat.Prime p ∧ 3 ≤ p)
    (hb : u * (∏ p ∈ S, (1+p)) = (2 * (2^a*c)) * ∏ p ∈ S, p) :
    (∀ f : ℕ →* ℕ, f 2 = 2 → (∀ n, n ≤ f n) →
        (∀ p, Nat.Prime p → 3 ≤ p → f p ≤ f (1+p)) →
        f x ≤ 2 * f c * x) ∧
      (∀ (r : ℕ) (g : ℕ →* ℕ), g 2 = 1 → (∀ n, 0 < n → 0 < g n) →
        (∀ p, Nat.Prime p → 3 ≤ p →
          g p ≤ (if p = r then 2 else 1) * g (1+p)) →
        g x ≤ 2 * g c) := by
  obtain ⟨y,hy⟩ := hx
  obtain ⟨z,hz⟩ := hdiv
  have hxy : x*y ≠ 0 := by rw [← hy]; positivity
  have hz0 : z ≠ 0 := right_ne_zero_of_mul (hz ▸ hu)
  constructor
  · intro f htwo hdom hstep
    have h := congrArg f hb
    simp only [map_mul, map_pow, htwo, map_prod] at h
    have hle := Finset.prod_le_prod' (s := S) (fun p hp' => hstep p (hp p hp').1 (hp p hp').2)
    have hpos : 0 < ∏ p ∈ S, f (1+p) :=
      Finset.prod_pos (fun p _ => lt_of_lt_of_le (by omega : 0 < 1+p) (hdom _))
    have hbound : f u ≤ 2*(2^a*f c) := by
      apply Nat.le_of_mul_le_mul_right (c := ∏ p ∈ S, f (1+p)) ?_ hpos
      exact h.trans_le (Nat.mul_le_mul_left _ hle)
    rw [hz,hy,map_mul,map_mul] at hbound
    have hfy : y ≤ f y * f z := le_trans (hdom y)
      (Nat.le_mul_of_pos_right _ (lt_of_lt_of_le (Nat.pos_of_ne_zero hz0) (hdom z)))
    have hy0 := Nat.pos_of_ne_zero (right_ne_zero_of_mul hxy)
    apply Nat.le_of_mul_le_mul_right (c := y) ?_ hy0
    calc f x * y ≤ f x * (f y * f z) := Nat.mul_le_mul_left _ hfy
         _ ≤ 2*(2^a*f c) := by simpa [mul_assoc] using hbound
         _ ≤ (2*f c*x)*y := by
           have hh : 2^a ≤ x*y := by omega
           calc _ = (2*f c)*2^a := by ring
                _ ≤ (2*f c)*(x*y) := Nat.mul_le_mul_left _ hh
                _ = _ := by ring
  · intro r g htwo hpos hstep
    have h := congrArg g hb
    simp only [map_mul, map_pow, htwo, one_pow, one_mul, map_prod] at h
    have hs := Finset.prod_le_prod' (s := S) (fun p hp' => hstep p (hp p hp').1 (hp p hp').2)
    rw [Finset.prod_mul_distrib] at hs
    have hshift : 0 < ∏ p ∈ S, g (1+p) := Finset.prod_pos (fun p _ => hpos _ (by omega))
    have hbound : g u ≤ 2 * g c := by
      apply Nat.le_of_mul_le_mul_right (c := ∏ p ∈ S, g (1+p)) ?_ hshift
      calc _ = _ := h
           _ ≤ g c * (2 * ∏ p ∈ S, g (1+p)) :=
             Nat.mul_le_mul_left _ (hs.trans (Nat.mul_le_mul_right _ (marked_product S r)))
           _ = _ := by ring
    rw [hz,hy,map_mul,map_mul] at hbound
    exact (Nat.le_mul_of_pos_right _ (hpos y (Nat.pos_of_ne_zero (right_ne_zero_of_mul hxy)))).trans
      ((Nat.le_mul_of_pos_right _ (hpos z (Nat.pos_of_ne_zero hz0))).trans hbound)

theorem finite_from_parts {A T : Set ℕ} {B : ℕ → Set ℕ} (hA : A.Finite)
    (hB : ∀ k, (B k).Finite) (parts : ∀ a ∈ T, ∃ k ∈ A, ∃ d ∈ B k, 2^k*d = a) :
    T.Finite := by
  refine (hA.biUnion (fun k _ => (hB k).image (fun d => 2^k*d))).subset ?_
  intro a ha
  obtain ⟨k,hk,d,hd,he⟩ := parts a ha
  exact Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hk,⟨d,hd,he⟩⟩⟩

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2.H2 := by
  intro h1 h2 c hc hpower
  apply finite_from_parts (h1 c hc hpower) (h2 c hc hpower)
  intro a ha
  obtain ⟨ha5,S,_,hI,hp,hb⟩ := ha
  let u := ∏ q ∈ (2^a*c).primeFactors, (1+q^(2^a*c).factorization q)
  have hu : u ≠ 0 := (Finset.prod_pos (fun q (_ : q ∈ (2^a*c).primeFactors) =>
    show 0 < 1+q^(2^a*c).factorization q by omega)).ne'
  have test := fun x (hx : x ∣ 2^a+1) =>
    divisor_tests hu hx (numerator_factor (by omega : 0 < a) hc)
      (fun p h => ⟨(hp p h).1,(Finset.mem_Icc.mp (hI h)).1⟩) hb
  obtain ⟨k,d,hd,he⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : a ≠ 0)
  have hbase : 2^(2^k : ℕ)+1 ∣ (2:ℕ)^a+1 := by
    rw [he, pow_mul]
    simpa only [one_pow] using hd.nat_add_dvd_pow_add_pow ((2:ℕ)^(2^k : ℕ)) 1
  refine ⟨k,test _ hbase,d,⟨hd,?_⟩,he.symm⟩
  rw [← he]
  exact test _ ⟨_,(Nat.div_mul_cancel hbase).symm⟩

end OMA.R_Erdos1052_erdos_1052_R2_H2_R4
