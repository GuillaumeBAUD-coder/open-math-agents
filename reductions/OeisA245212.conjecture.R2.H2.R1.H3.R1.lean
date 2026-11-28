import OMAReductions.R_OeisA245212_conjecture_R2_H2_R1

/-! The rank-one case of the finite exhaustion is settled outright: for `2^a*p^k` with `p` an odd prime the equation
forces `p ∣ a+1`, and then, after clearing denominators, a product of three positive integers would vanish.
What remains is split by the dyadic order into odd arguments and even arguments, both of rank at least two. -/
namespace OMA.R_OeisA245212_conjecture_R2_H2_R1_H3_R1
open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

theorem W_mul {x y : ℕ} (h : x.Coprime y) :
    ∑ d ∈ (x*y).divisors, d * σ 0 d = (∑ d ∈ x.divisors, d * σ 0 d) * (∑ d ∈ y.divisors, d * σ 0 d) := by
  have hm : ((ArithmeticFunction.id.pmul (σ 0))*ArithmeticFunction.zeta).IsMultiplicative :=
    (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta
  have ev : ∀ n : ℕ, ((ArithmeticFunction.id.pmul (σ 0))*ArithmeticFunction.zeta) n
      = ∑ d ∈ n.divisors, d * σ 0 d := by
    intro n
    have h := coe_mul_zeta_apply (f := ArithmeticFunction.id.pmul (σ 0)) (x := n)
    simpa only [ArithmeticFunction.natCoe_nat, ArithmeticFunction.pmul_apply,
      ArithmeticFunction.id_apply] using h
  rw [← ev, ← ev, ← ev]
  exact hm.map_mul_of_coprime h

theorem a_eq (n : ℕ) (hn : n ≠ 0) :
    OeisA245212.a n = 2*((n:ℤ)*(σ 0 n:ℤ)) - ((∑ d ∈ n.divisors, d * σ 0 d : ℕ):ℤ) := by
  have h : ∑ d ∈ n.divisors, (d:ℤ)*(d.divisors.card:ℤ)
      = ∑ d ∈ n.properDivisors, (d:ℤ)*(d.divisors.card:ℤ) + (n:ℤ)*(n.divisors.card:ℤ) := by
    have h1 := Finset.sum_insert (s := n.properDivisors) (a := n)
      (f := fun d => (d:ℤ)*(d.divisors.card:ℤ)) (by simp)
    rw [Nat.insert_self_properDivisors hn] at h1
    rw [h1, add_comm]
  unfold OeisA245212.a
  simp only [sigma_zero_apply, Nat.cast_sum, Nat.cast_mul]
  rw [h]; ring

theorem closedG (p : ℤ) (k : ℕ) :
    (p-1)^2*∑ i ∈ range (k+1), p^i*((i:ℤ)+1) = ((k:ℤ)+1)*p^(k+2)-((k:ℤ)+2)*p^(k+1)+1 := by
  induction k with
  | zero => rw [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring
  | succ k ih => rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring

theorem closedS (p : ℤ) (k : ℕ) : (p-1)*∑ i ∈ range (k+1), p^i = p^(k+1)-1 := by
  induction k with
  | zero => rw [Finset.sum_range_succ, Finset.sum_range_zero]; ring
  | succ k ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

theorem w_pp (p k : ℕ) (hp : p.Prime) :
    ((∑ d ∈ (p^k).divisors, d * σ 0 d : ℕ):ℤ) = ∑ i ∈ range (k+1), (p:ℤ)^i*((i:ℤ)+1) := by
  rw [Nat.sum_divisors_prime_pow hp, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sigma_zero_apply_prime_pow hp, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]

theorem s_pp (p k : ℕ) (hp : p.Prime) : (σ 1 (p^k):ℤ) = ∑ i ∈ range (k+1), (p:ℤ)^i := by
  rw [sigma_one_apply_prime_pow hp, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => Nat.cast_pow p i

theorem core (P q A K y C G S : ℤ) (hA : A = P*C-1)
    (hG : (P-1)^2*G = (K+1)*(P*y*P^2)-(K+2)*(P*y*P)+1) (hS : (P-1)*S = P*y*P-1)
    (eqn : q*(P*y)*((A+1)*(K+1))-(A*q+1)*G = (q-1)*S) :
    P*(q*(C-1)+1)*(P*y*(K*(P-1)-1)+1) = 0 := by
  subst hA
  linear_combination (-(P-1)^2)*eqn - ((P*C-1)*q+1)*hG - (q-1)*(P-1)*hS

theorem divis (P q A K y G S : ℤ)
    (hG : (P-1)^2*G = (K+1)*(P*y*P^2)-(K+2)*(P*y*P)+1) (hS : (P-1)*S = P*y*P-1)
    (eqn : q*(P*y)*((A+1)*(K+1))-(A*q+1)*G = (q-1)*S) : P ∣ q*(A+1) :=
  ⟨-(q*(-K*(P*y)*P+P*y*(A*K+2*K+1)-(A+1)*(K+1)*y-1)+(K*(P*y)*P-(K+1)*(P*y)+1)), by
    linear_combination (-(P-1)^2)*eqn - (A*q+1)*hG - (q-1)*(P-1)*hS⟩

/-- No number `2^a*p^(k+1)` with `p` an odd prime solves the equation. -/
theorem prime_power (p k a : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    OeisA245212.a (2^a*p^(k+1)) ≠ (σ 1 (2^a*p^(k+1)):ℤ) := by
  intro eqn
  have cop : Nat.Coprime (2^a) (p^(k+1)) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm h2))
  have hn : 2^a*p^(k+1) ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ hp.ne_zero)
  have e0 : σ 0 (2^a*p^(k+1)) = (a+1)*(k+1+1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime cop, sigma_zero_apply_prime_pow Nat.prime_two,
      sigma_zero_apply_prime_pow hp]
  have e1 : σ 1 (2^a*p^(k+1)) = σ 1 (2^a) * σ 1 (p^(k+1)) :=
    isMultiplicative_sigma.map_mul_of_coprime cop
  have g2 : ((∑ d ∈ (2^a).divisors, d * σ 0 d : ℕ):ℤ) = (a:ℤ)*2^(a+1)+1 := by
    have h := closedG 2 a
    rw [w_pp 2 a Nat.prime_two]; push_cast; linear_combination h
  have s2 : (σ 1 (2^a):ℤ) = 2^(a+1)-1 := by
    have h := closedS 2 a
    rw [s_pp 2 a Nat.prime_two]; push_cast; linear_combination h
  have key := a_eq _ hn
  rw [eqn, e0, e1, W_mul cop] at key
  simp only [Nat.cast_mul] at key
  rw [g2, s2] at key
  have hG := closedG (p:ℤ) (k+1)
  have hS := closedS (p:ℤ) (k+1)
  rw [← w_pp p (k+1) hp] at hG
  rw [← s_pp p (k+1) hp] at hS
  generalize ((∑ d ∈ (p^(k+1)).divisors, d * σ 0 d : ℕ):ℤ) = G at key hG
  generalize (σ 1 (p^(k+1)):ℤ) = S at key hS
  push_cast at key hG
  have hG' : ((p:ℤ)-1)^2*G
      = (((k:ℤ)+1)+1)*((p:ℤ)*(p:ℤ)^k*(p:ℤ)^2)-(((k:ℤ)+1)+2)*((p:ℤ)*(p:ℤ)^k*(p:ℤ))+1 := by
    linear_combination hG
  have hS' : ((p:ℤ)-1)*S = (p:ℤ)*(p:ℤ)^k*(p:ℤ)-1 := by linear_combination hS
  have eqn' : (2:ℤ)^(a+1)*((p:ℤ)*(p:ℤ)^k)*(((a:ℤ)+1)*(((k:ℤ)+1)+1))-((a:ℤ)*2^(a+1)+1)*G
      = ((2:ℤ)^(a+1)-1)*S := by linear_combination (-1:ℤ)*key
  have dv := divis (p:ℤ) (2^(a+1)) (a:ℤ) ((k:ℤ)+1) ((p:ℤ)^k) G S hG' hS' eqn'
  have dvn : p ∣ 2^(a+1)*(a+1) := by exact_mod_cast dv
  have cop2 : Nat.Coprime p (2^(a+1)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 h2)
  have pd : p ∣ a+1 := cop2.dvd_of_dvd_mul_left dvn
  obtain ⟨c, hc⟩ := pd
  have cpos : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, Nat.mul_zero] at hc; omega
    · exact h
  have hA : (a:ℤ) = (p:ℤ)*(c:ℤ)-1 := by
    have h : ((a+1:ℕ):ℤ) = ((p*c:ℕ):ℤ) := by rw [hc]
    push_cast at h; linear_combination h
  have fin := core (p:ℤ) (2^(a+1)) (a:ℤ) ((k:ℤ)+1) ((p:ℤ)^k) (c:ℤ) G S hA hG' hS' eqn'
  have p3 : (3:ℤ) ≤ (p:ℤ) := by
    have h := hp.two_le
    have h' : 3 ≤ p := by omega
    exact_mod_cast h'
  have c1 : (1:ℤ) ≤ (c:ℤ) := by exact_mod_cast cpos
  have k0 : (0:ℤ) ≤ (k:ℤ) := Int.natCast_nonneg k
  have q0 : (0:ℤ) < (2:ℤ)^(a+1) := by positivity
  have f1 : (0:ℤ) < (p:ℤ) := by linarith
  have y0 : (0:ℤ) < (p:ℤ)^k := pow_pos f1 k
  have f2 : (0:ℤ) < (2:ℤ)^(a+1)*((c:ℤ)-1)+1 := by
    have h := mul_nonneg q0.le (sub_nonneg.2 c1)
    linarith
  have f3 : (0:ℤ) < (p:ℤ)*(p:ℤ)^k*(((k:ℤ)+1)*((p:ℤ)-1)-1)+1 := by
    have h : (0:ℤ) ≤ ((k:ℤ)+1)*((p:ℤ)-1)-1 := by
      have h' := mul_nonneg k0 (by linarith : (0:ℤ) ≤ (p:ℤ)-1)
      linarith
    have h' := mul_nonneg (mul_pos f1 y0).le h
    linarith
  exact absurd fin (mul_pos (mul_pos f1 f2) f3).ne'

/-- Odd arguments with at least two distinct prime factors: the finite arithmetic at dyadic order zero. -/
def H1 : Prop :=
  let cost := Nat.rec (motive:=fun _=>ℕ→ℕ) (fun _=>1)
    (fun _ f u=>2*(u+1)*f (2*(u+1)^2))
  let fixed := Nat.rec (motive:=fun _=>ℕ→ℕ) (fun _=>1) (fun i f x=>
    let u:=f x; let b:=2*u*x*2^i+2
    2*u+(x^(i+1)*(b^2)^(i+1))*cost (i+1) (x*(b*(x*b)+1)^(i+1)))
  let envelope (j x : ℕ) := ∑i∈range (j+1),fixed i x
  let poly (j x : ℕ) := let u:=2*envelope j x; 2*u+2*u*(2*envelope j (x+2*u))
  let cut (j D : ℕ) := let a:=poly j 1+1; let d:=poly j 2
                         a*(16*(d*D+1)^2+2*(a*D)+6)^d
  let length (r : ℕ) :=
    let j:=(3*r+4)^(2*r+1)
    let e:=(r+2)*j+r
    let h:=12*e+4
    let s:=128+2*r*2^r+(2^(16*(e+2)^2+8)+(16*128^e)^2)+2+16*(h*j+2)^2
    s+cut (r+1) (2*e+1+h*j*r)+(s+2^270+16*140^2)+cut (r+1) (1+h*j*r)
  let w : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0))*ArithmeticFunction.zeta
  let budget (A r : ℕ) := Nat.rec 1 (fun i z=>max (2*z) ((2+2*A*2^i*z)^(i+1))) r
  let threshold (A S r : ℕ) := budget A r*(2*A*r*2^r+2*S)
  let step (h r : ℕ) :=
    let A:=w h; let H:=2*(h*σ 0 h); let e:=threshold A (σ 1 h) r
    h*(max (e+1) (r*H*(σ 1 h+1)/(H-A))+1)^e
  let two (B : ℕ) :=
    let C:=2*B^3+1; let P:=2*C*(C+4)
    let scalar:=16*(C+C+1)
    let Z:=P^4+scalar+C+2*C*P+2
    let expo:=4*C*Z+2*(C+C*Z^2)
    let scale:=max scalar ((2*(4*C+C))^2)
    let multiplier:=2*P*(C+C)*(C*P+1)
    let loose:=2*C+4*C*P+max 784 (64*(scale*multiplier^6))
    4*(B*max 1 (max (Z^expo) (P^loose)))^7
  let next (B r : ℕ) :=
    let C:=2*B^3+1
    let e:=threshold C C r
    B*(max (e+1) (r*C*(C+1))+1)^e
  let small := ∑k∈range 256,
    (two (2^k) + 4*((range (step (2^k) 3+1)).sup (fun h=>step h 2))^7 +
      two (next (next (2^k) 4) 3))
  ∀ r : ℕ, 2 ≤ r → ∀ t ≤ (length r)^r+small, ∀ m ≤ (2*t^2)^(t-1), Odd m →
    m.primeFactors.card=r → m.divisors.card=t → OeisA245212.a m≠(σ 1 m:ℤ)

/-- Even arguments whose odd part has at least two distinct prime factors, all indices bounded as before. -/
def H2 : Prop :=
  let cost := Nat.rec (motive:=fun _=>ℕ→ℕ) (fun _=>1)
    (fun _ f u=>2*(u+1)*f (2*(u+1)^2))
  let fixed := Nat.rec (motive:=fun _=>ℕ→ℕ) (fun _=>1) (fun i f x=>
    let u:=f x; let b:=2*u*x*2^i+2
    2*u+(x^(i+1)*(b^2)^(i+1))*cost (i+1) (x*(b*(x*b)+1)^(i+1)))
  let envelope (j x : ℕ) := ∑i∈range (j+1),fixed i x
  let poly (j x : ℕ) := let u:=2*envelope j x; 2*u+2*u*(2*envelope j (x+2*u))
  let cut (j D : ℕ) := let a:=poly j 1+1; let d:=poly j 2
                         a*(16*(d*D+1)^2+2*(a*D)+6)^d
  let length (r : ℕ) :=
    let j:=(3*r+4)^(2*r+1)
    let e:=(r+2)*j+r
    let h:=12*e+4
    let s:=128+2*r*2^r+(2^(16*(e+2)^2+8)+(16*128^e)^2)+2+16*(h*j+2)^2
    s+cut (r+1) (2*e+1+h*j*r)+(s+2^270+16*140^2)+cut (r+1) (1+h*j*r)
  let w : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0))*ArithmeticFunction.zeta
  let budget (A r : ℕ) := Nat.rec 1 (fun i z=>max (2*z) ((2+2*A*2^i*z)^(i+1))) r
  let threshold (A S r : ℕ) := budget A r*(2*A*r*2^r+2*S)
  let step (h r : ℕ) :=
    let A:=w h; let H:=2*(h*σ 0 h); let e:=threshold A (σ 1 h) r
    h*(max (e+1) (r*H*(σ 1 h+1)/(H-A))+1)^e
  let two (B : ℕ) :=
    let C:=2*B^3+1; let P:=2*C*(C+4)
    let scalar:=16*(C+C+1)
    let Z:=P^4+scalar+C+2*C*P+2
    let expo:=4*C*Z+2*(C+C*Z^2)
    let scale:=max scalar ((2*(4*C+C))^2)
    let multiplier:=2*P*(C+C)*(C*P+1)
    let loose:=2*C+4*C*P+max 784 (64*(scale*multiplier^6))
    4*(B*max 1 (max (Z^expo) (P^loose)))^7
  let next (B r : ℕ) :=
    let C:=2*B^3+1
    let e:=threshold C C r
    B*(max (e+1) (r*C*(C+1))+1)^e
  let small := ∑k∈range 256,
    (two (2^k) + 4*((range (step (2^k) 3+1)).sup (fun h=>step h 2))^7 +
      two (next (next (2^k) 4) 3))
  ∀ r : ℕ, 2 ≤ r → ∀ t ≤ (length r)^r+small, ∀ a < t*(2*Nat.log 2 (8*t^3)+2), 1 ≤ a →
    ∀ m ≤ ((2^(a+1)-1)*(a+2)*t^2)^(t-1), Odd m → m.primeFactors.card=r →
    m.divisors.card=t → OeisA245212.a (2^a*m)≠(σ 1 (2^a*m):ℤ)

theorem main : H1 → H2 → OMA.R_OeisA245212_conjecture_R2_H2_R1.H3 := by
  intro oddcase evencase r t ht a ha m hm odd large rank count
  by_cases hr : 2 ≤ r
  · rcases Nat.eq_zero_or_pos a with h0 | h1
    · subst h0
      have hm' : m ≤ (2*t^2)^(t-1) := hm.trans (le_of_eq (by norm_num))
      have fact := oddcase r hr t ht m hm' odd rank count
      rw [pow_zero, one_mul]
      exact fact
    · exact evencase r hr t ht a ha h1 m hm odd rank count
  · have r1 : m.primeFactors.card = 1 := by
      have h : m.primeFactors.card ≠ 0 := by
        rw [Ne, Finset.card_eq_zero, Nat.primeFactors_eq_empty]; omega
      omega
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).1 (isPrimePow_iff_card_primeFactors_eq_one.2 r1)
    obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := ⟨k-1, by omega⟩
    refine prime_power p j a hp ?_
    rintro rfl
    exact (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, by omega⟩)) odd

end OMA.R_OeisA245212_conjecture_R2_H2_R1_H3_R1
