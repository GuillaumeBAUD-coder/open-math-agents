import OMAReductions.R_arxiv_2604_17847_R1_H2_R1

-- Credit: @wispiANt
namespace OMA.R_arxiv_2604_17847_R1_H2_R1_H3_R1

open OMA.S_arxiv_2604_17847
open OMA.R_arxiv_2604_17847_R1_H2_R1

-- The complete 3-primary condition is a single iterated cubic equation.
def H1 : Prop :=
  ∀ q : ℕ, q.Prime → 1000 < q → 96 < pisano q →
    let h := pisano q / 2
    (¬ (q ∣ (ordCompl[q] (Nat.fib h)).totient ∨
        q ∣ (ordCompl[q] (ordCompl[2*q+1] (2*Nat.fib (h+1) - Nat.fib h))).totient)) → q % 15 = 8 →
    let t := pisano q/4
    q ^ 2 ∣ (if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t) → (2*q+1).Prime →
    let c := 2*(q+1)/pisano q
    ¬ (rankOfApparition (2*q+1)).Coprime c →
    ¬ (3 ∣ c ∧ (rankOfApparition (2*q+1)).Coprime (c/3) ∧
      ∃ x : ZMod (2*q+1), x^3 + 3*x = 1) →
    ∃ x : ZMod (2*q+1), (fun y : ZMod (2*q+1) => y^3+3*y)^[c.factorization 3] x = 1

-- At the other shared primes only their rank valuations remain.
def H2 : Prop :=
  ∀ q : ℕ, q.Prime → 1000 < q → 96 < pisano q →
    let h := pisano q / 2
    (¬ (q ∣ (ordCompl[q] (Nat.fib h)).totient ∨
        q ∣ (ordCompl[q] (ordCompl[2*q+1] (2*Nat.fib (h+1) - Nat.fib h))).totient)) → q % 15 = 8 →
    let t := pisano q/4
    q ^ 2 ∣ (if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t) → (2*q+1).Prime →
    let c := 2*(q+1)/pisano q
    ¬ (rankOfApparition (2*q+1)).Coprime c →
    ¬ (3 ∣ c ∧ (rankOfApparition (2*q+1)).Coprime (c/3) ∧
      ∃ x : ZMod (2*q+1), x^3 + 3*x = 1) →
    ∀ l : ℕ, l.Prime → 7 ≤ l → l ∣ c → l ∣ rankOfApparition (2*q+1) →
      (rankOfApparition (2*q+1)).factorization l ≤ (pisano q).factorization l

lemma cubic_trace {K : Type*} [Field K] {u v : K} (prod : u*v = -1) (e : ℕ) :
    (fun x : K => x^3+3*x)^[e] (u+v) = u^(3^e)+v^(3^e) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ 3 e, pow_mul, pow_mul]
    have h : u^(3^e)*v^(3^e) = -1 := by
      rw [←mul_pow, prod, (show Odd (3^e) from (by decide : Odd 3).pow).neg_one_pow]
    linear_combination 3*(u^(3^e)+v^(3^e))*h

lemma map_cubic_trace {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K]
    (x : ZMod p) (e : ℕ) :
    algebraMap (ZMod p) K ((fun y : ZMod p => y^3+3*y)^[e] x) =
      (fun y : K => y^3+3*y)^[e] (algebraMap (ZMod p) K x) := by
  induction e with
  | zero => rfl
  | succ e ih => simp only [Function.iterate_succ_apply', map_add, map_pow, map_mul, map_ofNat, ih]

lemma trace_pair {K : Type*} [Field K] [IsAlgClosed K] (two : (2 : K) ≠ 0) (x : K) :
    ∃ u v : K, u+v=x ∧ u*v = -1 := by
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq (x^2+4) (by decide : 0 < 2)
  let u := (x+s)/2
  have twice : u*2=x+s := div_mul_cancel₀ _ two
  refine ⟨u,x-u,by ring,?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 two)
  linear_combination -(2*u+s-x)*twice - hs

lemma frobenius_pair {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    {u v : K} (prod : u*v = -1) (fixed : (u+v)^p=u+v) :
    u^p=u ∨ u^p=v := by
  have trace : u^p+v^p=u+v := by rwa [add_pow_char] at fixed
  have norm : u^p*v^p = -1 := by
    rw [←mul_pow, prod, neg_one_pow_char]
  apply (mul_eq_zero.mp (show (u^p-u)*(u^p-v)=0 by
    linear_combination u^p*trace - norm + prod)).imp sub_eq_zero.mp sub_eq_zero.mp

lemma fibonacci_pair {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    (hl : 5 < p) (zero : p ∣ Nat.fib (p+1)) {a b : K} (sum : a+b=1) (prod : a*b = -1) :
    a^2=a+1 ∧ b^2=b+1 ∧ a-b ≠ 0 ∧ a^p=b := by
  have A : a^2=a+1 := by linear_combination a*sum-prod
  have B : b^2=b+1 := by linear_combination b*sum-prod
  have diff : a-b ≠ 0 := by
    intro same
    have five : (5 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K (by decide : Nat.Prime 5) (show p ≠ 5 by omega)
    exact five (by linear_combination (2*a-1)*sum + (2*a-1)*same - 4*A)
  refine ⟨A,B,diff,?_⟩
  rcases frobenius_pair prod (by rw [sum,one_pow]) with fix | swap
  · have f : a^p+b^p=1 := by rw [←add_pow_char,sum,one_pow]
    have fb : b^p=b := by linear_combination f - fix - sum
    have h := fib_root_difference A B (p+1)
    rw [(CharP.cast_eq_zero_iff K p _).mpr zero, zero_mul, pow_succ, pow_succ, fix, fb] at h
    exact (diff (by linear_combination -h - A + B)).elim
  · exact swap

lemma cubic_tower_iff {p e : ℕ} (hp : p.Prime) (hl : 5 < p)
    (zero : p ∣ Nat.fib (p+1)) (divides : 3^e ∣ p+1) :
    (∃ x : ZMod p, (fun y : ZMod p => y^3+3*y)^[e] x = 1) ↔
      p ∣ Nat.fib ((p+1)/3^e) := by
  let : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  let k := 3^e
  let n := (p+1)/k
  have whole : k*n = p+1 := Nat.mul_div_cancel' divides
  have odd : Odd k := (by decide : Odd 3).pow
  have two : (2 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two (show p ≠ 2 by omega)
  constructor
  · rintro ⟨x,hx⟩
    let X := algebraMap (ZMod p) K x
    obtain ⟨u,v,tr,prod⟩ := trace_pair two X
    have sum : u^k+v^k=1 := by
      rw [← cubic_trace prod, tr, ←map_cubic_trace, hx, map_one]
    have norm : u^k*v^k = -1 := by rw [←mul_pow,prod,odd.neg_one_pow]
    obtain ⟨A,B,diff,swap⟩ := fibonacci_pair hl zero sum norm
    have fixed : (u+v)^p=u+v := by rw [tr]; simp [X, ←map_pow, ZMod.pow_card]
    have uv : u^p=v := by
      rcases frobenius_pair prod fixed with fix | ex
      · rw [←pow_mul, Nat.mul_comm k p, pow_mul, fix] at swap
        exact (diff (sub_eq_zero.mpr swap)).elim
      · exact ex
    rw [add_pow_char,uv] at fixed
    have vu : v^p=u := by linear_combination fixed
    have eq : u^(p+1)=v^(p+1) := by rw [pow_succ,pow_succ,uv,vu,mul_comm]
    have h := fib_root_difference A B n
    rw [←pow_mul, ←pow_mul, whole, eq, sub_self] at h
    exact (CharP.cast_eq_zero_iff K p _).mp ((mul_eq_zero.mp h).resolve_right diff)
  · intro short
    obtain ⟨a,b,sum,prod⟩ := trace_pair two (1 : K)
    obtain ⟨A,B,_,swap⟩ := fibonacci_pair hl zero sum prod
    have az : a ≠ 0 := by rintro rfl; simp at prod
    obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq a (show 0 < k by positivity)
    have uz : u ≠ 0 := by rintro rfl; simp [show k ≠ 0 by positivity] at hu; exact az hu.symm
    let v := -(u⁻¹)
    have uv : u*v = -1 := by dsimp only [v]; rw [mul_neg, mul_inv_cancel₀ uz]
    have hv : v^k=b := by
      apply mul_left_cancel₀ az
      rw [←hu, ←mul_pow, uv, odd.neg_one_pow, hu, prod]
    have h := fib_root_difference A B n
    rw [(CharP.cast_eq_zero_iff K p _).mpr short,zero_mul] at h
    have same : u^(p+1)=v^(p+1) := by
      rw [←whole,pow_mul,pow_mul,hu,hv]
      exact sub_eq_zero.mp h.symm
    have sq : u^(p+1)*u^(p+1)=1 := by
      calc _ = u^(p+1)*v^(p+1) := by rw [←same]
           _ = 1 := by rw [←mul_pow,uv,pow_succ,neg_one_pow_char]; ring
    have nontriv : u^(p+1) ≠ 1 := by
      intro one
      have bad : a^(p+1)=1 := by rw [←hu,←pow_mul,Nat.mul_comm k _,pow_mul,one,one_pow]
      rw [pow_succ,swap,mul_comm,prod] at bad
      exact two (by linear_combination -bad)
    have minus : u^(p+1) = -1 := by
      rcases mul_self_eq_one_iff.mp sq with pos | neg
      · exact (nontriv pos).elim
      · exact neg
    have up : u^p=v := by
      apply mul_right_cancel₀ uz
      rw [←pow_succ,minus,mul_comm,uv]
    have vz : v ≠ 0 := by rintro h; rw [h,mul_zero] at uv; simp at uv
    have vp : v^p=u := by
      apply mul_right_cancel₀ vz
      rw [←pow_succ,←same,minus,uv]
    have fixed : (u+v)^p=u+v := by rw [add_pow_char,up,vp,add_comm]
    obtain ⟨i,hi⟩ := (mem_bot_iff_intCast p K).mp ((Subfield.mem_bot_iff_pow_eq_self K p).mpr fixed)
    refine ⟨i, (algebraMap (ZMod p) K).injective ?_⟩
    rw [map_cubic_trace,map_intCast,hi,cubic_trace uv,hu,hv,sum,map_one]

-- Removing exactly the 3-part of C does not change v₃(P).
lemma alignment_local_iff {q : ℕ} (hq : q.Prime) (hl : 5 < q)
    (residue : q%15=8) (hp : (2*q+1).Prime) :
    let c := 2*(q+1)/pisano q
    2*q+1 ∣ Nat.fib (pisano q) ↔
      (∃ x : ZMod (2*q+1), (fun y : ZMod (2*q+1) => y^3+3*y)^[c.factorization 3] x = 1) ∧
      ∀ l : ℕ, l.Prime → 7 ≤ l → l ∣ c → l ∣ rankOfApparition (2*q+1) →
        (rankOfApparition (2*q+1)).factorization l ≤ (pisano q).factorization l := by
  intro c
  let P := pisano q
  let k := 3^c.factorization 3
  let m := (2*q+1+1)/k
  let : NeZero q := ⟨hq.ne_zero⟩
  have Ppos : 0 < P := (period_and_returns q).1
  have total : P*c = 2*q+1+1 := by
    have h := Nat.mul_div_cancel' (nonsplit_period_cofactor hq hl (by omega)).1
    dsimp [P,c]; omega
  have cn : c ≠ 0 := by intro z; rw [z,mul_zero] at total; omega
  have strip : k ∣ c := Nat.ordProj_dvd c 3
  have divides : k ∣ 2*q+1+1 := total ▸ dvd_mul_of_dvd_right strip _
  have index : m = P*(c/k) := by
    dsimp only [m]; rw [←total,Nat.mul_div_assoc _ strip]
  have mpos : 0 < m := Nat.div_pos (Nat.le_of_dvd (by omega) divides) (by positivity)
  have zero := zero_at_selected_neighbor hp (by omega)
  rw [if_neg (by omega)] at zero
  have test := cubic_tower_iff hp (by omega) zero divides
  have locals := companion_odd_tests_iff hq hl residue hp
  constructor
  · intro aligned
    exact ⟨test.mpr (aligned.trans (Nat.fib_dvd _ _ (show P ∣ m by rw [index]; exact dvd_mul_right ..))),
      fun l pr big lc _ => locals.mp aligned l pr (by omega) lc⟩
  · rintro ⟨root,large⟩
    apply locals.mpr
    intro l pr above lc
    by_cases lr : l ∣ rankOfApparition (2*q+1)
    · by_cases three : l=3
      · subst l
        have rr := OMA.R_arxiv_2604_17847_R1.rank_dvd_index mpos (test.mp root)
        have rn : rankOfApparition (2*q+1) ≠ 0 := by intro z; rw [z,zero_dvd_iff] at rr; omega
        have h := (Nat.factorization_le_iff_dvd rn mpos.ne').mpr rr 3
        have unit : ¬ 3 ∣ c/k := Nat.not_dvd_ordCompl Nat.prime_three cn
        have nz : c/k ≠ 0 := by intro z; exact unit (z ▸ dvd_zero _)
        rw [index,Nat.factorization_mul Ppos.ne' nz,Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd unit,add_zero] at h
        exact h
      · have notFive : l ≠ 5 := by
          intro eq
          subst l
          have d : 5 ∣ 2*q+1+1 := total ▸ dvd_mul_of_dvd_right lc _
          omega
        have big : 7 ≤ l := by
          by_contra! small
          have choices : l = 4 ∨ l = 6 := by omega
          rcases choices with rfl | rfl <;> norm_num at pr
        exact large l pr big lc lr
    · simp [Nat.factorization_eq_zero_of_not_dvd lr]

-- With a pure power of three there is no second local obstruction.
lemma alignment_three_power_iff {q e : ℕ} (hq : q.Prime) (hl : 5 < q)
    (residue : q%15=8) (hp : (2*q+1).Prime) (cofactor : 2*(q+1)/pisano q=3^e) :
    2*q+1 ∣ Nat.fib (pisano q) ↔
      ∃ x : ZMod (2*q+1), (fun y : ZMod (2*q+1) => y^3+3*y)^[e] x = 1 := by
  have h := alignment_local_iff hq hl residue hp
  dsimp only at h
  rw [cofactor,Nat.factorization_pow_self Nat.prime_three] at h
  constructor
  · exact fun z => (h.mp z).1
  · intro root
    refine h.mpr ⟨root, ?_⟩
    intro l prime big divides _
    have small := Nat.le_of_dvd (by decide : 0 < 3) (prime.dvd_of_dvd_pow divides)
    omega

lemma parent_iff : (H1 ∧ H2) ↔ OMA.R_arxiv_2604_17847_R1_H2_R1.H3 := by
  constructor
  · rintro ⟨tower,large⟩ q hq high long h noOther res t square hp c cop cubic
    have aligned := (alignment_local_iff hq (by omega) res hp).mpr
      ⟨tower q hq high long noOther res square hp cop cubic,
       large q hq high long noOther res square hp cop cubic⟩
    have half := (half_quarter_square_iff hq (by omega) res).mpr square
    exact (companion_quarter_iff hq (by omega) res half hp).mp aligned
  · intro parent
    constructor <;> intro q hq high long h noOther res t square hp c cop cubic
    all_goals
      have half := (half_quarter_square_iff hq (by omega) res).mpr square
      have aligned := (companion_quarter_iff hq (by omega) res half hp).mpr
        (parent q hq high long noOther res square hp cop cubic)
      have tests := (alignment_local_iff hq (by omega) res hp).mp aligned
    · exact tests.1
    · exact tests.2

theorem main : H1 → H2 → OMA.R_arxiv_2604_17847_R1_H2_R1.H3 :=
  fun tower large => parent_iff.mp ⟨tower,large⟩

end OMA.R_arxiv_2604_17847_R1_H2_R1_H3_R1
