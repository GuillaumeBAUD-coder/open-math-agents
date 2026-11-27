import OMAReductions.R_Erdos470_erdos_470_parts_ii_R2

/-! # A criterion for a primitive weird number with two odd prime factors -/
-- Credit: @steveDOTdigital
namespace OMA.WeirdCriterion
open Finset Nat

private def S (n : ℕ) := ∑ d ∈ n.divisors, d

private lemma single (p : ℕ) (hp : p.Prime) : S p = p+1 := by
  simp [S,hp.divisors,add_comm,hp.ne_one.symm]

private lemma twos (k : ℕ) : S (2^k) + 1 = 2^(k+1) := by
  unfold S
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => decide
  | succ k ih =>
    rw [sum_range_succ, pow_succ 2 (k+1)]
    omega

private lemma two_one (k r : ℕ) (hr : r.Prime) (ne : 2 ≠ r) :
    S (2^k*r) = (2^(k+1)-1)*(r+1) := by
  have cop := ((Nat.coprime_primes Nat.prime_two hr).mpr ne).pow_left k
  have add := twos k
  rw [show S (2^k*r) = S (2^k)*S r from cop.sum_divisors_mul,single r hr]
  congr 1
  omega

private lemma two_two (k p q : ℕ) (hp : p.Prime) (hq : q.Prime) (pn : 2 ≠ p)
    (qn : 2 ≠ q) (ne : p ≠ q) : S (2^k*p*q) = (2^(k+1)-1)*(p+1)*(q+1) := by
  have cp := ((Nat.coprime_primes Nat.prime_two hq).mpr qn).pow_left k
  have cq := (Nat.coprime_primes hp hq).mpr ne
  rw [show S (2^k*p*q) = S (2^k*p)*S q from (cp.mul_left cq).sum_divisors_mul,
    two_one k p hp pn,single q hq]

private lemma exclusion (k p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (bp : 2^(k+1) < p) (bq : 2^(k+1) < q) (pq : p ≠ q)
    (pos : 2^(k+1)*p*q < (2^(k+1)-1)*(p+1)*(q+1))
    (cap : (2^(k+1)-1)*(p+1)*(q+1) < 2^(k+1)*p*q+q)
    (res : 2^(k+1) ≤ ((2^(k+1)-1)*(p+1)*(q+1)-2^(k+1)*p*q)%p) :
    (2^k*p*q).Weird := by
  classical
  let n := 2^k*p*q
  let N := 2^(k+1)
  let D := (N-1)*(p+1)*(q+1)-N*p*q
  have bn : 2 ≤ N := by dsimp [N]; rw [pow_succ]; have := Nat.two_pow_pos k; omega
  have sn : S n = (N-1)*(p+1)*(q+1) := two_two _ _ _ hp hq (by change N<p at bp; omega) (by change N<q at bq; omega) pq
  have twice : 2*n = N*p*q := by dsimp [n,N]; rw [pow_succ]; ring
  constructor
  · rw [Nat.abundant_iff_sum_divisors]
    change 2*n < S n
    rwa [sn,twice]
  · rintro ⟨_,s,sub,ss⟩
    let t := n.properDivisors \ s
    have split : (∑ d ∈ t, d) + ∑ d ∈ s, d = ∑ d ∈ n.properDivisors, d := sum_sdiff sub
    have total : S n = (∑ d ∈ n.properDivisors, d) + n := Nat.sum_divisors_eq_sum_properDivisors_add_self
    change ∑ d ∈ s, d = n at ss
    have weight : ∑ d ∈ t, d = D := by dsimp [D]; omega
    have lim : D < q := by
      have sublt (a b c : ℕ) (h : a < b+c) (hc : 0<c) : a-b<c := by omega
      exact sublt _ _ _ cap hq.pos
    have each (d : ℕ) (hd : d ∈ t) : d ∣ n ∧ d < q := by
      have ld : d ≤ ∑ x ∈ t, x := single_le_sum (fun x _ => Nat.zero_le x) hd
      exact ⟨(Nat.mem_properDivisors.mp (mem_sdiff.mp hd).1).1,by omega⟩
    let sr := t.filter (fun d => ¬p ∣ d)
    let lr := t.filter (fun d => p ∣ d)
    have srsub : sr ⊆ (2^k).divisors := by
      intro d hd
      obtain ⟨dt,np⟩ := mem_filter.mp hd
      obtain ⟨dn,lt⟩ := each _ dt
      have dp : 0 < d := Nat.pos_of_dvd_of_pos dn (by dsimp [n]; positivity)
      have cq := (hq.coprime_iff_not_dvd.mpr (fun h => (not_le_of_gt lt) (Nat.le_of_dvd dp h))).symm
      have cp := (hp.coprime_iff_not_dvd.mpr np).symm
      exact Nat.mem_divisors.mpr ⟨cp.dvd_of_dvd_mul_right (cq.dvd_of_dvd_mul_right dn),by positivity⟩
    have sl : (∑ d ∈ sr, d) ≤ S (2^k) := sum_le_sum_of_subset_of_nonneg srsub (by intros; omega)
    have ll : p ∣ ∑ d ∈ lr, d := Finset.dvd_sum (fun d h => (mem_filter.mp h).2)
    have weights : (∑ d ∈ lr,d)+(∑ d ∈ sr,d) = D := (sum_filter_add_sum_filter_not t (fun d => p ∣ d) id).trans weight
    have small : ∑ d ∈ sr,d < p := by have := twos k; omega
    have red : D%p = ∑ d ∈ sr,d := by
      rw [←weights,Nat.add_mod,Nat.mod_eq_zero_of_dvd ll,zero_add,Nat.mod_mod,Nat.mod_eq_of_lt small]
    change N ≤ D%p at res
    have key : S (2^k)+1=N := twos k
    omega

private lemma reduced_one (k r : ℕ) (hr : r.Prime) (bound : 2^(k+1)<r) : ¬(2^k*r).Abundant := by
  have pos : 1 ≤ 2^(k+1) := Nat.two_pow_pos _
  have bn : 2 ≤ 2^(k+1) := by rw [pow_succ]; have := Nat.two_pow_pos k; omega
  intro h
  have sum := Nat.abundant_iff_sum_divisors.mp h
  change 2*(2^k*r) < S (2^k*r) at sum
  rw [two_one _ _ hr (by omega)] at sum
  have n := Nat.sub_add_cancel pos
  rw [show 2*(2^k*r)=2^(k+1)*r by rw [pow_succ]; ring] at sum
  nlinarith only [sum,bound,n,congrArg (· * r) n]

private lemma reduced_two (j p q : ℕ) (hp : p.Prime) (hq : q.Prime) (pq : p ≠ q)
    (bp : 2^(j+2)<p) (bq : 2^(j+2)<q) : ¬(2^j*p*q).Abundant := by
  intro h
  let T := 2^(j+1)
  have tpos : 1≤T := Nat.two_pow_pos _
  have bp' : 2*T<p := by simpa [T,pow_succ,Nat.mul_comm] using bp
  have bq' : 2*T<q := by simpa [T,pow_succ,Nat.mul_comm] using bq
  have sum := Nat.abundant_iff_sum_divisors.mp h
  change 2*(2^j*p*q) < S (2^j*p*q) at sum
  rw [two_two _ _ _ hp hq (by omega) (by omega) pq] at sum
  rw [show 2*(2^j*p*q)=T*p*q by dsimp [T]; rw [pow_succ]; ring] at sum
  change T*p*q < (T-1)*(p+1)*(q+1) at sum
  obtain ⟨a,pa⟩ := Nat.exists_eq_add_of_le (show 2*T ≤ p by omega)
  obtain ⟨b,qb⟩ := Nat.exists_eq_add_of_le (show 2*T ≤ q by omega)
  have e := Nat.sub_add_cancel tpos
  generalize T-1 = u at sum e
  rw [←e,pa,qb,←e] at sum
  nlinarith only [sum,Nat.zero_le a,Nat.zero_le b,Nat.zero_le (a*b),Nat.zero_le u,
    Nat.zero_le (a*u),Nat.zero_le (b*u)]

private lemma minimality (k p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (bp : 2^(k+1)<p) (bq : 2^(k+1)<q) (pq : p≠q) (d : ℕ)
    (hd : d ∈ (2^k*p*q).properDivisors) : ¬d.Weird := by
  have ppos := hp.pos
  have qpos := hq.pos
  obtain ⟨dv,lt⟩ := Nat.mem_properDivisors.mp hd
  obtain ⟨t,eq⟩ := dv
  have tn : t≠1 := fun h => by simp [h] at eq; omega
  obtain ⟨r,hr,u,tu⟩ := Nat.exists_prime_and_dvd tn
  have split : 2^k*p*q = (d*u)*r := by rw [eq,tu]; ring
  have rn : r ∣ 2^k*p*q := ⟨d*u,by rw [split]; ring⟩
  intro weird
  have lift {M : ℕ} (e : 2^k*p*q=M*r) (nz : M≠0) : M.Abundant := by
    have same : M=d*u := Nat.eq_of_mul_eq_mul_right hr.pos (e.symm.trans split)
    exact weird.1.of_dvd ⟨u,same⟩ nz
  rcases hr.dvd_mul.mp rn with l|rq
  · rcases hr.dvd_mul.mp l with two|rp
    · have r2 : r=2 := ((Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow two)).resolve_left hr.ne_one
      subst r
      cases k with
      | zero => simp at two
      | succ j =>
        exact reduced_two j p q hp hq pq bp bq (lift (M := 2^j*p*q) (by rw [pow_succ]; ring) (by positivity))
    · have e : r=p := ((Nat.dvd_prime hp).mp rp).resolve_left hr.ne_one
      subst r
      exact reduced_one k q hq bq (lift (M := 2^k*q) (by ring) (by positivity))
  · have e : r=q := ((Nat.dvd_prime hq).mp rq).resolve_left hr.ne_one
    subst r
    exact reduced_one k p hp bp (lift (M := 2^k*p) rfl (by positivity))

end OMA.WeirdCriterion

theorem OMA.WeirdCriterion.result (k p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (bp : 2^(k+1)<p) (bq : 2^(k+1)<q) (pq : p≠q)
    (pos : 2^(k+1)*p*q < (2^(k+1)-1)*(p+1)*(q+1))
    (cap : (2^(k+1)-1)*(p+1)*(q+1) < 2^(k+1)*p*q+q)
    (res : 2^(k+1) ≤ ((2^(k+1)-1)*(p+1)*(q+1)-2^(k+1)*p*q)%p) :
    Erdos470.PrimitiveWeird (2^k*p*q) :=
  ⟨exclusion _ _ _ hp hq bp bq pq pos cap res,minimality _ _ _ hp hq bp bq pq⟩

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R2.H1 := OMA.WeirdCriterion.result
