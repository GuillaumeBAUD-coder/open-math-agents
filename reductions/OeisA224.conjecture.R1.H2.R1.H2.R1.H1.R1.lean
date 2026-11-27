import OMAReductions.R_OeisA224_conjecture_R1_H2_R1_H2_R1
import Mathlib
-- Credit: @marcusbuffett
/-!
For Ordowski's conjecture, exclude every squarefree product of three distinct
odd primes p < q < r, without an upper bound on any of them. Put
x=(p+1)/2, y=(q+1)/2, z=(r+1)/2. The number of square residue classes is
xyz. If the congruence holds, the integer quotient k satisfies

  (pqr)^2 = k xyz (xyz-1) + 1.

The limiting quotients as the largest factors grow give finite bounds on k,
x and y. At each surviving triple (k,x,y), the equation in z is quadratic.
A finite discriminant check leaves just (31,2,9), excluded modulo three.
-/

namespace OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1

set_option maxHeartbeats 1500000 in

private theorem rat_bounds (k x y z p q r : ℚ)
    (hx : 2 ≤ x) (hxy : x < y) (hyz : y < z)
    (hp : p = 2*x-1) (hq : q = 2*y-1) (hr : r = 2*z-1)
    (he : (p*q*r)^2 = k*(x*y*z)*(x*y*z-1)+1) :
    k < 64 ∧ (64-k)*x < 192 ∧ k*x^2 < 16*p^2 ∧
    (16*p^2-k*x^2)*y < 32*p^2 ∧ k*(x*y)^2 < 4*(p*q)^2 ∧
    (p*q^2)^2 < k*(x*y^2)^2 := by
  have xp : 0 < x := by linarith
  have yp : 0 < y := by linarith
  have zp : 0 < z := by linarith
  have pp : 0 < p := by linarith
  have qp : 0 < q := by linarith
  have rp : 0 < r := by linarith
  let A := x*y*z
  let B := p*q
  let C := x*y
  let N := p*q*r
  have hc : 2 ≤ C := by
    dsimp [C]
    calc 2 ≤ 2*1 := by norm_num
         _ ≤ x*y := by gcongr; linarith
  have ha : 2 ≤ A := by
    change 2 ≤ C*z
    calc 2 ≤ 2*1 := by norm_num
         _ ≤ C*z := by gcongr; linarith
  have han : A < N := by
    dsimp [A,N]
    gcongr <;> linarith
  have ae : N^2 = k*A*(A-1)+1 := he
  have kau : 1 < k*A := by
    by_contra! h
    have hu := mul_le_mul_of_nonneg_right h (show 0 ≤ A-1 by linarith)
    nlinarith only [ae,hu,han,ha,sq_nonneg (N-1)]
  have kl : N^2 < k*A^2 := by nlinarith only [ae,kau]
  have bla : 0 < B := mul_pos pp qp
  have cla : 0 < C := by linarith
  have gap : 0 < 4*z*(C-1)-C := by
    have := mul_le_mul_of_nonneg_right (show 1 ≤ z by linarith) (show 0 ≤ C-1 by linarith)
    linarith
  have up : k*C^2 < 4*B^2 := by
    apply lt_of_mul_lt_mul_right (a := A*(A-1))
    calc k*C^2*(A*(A-1)) = (N^2-1)*C^2 := by linear_combination -C^2*ae
         _ < 4*B^2*(A*(A-1)) := by
           change ((B*r)^2-1)*C^2 < 4*B^2*((C*z)*(C*z-1))
           rw [hr]
           nlinarith only [mul_pos (mul_pos (sq_pos_of_pos bla) cla) gap, sq_nonneg C]
    exact mul_nonneg (by linarith) (by linarith)
  have mid : k*x^2 < 16*p^2 := by
    apply lt_of_mul_lt_mul_right (a := y^2)
    calc k*x^2*y^2 = k*C^2 := by dsimp [C]; ring
         _ < 4*B^2 := up
         _ < 16*p^2*y^2 := by
           dsimp [B]
           nlinarith only [mul_pos (sq_pos_of_pos pp) (show 0 < 4*y^2-q^2 by rw [hq]; nlinarith)]
    positivity
  have top : k < 64 := by
    apply lt_of_mul_lt_mul_right (a := x^2)
    calc k*x^2 < 16*p^2 := mid
         _ < 64*x^2 := by rw [hp]; nlinarith
    positivity
  have mono1 : p*y ≤ q*x := by rw [hp,hq]; nlinarith
  have mono2 : q*z ≤ r*y := by rw [hq,hr]; nlinarith
  have mono3 : p*z ≤ r*x := by rw [hp,hr]; nlinarith
  have loy : (p*q^2)^2 < k*(x*y^2)^2 := by
    apply lt_of_mul_lt_mul_right (a := z^2)
    calc (p*q^2)^2*z^2 = (p*q*(q*z))^2 := by ring
         _ ≤ (p*q*(r*y))^2 := by gcongr
         _ = N^2*y^2 := by dsimp [N]; ring
         _ < (k*A^2)*y^2 := mul_lt_mul_of_pos_right kl (sq_pos_of_pos yp)
         _ = k*(x*y^2)^2*z^2 := by dsimp [A]; ring
    positivity
  have lox : p^6 < k*x^6 := by
    apply lt_of_mul_lt_mul_right (a := (y*z)^2)
    calc p^6*(y*z)^2 = (p*(p*y)*(p*z))^2 := by ring
         _ ≤ (p*(q*x)*(r*x))^2 := by gcongr
         _ = N^2*x^4 := by dsimp [N]; ring
         _ < (k*A^2)*x^4 := mul_lt_mul_of_pos_right kl (pow_pos xp 4)
         _ = k*x^6*(y*z)^2 := by dsimp [A]; ring
    positivity
  have bern6 : 64*x^6-192*x^5 ≤ p^6 := by
    subst p
    obtain ⟨u,hu,hu'⟩ : ∃ u : ℚ, 0 ≤ u ∧ x = 2+u := ⟨x-2, by linarith, by ring⟩
    rw [hu']
    ring_nf
    linarith [pow_nonneg hu 2,pow_nonneg hu 3,pow_nonneg hu 4]
  have bern4 : 16*y^4-32*y^3 ≤ q^4 := by
    subst q
    obtain ⟨u,hu,hu'⟩ : ∃ u : ℚ, 0 ≤ u ∧ y = 2+u := ⟨y-2, by linarith, by ring⟩
    rw [hu']
    ring_nf
    linarith [sq_nonneg u]
  refine ⟨top, ?_, mid, ?_, up, loy⟩
  · apply lt_of_mul_lt_mul_right (a := x^5) <;> first | positivity | nlinarith only [lox,bern6]
  · apply lt_of_mul_lt_mul_right (a := y^3) <;> first | positivity |
      nlinarith only [loy,mul_le_mul_of_nonneg_left bern4 (sq_nonneg p)]
-- Split the finite check by the residue of y so individual kernel
-- reductions stay small. The factorial filter discards impossible primes.
set_option maxHeartbeats 20000000 in
private theorem residue_certificate (t : Fin 128) :
    (List.range 64).all (fun k =>
      (List.range (192/(64-k)+1)).all (fun x => Id.run do
        let p := 2*x-1
        if x < 2 || 16*p^2 ≤ k*x^2 || (30 < p && p.gcd (Nat.factorial 30) != 1) then return true
        let bound := 32*p^2/(16*p^2-k*x^2)
        return (List.range (bound/128+1)).all (fun b => Id.run do
          let y := b*128+t.val
          let q := 2*y-1
          let B := p*q
          let C := x*y
          if y ≤ x || 4*B^2 ≤ k*C^2 || (p*q^2)^2 ≥ k*(x*y^2)^2 then return true
          if 30 < q && q.gcd (Nat.factorial 30) != 1 then return true
          let a := 4*B^2-k*C^2
          let b' := 4*B^2-k*C
          let c := B^2-1
          let d := b'^2-4*a*c
          return (b'^2 < 4*a*c || d.sqrt^2 != d || (k == 31 && x == 2 && y == 9)) ) )) = true := by
  fin_cases t <;> as_aux_lemma => decide +kernel

private theorem quadratic_check {k x y : ℕ} (hk : k < 64) (hx : 2 ≤ x)
    (hxy : x < y) (hxb : (64-k)*x < 192)
    (hp : Nat.Prime (2*x-1)) (hq : Nat.Prime (2*y-1))
    (hm : k*x^2 < 16*(2*x-1)^2)
    (hyb : (16*(2*x-1)^2-k*x^2)*y < 32*(2*x-1)^2)
    (hu : k*(x*y)^2 < 4*((2*x-1)*(2*y-1))^2)
    (hl : ((2*x-1)*(2*y-1)^2)^2 < k*(x*y^2)^2) :
    let B := (2*x-1)*(2*y-1)
    let C := x*y
    let a := 4*B^2-k*C^2
    let b := 4*B^2-k*C
    let c := B^2-1
    let d := b^2-4*a*c
    b^2 < 4*a*c ∨ d.sqrt^2 ≠ d ∨ (k=31 ∧ x=2 ∧ y=9) := by
  dsimp only
  let t : Fin 128 := ⟨y%128, Nat.mod_lt _ (by decide)⟩
  have row := List.all_eq_true.mp (residue_certificate t) k (List.mem_range.mpr hk)
  have xmem : x < 192/(64-k)+1 := by
    apply Nat.lt_succ_of_le
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa only [Nat.mul_comm x] using hxb.le)
  have slot := List.all_eq_true.mp row x (List.mem_range.mpr xmem)
  have hsieve (p : ℕ) (prime : p.Prime) : 30 < p → p.gcd (Nat.factorial 30) = 1 := by
    intro h
    exact prime.coprime_iff_not_dvd.mpr (fun hd => (Nat.not_le_of_gt h) ((prime.dvd_factorial).mp hd))
  have ppass : (decide (30 < 2*x-1) && ((2*x-1).gcd (Nat.factorial 30) != 1)) = false := by
    by_cases h : 30 < 2*x-1
    · simp [h,hsieve _ hp h]
    · simp [h]
  have qpass : (decide (30 < 2*y-1) && ((2*y-1).gcd (Nat.factorial 30) != 1)) = false := by
    by_cases h : 30 < 2*y-1
    · simp [h,hsieve _ hq h]
    · simp [h]
  have notx : ¬ x < 2 := by omega
  simp only [Id.run, notx, decide_false, Nat.not_le_of_gt hm, ppass,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte] at slot
  have yle : y ≤ 32*(2*x-1)^2/(16*(2*x-1)^2-k*x^2) := by
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    simpa only [Nat.mul_comm y] using hyb.le
  have idx := List.all_eq_true.mp slot (y/128) (List.mem_range.mpr
    (Nat.lt_succ_of_le (Nat.div_le_div_right yle)))
  have rebuild : y/128*128+t.val = y := by dsimp [t]; omega
  simp only [rebuild, Nat.not_le_of_gt hxy, Nat.not_le_of_gt hu, Nat.not_le_of_gt hl,
    decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, qpass] at idx
  change (_ || _ || _) = true at idx
  simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, Bool.and_eq_true, beq_iff_eq] at idx
  tauto

set_option maxHeartbeats 1200000 in
private theorem no_triple (k x y z p q r : ℕ) (hx : 2 ≤ x) (hxy : x < y) (hyz : y < z)
    (hp : p+1=2*x) (hq : q+1=2*y) (hr : r+1=2*z) (pp : p.Prime) (qp : q.Prime)
    (he : (p*q*r)^2 = k*(x*y*z)*(x*y*z-1)+1) : False := by
  have xp : 0 < x := by omega
  have yp : 0 < y := by omega
  have zp : 0 < z := by omega
  have ara : 1 ≤ x*y*z := Nat.succ_le_of_lt (by positivity)
  have heR : ((p:ℚ)*q*r)^2 = (k:ℚ)*(x*y*z)*(x*y*z-1)+1 := by
    exact_mod_cast (show ((p*q*r:ℕ):ℚ)^2 = ((k*(x*y*z)*(x*y*z-1)+1:ℕ):ℚ) by exact_mod_cast he)
  have hpQ : (p:ℚ)+1=2*x := by exact_mod_cast hp
  have hqQ : (q:ℚ)+1=2*y := by exact_mod_cast hq
  have hrQ : (r:ℚ)+1=2*z := by exact_mod_cast hr
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := rat_bounds k x y z p q r (by exact_mod_cast hx)
    (by exact_mod_cast hxy) (by exact_mod_cast hyz) (by linarith) (by linarith) (by linarith) heR
  have hk : k < 64 := by exact_mod_cast h0
  have hx' : (64-k)*x < 192 := by
    exact_mod_cast (show (((64-k:ℕ):ℚ)*x < 192) by push_cast [Nat.cast_sub hk.le]; exact h1)
  have hmid : k*x^2 < 16*p^2 := by exact_mod_cast h2
  have hy' : (16*p^2-k*x^2)*y < 32*p^2 := by
    exact_mod_cast (show (((16*p^2-k*x^2:ℕ):ℚ)*y < 32*(p:ℚ)^2) by push_cast [Nat.cast_sub hmid.le]; exact h3)
  have hup : k*(x*y)^2 < 4*(p*q)^2 := by exact_mod_cast h4
  have hlo : (p*q^2)^2 < k*(x*y^2)^2 := by exact_mod_cast h5
  have ep : 2*x-1 = p := by omega
  have eq : 2*y-1 = q := by omega
  have cert := quadratic_check hk hx hxy hx' (ep ▸ pp) (eq ▸ qp) (by rwa [ep])
    (by rwa [ep]) (by rwa [ep,eq]) (by rwa [ep,eq])
  dsimp only at cert
  rw [ep,eq] at cert
  let B := p*q
  let C := x*y
  let a := 4*B^2-k*C^2
  let b := 4*B^2-k*C
  let c := B^2-1
  have positiveX : 0 < x := by omega
  have positiveY : 0 < y := by omega
  have positiveZ : 0 < z := by omega
  have bc : 1 ≤ B^2 := by dsimp [B]; have := pp.pos; have := qp.pos; exact Nat.succ_le_of_lt (by positivity)
  have cc : 1 ≤ C := by dsimp [C]; exact Nat.succ_le_of_lt (by positivity)
  have ku : k*C ≤ 4*B^2 := le_trans (Nat.mul_le_mul_left _ (by nlinarith only [cc] : C ≤ C^2)) hup.le
  have quad : (a:ℤ)*z^2+c=b*z := by
    have heI : ((B:ℤ)*r)^2 = (k:ℤ)*(C*z)*(C*z-1)+1 := by
      have h := congrArg (fun t : ℕ => (t:ℤ)) he
      push_cast [Nat.cast_sub ara] at h
      exact h
    have hrI : (r:ℤ)+1=2*z := by exact_mod_cast hr
    rw [show (r:ℤ)=2*z-1 by linarith] at heI
    dsimp only [a,b,c]
    have hu : k*C^2 ≤ 4*B^2 := hup.le
    push_cast [Nat.cast_sub hu, Nat.cast_sub ku, Nat.cast_sub bc]
    linear_combination heI
  have disc : (b:ℤ)^2-4*a*c = (2*(a:ℤ)*z-b)^2 := by linear_combination -4*(a:ℤ)*quad
  let u := (2*(a:ℤ)*z-b).natAbs
  have discriminant : b^2 = 4*a*c + u^2 := by
    have u2 : (u:ℤ)^2 = (2*(a:ℤ)*z-b)^2 := Int.natAbs_sq _
    exact_mod_cast (show (b:ℤ)^2=4*a*c+(u:ℤ)^2 by linarith)
  change b^2 < 4*a*c ∨ (b^2-4*a*c).sqrt^2 ≠ b^2-4*a*c ∨ _ at cert
  have ds : b^2-4*a*c = u^2 := by omega
  rcases cert with bad | bad | ⟨rfl,rfl,rfl⟩
  · omega
  · exact bad (by simp [ds,Nat.sqrt_eq'])
  · norm_num at ep eq
    subst p q
    norm_num [a,b,c,B,C] at quad
    omega


open OeisA224

private theorem triple_fails {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hodd : p ≠ 2) (hpq : p < q) (hqr : q < r) :
    ¬ (p*q*r)^2 ≡ 1 [MOD a (p*q*r)*(a (p*q*r)-1)] := by
  intro htest
  let x := (p+1)/2
  let y := (q+1)/2
  let z := (r+1)/2
  have p3 : 3 ≤ p := by have := hp.two_le; omega
  have halves (p : ℕ) (hp : p.Prime) (h : p ≠ 2) : p+1=2*((p+1)/2) := by
    have := Nat.odd_iff.mp (hp.odd_of_ne_two h)
    omega
  have px : p+1=2*x := halves _ hp hodd
  have qy : q+1=2*y := halves _ hq (by omega)
  have rz : r+1=2*z := halves _ hr (by omega)
  have cp := (Nat.coprime_primes hp hq).mpr hpq.ne
  have cr : (p*q).Coprime r := Nat.coprime_mul_iff_left.mpr
    ⟨(Nat.coprime_primes hp hr).mpr (by omega), (Nat.coprime_primes hq hr).mpr hqr.ne⟩
  have ac : a (p*q*r)=x*y*z := by
    rw [OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime (Nat.mul_pos hp.pos hq.pos) hr.pos cr,
      OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime hp.pos hq.pos cp,
      OMA.R_OeisA224_conjecture_R1.card_squares_prime p hp hodd,
      OMA.R_OeisA224_conjecture_R1.card_squares_prime q hq (by omega),
      OMA.R_OeisA224_conjecture_R1.card_squares_prime r hr (by omega)]
  rw [ac] at htest
  have hs : 1 ≤ (p*q*r)^2 := Nat.succ_le_of_lt (pow_pos (mul_pos (mul_pos hp.pos hq.pos) hr.pos) _)
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hs).mp htest.symm
  apply no_triple k x y z p q r (by omega) (by omega) (by omega) px qy rz hp hq
  rw [mul_comm (x*y*z*(x*y*z-1)) k, ← mul_assoc] at hk
  omega

private theorem sorted_three (s : Finset ℕ) (h : s.card=3) :
    ∃ p q r : ℕ, p < q ∧ q < r ∧ s={p,q,r} := by
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := s.card_eq_three.mp h
  rcases lt_or_gt_of_ne hab with h₁ | h₁ <;>
    rcases lt_or_gt_of_ne hbc with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hac with h₃ | h₃ <;>
    first | omega
          | exact ⟨a,b,c,by omega,by omega,rfl⟩
          | exact ⟨a,c,b,by omega,by omega,by ext; simp; tauto⟩
          | exact ⟨b,a,c,by omega,by omega,by ext; simp; tauto⟩
          | exact ⟨b,c,a,by omega,by omega,by ext; simp; tauto⟩
          | exact ⟨c,a,b,by omega,by omega,by ext; simp; tauto⟩
          | exact ⟨c,b,a,by omega,by omega,by ext; simp; tauto⟩

private theorem squarefree_three {n : ℕ} (odd : Odd n) (sf : Squarefree n)
    (hc : n.primeFactors.card=3) : ¬ n^2 ≡ 1 [MOD a n*(a n-1)] := by
  obtain ⟨p,q,r,hpq,hqr,hs⟩ := sorted_three _ hc
  have memp : p ∈ n.primeFactors := by simp [hs]
  have memq : q ∈ n.primeFactors := by simp [hs]
  have memr : r ∈ n.primeFactors := by simp [hs]
  have hpr : p ≠ r := by omega
  have hn := Nat.prod_primeFactors_of_squarefree sf
  have val : n=p*q*r := by
    rw [hs] at hn
    simpa [hpq.ne,hpr,hqr.ne,mul_assoc] using hn.symm
  have po : p ≠ 2 := by
    rintro rfl
    exact odd.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors memp)
  rw [val]
  exact triple_fails (Nat.prime_of_mem_primeFactors memp) (Nat.prime_of_mem_primeFactors memq)
    (Nat.prime_of_mem_primeFactors memr) po hpq hqr

-- Three distinct prime factors, with at least one repeated in the factorization.
def H1 : Prop :=
  ∀ n : ℕ, Odd n → n.primeFactors.card=3 → ¬ Squarefree n →
    (∃ p ∈ n.primeFactors, p < 16*(2^n.primeFactors.card)^3) →
    ¬ n^2 ≡ 1 [MOD a n*(a n-1)]

-- The four-distinct-primes case, including arbitrary positive exponents.
def H2 : Prop :=
  ∀ n : ℕ, Odd n → n.primeFactors.card=4 →
    (∃ p ∈ n.primeFactors, p < 16*(2^n.primeFactors.card)^3) →
    ¬ n^2 ≡ 1 [MOD a n*(a n-1)]

theorem main : H1 → H2 → OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1.H1 := by
  intro three four n odd lo hi small
  by_cases h : n.primeFactors.card = 3
  · by_cases sf : Squarefree n
    · exact squarefree_three odd sf h
    · exact three n odd h sf small
  · exact four n odd (by omega) small

end OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1
