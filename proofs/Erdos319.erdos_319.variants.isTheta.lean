import FormalConjectures.ErdosProblems.«319»

/-! A linear-size Egyptian fraction expansion from two disjoint ranges of primes.
For T a large power of 16, put N = T^18. Choose two primes from the disjoint
ranges (T^6,T^7] and (T^8,T^9]. Their reciprocal sums have uniform positive lower
bounds by Chebyshev's estimates. Multiplying each pair by small odd cofactors gives
at least a fixed multiple of N distinct integers in [N/8,N].

Bézout's identity expands the sum of their reciprocals as an integer combination
of the reciprocals of odd integers j up to L = T^9. Choose 0 ≤ u < j so that
adding u/(jL) clears the factor j from each denominator. Since L is a power of
two, the binary digits of u realize each correction with distinct even denominators
of odd part j. One final dyadic correction gives an integer from 1 to 10. Scaling
all denominators by that integer gives a sum of one, and adjoining a single negative
term at denominator one gives a minimal signed relation. -/
open Finset Filter Real
open scoped BigOperators Topology
namespace DenseEgyptian
noncomputable section

private def primes (u v : ℕ) := (Ioc u v).filter Nat.Prime
private def mass (s : Finset ℕ) : ℝ := ∑ p ∈ s, 1/(p : ℝ)

private theorem theta_lower : ∀ᶠ n : ℕ in atTop, (n : ℝ)/4 ≤ Chebyshev.theta n := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  filter_upwards [(Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (4*(|C|+4))), eventually_ge_atTop 1] with n hn hn1
  change 4*(|C|+4) ≤ √(n:ℝ) at hn
  have h := Chebyshev.psi_ge n
  have h' := hC n
  have hnn : 0 ≤ (n:ℝ) := by positivity
  have e := Real.sq_sqrt hnn
  have ep := Real.sq_sqrt (show 0 ≤ (n:ℝ)+1 by positivity)
  have hp := Real.sqrt_nonneg (n:ℝ)
  have hpp := Real.sqrt_nonneg ((n:ℝ)+1)
  have hsp : √((n:ℝ)+1) ≤ √(n:ℝ)+1 := by nlinarith
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (show 0 < (n:ℝ)+1 by positivity))
  rw [Real.log_sqrt (by positivity)] at hl
  have h2 : 1/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hc := mul_le_mul_of_nonneg_right (le_abs_self C) hp
  nlinarith [mul_le_mul_of_nonneg_right hn hp, mul_le_mul_of_nonneg_right h2 hnn]

private theorem cut (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    primes a c = primes a b ∪ primes b c := by
  ext x
  simp only [primes, mem_filter, mem_Ioc, mem_union]
  by_cases hp : x.Prime <;> simp [hp]; omega

private theorem sep (a b c : ℕ) : Disjoint (primes a b) (primes b c) := by
  rw [disjoint_left]
  simp [primes]; omega

private theorem shell : ∀ᶠ j : ℕ in atTop,
    1 ≤ (64*((j : ℝ)+1)) * mass (primes (16^j) (16^(j+1))) := by
  have ht : Tendsto (fun j : ℕ => 16^(j+1) : ℕ → ℕ) atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (16:ℕ))).comp
      (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually theta_lower] with j hj
  let x : ℕ := 16^j
  let y : ℕ := 16^(j+1)
  have hxy : y = 16*x := by dsimp [x,y]; ring
  have hye : (y:ℝ) = 16*(x:ℝ) := by exact_mod_cast hxy
  have hpos : 0 < x := by positivity
  have hxy' : x ≤ y := by omega
  have hy : (y:ℝ)/4 ≤ Chebyshev.theta y := hj
  have hx := Chebyshev.theta_le_log4_mul_x (x := (x:ℝ)) (by positivity)
  have h4 : Real.log 4 ≤ 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num; linarith [Real.log_two_lt_d9]
  have e (n : ℕ) : Chebyshev.theta n = ∑ p ∈ primes 0 n, Real.log p := by
    simp [Chebyshev.theta,primes]
  rw [e, cut 0 x y (by omega) hxy', sum_union (sep ..)] at hy
  rw [e] at hx
  have lower : (x:ℝ) ≤ ∑ p ∈ primes x y, Real.log p := by
    rw [hye] at hy
    nlinarith [mul_le_mul_of_nonneg_right h4 (show 0 ≤ (x:ℝ) by positivity)]
  have upper : (∑ p ∈ primes x y, Real.log p) ≤ ((y:ℝ)*Real.log y)*mass (primes x y) := by
    rw [mass, mul_sum]
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hp',hpr⟩ := mem_filter.mp hp
    have hpy := (mem_Ioc.mp hp').2
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast hpr.pos
    have hyp : (p:ℝ) ≤ y := by exact_mod_cast hpy
    rw [mul_one_div, le_div_iff₀ hp0]
    apply le_trans (mul_le_mul_of_nonneg_right (Real.log_le_log hp0 hyp) hp0.le)
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right hyp (Real.log_nonneg (by exact_mod_cast hpr.one_le.trans hpy))
  have hylog : Real.log y ≤ 4*((j:ℝ)+1) := by
    dsimp [y]; push_cast; rw [Real.log_pow]
    have hs : Real.log 16 ≤ 4 := by
      rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num; linarith [Real.log_two_lt_d9]
    push_cast; nlinarith [mul_le_mul_of_nonneg_right hs (show 0 ≤ (j:ℝ)+1 by positivity)]
  have hm : 0 ≤ mass (primes x y) := sum_nonneg (fun _ _ => by positivity)
  have htotal := lower.trans (upper.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hylog (Nat.cast_nonneg y)) hm))
  rw [hye] at htotal
  exact (le_of_mul_le_mul_left (a := (x:ℝ)) (by convert htotal using 1 <;> ring)
    (by positivity))

private theorem window (k b : ℕ) (hk : 0 < k) (hb : 1 ≤ b) (hb' : b ≤ 8)
    (hj : ∀ j ≥ k, 1 ≤ (64*((j:ℝ)+1))*mass (primes (16^j) (16^(j+1)))) :
    (1:ℝ)/576 ≤ mass (primes (16^(b*k)) (16^((b+1)*k))) := by
  let a := b*k
  have hka : k ≤ a := by dsimp [a]; nlinarith
  have hind : ∀ l ≤ k, (l:ℝ) ≤ (576*(k:ℝ))*mass (primes (16^a) (16^(a+l))) := by
    intro l; induction l with
    | zero => intro _; simp [mass,primes]
    | succ l ih =>
      intro hl
      have hstep := hj (a+l) (by omega)
      have hL : a+l+1 ≤ 9*k := by dsimp [a]; nlinarith
      have hnon : 0 ≤ mass (primes (16^(a+l)) (16^(a+l+1))) :=
        sum_nonneg fun _ _ => by positivity
      have hreal : 64*((a+l:ℕ)+1:ℝ) ≤ 576*k := by exact_mod_cast (show 64*(a+l+1) ≤ 576*k by omega)
      have hg := mul_le_mul_of_nonneg_right hreal hnon
      change ((l+1:ℕ):ℝ) ≤ (576*(k:ℝ))*mass (primes (16^a) (16^(a+l+1)))
      rw [cut (16^a) (16^(a+l)) (16^(a+l+1))
        (Nat.pow_le_pow_right (by decide) (by omega)) (Nat.pow_le_pow_right (by decide) (by omega))]
      rw [mass, sum_union (sep ..)]
      change (l+1:ℕ) ≤ (576*(k:ℝ))*(mass _ + mass _)
      push_cast at hstep hg ⊢
      nlinarith [ih (by omega)]
  have h := hind k le_rfl
  have hpow : (b+1)*k = a+k := by dsimp [a]; ring
  rw [hpow]
  have hk' : 0 < (k:ℝ) := by positivity
  exact (le_of_mul_le_mul_left (a:=(k:ℝ)) (by convert (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (1:ℝ)/576)) using 1 <;> ring) hk')

private def spanQ (S : Finset ℕ) (r : ℚ) : Prop :=
  ∃ z : ℕ → ℤ, r = ∑ d ∈ S, (z d : ℚ)/d

private theorem rep_one {S : Finset ℕ} {d : ℕ} (hd : d ∈ S) : spanQ S (1/d) := by
  refine ⟨fun j => if j=d then 1 else 0, ?_⟩
  simp [ite_div, hd, apply_ite]

private theorem rep_comb {S : Finset ℕ} {r s : ℚ} (hr : spanQ S r) (hs : spanQ S s)
    (a b : ℤ) : spanQ S (a*r + b*s) := by
  obtain ⟨u,rfl⟩ := hr
  obtain ⟨v,rfl⟩ := hs
  refine ⟨fun n => a*u n+b*v n, ?_⟩
  rw [mul_sum,mul_sum,← sum_add_distrib]
  exact sum_congr rfl fun i _ => by push_cast; ring

private theorem rep_coprime {S : Finset ℕ} {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (h : a.Coprime b) (ra : spanQ S (1/a)) (rb : spanQ S (1/b)) :
    spanQ S (1/((a*b:ℕ):ℚ)) := by
  have e := Nat.gcd_eq_gcd_ab a b
  rw [h] at e
  have e' : (1:ℚ) = a*(a.gcdA b:ℚ)+b*(a.gcdB b:ℚ) := by exact_mod_cast e
  convert rep_comb ra rb (a.gcdB b) (a.gcdA b) using 1
  push_cast
  field_simp
  all_goals linarith

private theorem rep_sum {S A : Finset ℕ} (h : ∀ n ∈ A, spanQ S (1/n)) :
    spanQ S (∑ n ∈ A, (1:ℚ)/n) := by
  induction A using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | @insert a A ha ih =>
    rw [sum_insert ha]
    simpa using rep_comb (h a (by simp)) (ih fun n hn => h n (by simp [hn])) 1 1

private def halfTerms (N p q : ℕ) := N/(8*(p*q))
private def cof (N p q j : ℕ) := 2*(halfTerms N p q+j)+1

private theorem cof_bounds {T p q j : ℕ} (hT : 16 ≤ T)
    (hp : T^6 < p ∧ p ≤ T^7) (hq : T^8 < q ∧ q ≤ T^9)
    (hj : j < halfTerms (T^18) p q) :
    0 < cof (T^18) p q j ∧ cof (T^18) p q j < T^6 ∧
    T^18 ≤ 8*(p*q*cof (T^18) p q j) ∧ p*q*cof (T^18) p q j ≤ T^18 := by
  let N := T^18
  let h := halfTerms N p q
  have ht : 1 ≤ T := by omega
  have hpq0 : 0 < p*q := Nat.mul_pos (by omega) (by omega)
  have hg : 8*(p*q) ≤ N := by
    calc
      _ ≤ 8*(T^7*T^9) := by gcongr <;> omega
      _ ≤ T^2*(T^7*T^9) := by gcongr; nlinarith
      _ = N := by dsimp [N]; ring
  have hdiv := Nat.div_mul_le_self N (8*(p*q))
  have hrem := Nat.lt_div_mul_add (a:=N) (by omega : 0 < 8*(p*q))
  change h*(8*(p*q)) ≤ N at hdiv
  change N < h*(8*(p*q)) + 8*(p*q) at hrem
  change j < h at hj
  change 0 < 2*(h+j)+1 ∧ 2*(h+j)+1 < T^6 ∧
    N ≤ 8*(p*q*(2*(h+j)+1)) ∧ p*q*(2*(h+j)+1) ≤ N
  have hh : 1 ≤ h := by omega
  have he : p*q*(2*(h+j)+1) ≤ N := by
    nlinarith [Nat.mul_le_mul_left (p*q) (show 2*(h+j)+1 ≤ 8*h by omega)]
  refine ⟨by omega, ?_, ?_, he⟩
  · by_contra! hn
    have bound := Nat.mul_le_mul (Nat.mul_le_mul hp.1.le hq.1.le) hn
    have bad : T^20 ≤ T^18 := by
      calc T^20 = T^6*T^8*T^6 := by ring
           _ ≤ _ := bound.trans he
    exact (Nat.pow_lt_pow_right (by omega : 1 < T) (by decide : 18<20)).not_ge bad
  · have hle : N ≤ 8*(p*q*(2*(h+j)+1)) := by nlinarith [Nat.zero_le (p*q*j)]
    omega

private def oddPool (L : ℕ) := (Icc 2 L).filter Odd
private theorem prime_match {p a b c : ℕ} (hp : p.Prime) (hb : b.Prime)
    (ha : 0<a) (hc : 0<c) (hap : a < p) (hcp : c < p) (h : p ∣ a*b*c) : p=b := by
  rcases hp.dvd_mul.mp h with hab|hpc
  · rcases hp.dvd_mul.mp hab with hpa|hpb
    · exact False.elim (hap.not_ge (Nat.le_of_dvd ha hpa))
    · exact (Nat.prime_dvd_prime_iff_eq hp hb).mp hpb
  · exact False.elim (hcp.not_ge (Nat.le_of_dvd hc hpc))

private theorem many (T : ℕ) (ht : 16 ≤ T)
    (hP : 1/576 ≤ mass (primes (T^6) (T^7)))
    (hQ : 1/576 ≤ mass (primes (T^8) (T^9))) :
    ∃ A : Finset ℕ, (T^18 : ℝ)/(16*576^2) ≤ A.card ∧
      ∀ n ∈ A, 2 ≤ n ∧ Odd n ∧ n ≤ T^18 ∧ T^18 ≤ 8*n ∧
        spanQ (oddPool (T^9)) (1/n) := by
  classical
  let P := primes (T^6) (T^7)
  let Q := primes (T^8) (T^9)
  let N := T^18
  let D := (P ×ˢ Q).sigma fun pq => range (halfTerms N pq.1 pq.2)
  let f (d : Σ _ : ℕ × ℕ, ℕ) := d.1.1*d.1.2*cof N d.1.1 d.1.2 d.2
  have pSpec {p : ℕ} (hp : p∈P) := And.intro (mem_Ioc.mp (mem_filter.mp hp).1) (mem_filter.mp hp).2
  have qSpec {q : ℕ} (hq : q∈Q) := And.intro (mem_Ioc.mp (mem_filter.mp hq).1) (mem_filter.mp hq).2
  have pqGap : T^7 < T^8 := Nat.pow_lt_pow_right (by omega) (by decide)
  have dSpec {p q j : ℕ} (hd : (⟨(p,q),j⟩ : Σ _ : ℕ × ℕ, ℕ) ∈ D) :
      p∈P ∧ q∈Q ∧ j < halfTerms N p q := by simpa [D, and_assoc] using hd
  have inj : Set.InjOn f D := by
    rintro ⟨⟨p,q⟩,j⟩ hd ⟨⟨p',q'⟩,j'⟩ hd' he
    rcases dSpec hd with ⟨hp,hq,hj⟩
    rcases dSpec hd' with ⟨hp',hq',hj'⟩
    rcases pSpec hp with ⟨hp,pr⟩; rcases pSpec hp' with ⟨hp',pr'⟩
    rcases qSpec hq with ⟨hq,qr⟩; rcases qSpec hq' with ⟨hq',qr'⟩
    have c' := cof_bounds ht hp' hq' hj'
    have c := cof_bounds ht hp hq hj
    change p*q*cof N p q j = p'*q'*cof N p' q' j' at he
    have hqD : q ∣ p'*q'*cof N p' q' j' := he ▸ dvd_mul_of_dvd_left (dvd_mul_left q p) _
    have hqq : q=q' := prime_match qr qr' pr'.pos c'.1 (by omega) (by omega) hqD
    subst q'
    have he' : p*cof N p q j = p'*cof N p' q j' := by
      apply Nat.eq_of_mul_eq_mul_left qr.pos
      convert he using 1 <;> ring
    have hpd : p ∣ p'*cof N p' q j' := he' ▸ dvd_mul_right _ _
    have hpp : p=p' := by
      rcases pr.dvd_mul.mp hpd with hab|hab
      · exact (Nat.prime_dvd_prime_iff_eq pr pr').mp hab
      · exact False.elim ((show cof N p' q j' < p by dsimp [N]; omega).not_ge (Nat.le_of_dvd c'.1 hab))
    subst p'
    have := Nat.eq_of_mul_eq_mul_left pr.pos he'
    simp only [cof] at this
    congr 2; omega
  refine ⟨D.image f, ?_, ?_⟩
  · rw [card_image_of_injOn inj, card_sigma, sum_product]
    simp only [card_range, Nat.cast_sum]
    have bound (p q : ℕ) (hp : p∈P) (hq : q∈Q) :
        (N:ℝ)/(16*(p*q)) ≤ halfTerms N p q := by
      rcases pSpec hp with ⟨hp,pr⟩; rcases qSpec hq with ⟨hq,qr⟩
      have hd : 8*(p*q) ≤ N := by
        calc _ ≤ 8*(T^7*T^9) := by gcongr <;> omega
             _ ≤ T^2*(T^7*T^9) := by gcongr; nlinarith
             _ = N := by dsimp [N]; ring
      have hpos := Nat.mul_pos pr.pos qr.pos
      have hhalf : 0 < halfTerms N p q := (Nat.div_pos hd (by positivity))
      have hrem := Nat.lt_div_mul_add (a:=N) (by positivity : 0<8*(p*q))
      change N < halfTerms N p q*(8*(p*q))+8*(p*q) at hrem
      have hp0 := pr.pos; have hq0 := qr.pos
      rw [div_le_iff₀ (by positivity : (0:ℝ)<16*(p*q))]
      exact_mod_cast (show N ≤ halfTerms N p q*(16*(p*q)) by
        nlinarith [Nat.mul_le_mul_left (p*q) hhalf])
    calc
      _ ≤ (N:ℝ)/16*(mass P*mass Q) := by
        have hm := mul_le_mul hP hQ (by norm_num) (hP.trans' (by norm_num))
        have := mul_le_mul_of_nonneg_left hm (by positivity : 0≤(N:ℝ)/16)
        change (T:ℝ)^18/(16*576^2) ≤ ((T^18:ℕ):ℝ)/16*(mass P*mass Q)
        dsimp [N] at this; push_cast at this ⊢; linarith
      _ = ∑ p ∈ P, ∑ q ∈ Q, (N:ℝ)/(16*(p*q)) := by
        simp only [mass, sum_mul, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by simp [div_eq_mul_inv]; ring
      _ ≤ _ := sum_le_sum fun p hp => sum_le_sum fun q hq => bound p q hp hq
  · intro n hn
    obtain ⟨⟨⟨p,q⟩,j⟩,hd,rfl⟩ := mem_image.mp hn
    rcases dSpec hd with ⟨hp,hq,hj⟩
    rcases pSpec hp with ⟨hp,pr⟩; rcases qSpec hq with ⟨hq,qr⟩
    obtain ⟨hc,hc',hlo,hhi⟩ := cof_bounds ht hp hq hj
    let i := cof N p q j
    have hiodd : Odd i := ⟨_,rfl⟩
    have hpp : 2 < p := by have hh := Nat.le_self_pow (by decide : 6≠0) T; omega
    have hqq : 2 < q := by omega
    have hpo := pr.odd_of_ne_two (by omega)
    have hqo := qr.odd_of_ne_two (by omega)
    have hpool (d : ℕ) (hd : 2 ≤ d) (hd' : d ≤ T^9) (ho : Odd d) : d ∈ oddPool (T^9) :=
      mem_filter.mpr ⟨mem_Icc.mpr ⟨hd,hd'⟩,ho⟩
    have hile : 2 ≤ i := by dsimp [i,cof]; omega
    have hip : i < p := by dsimp [i,N]; omega
    have hiq : i < q := by omega
    have hpq : p < q := by omega
    have h69 : T^6 ≤ T^9 := Nat.pow_le_pow_right (by omega) (by decide)
    have h79 : T^7 ≤ T^9 := Nat.pow_le_pow_right (by omega) (by decide)
    have hcp : p.Coprime i := pr.coprime_iff_not_dvd.mpr fun h => hip.not_ge (Nat.le_of_dvd (by omega) h)
    have hcq : q.Coprime i := qr.coprime_iff_not_dvd.mpr fun h => hiq.not_ge (Nat.le_of_dvd (by omega) h)
    have hpqr := pr.coprime_iff_not_dvd.mpr (show ¬ p ∣ q from fun h => hpq.ne ((Nat.prime_dvd_prime_iff_eq pr qr).mp h))
    change 2 ≤ p*q*i ∧ _ ∧ _ ∧ _ ∧ _
    exact ⟨by nlinarith [Nat.mul_pos pr.pos qr.pos], (hpo.mul hqo).mul hiodd, hhi, hlo,
      rep_coprime (Nat.mul_pos pr.pos qr.pos) hc (hcp.mul_left hcq)
        (rep_coprime pr.pos qr.pos hpqr (rep_one (hpool p (by omega) (by omega) hpo))
          (rep_one (hpool q (by omega) hq.2 hqo)))
        (rep_one (hpool i hile (by dsimp [i,N]; omega) hiodd))⟩

private def packet (j K u : ℕ) : Finset ℕ :=
  u.bitIndices.toFinset.image fun b => j*2^(K-b)

private theorem bits_lt {b K u : ℕ} (hu : u<2^K) (hb : b ∈ u.bitIndices.toFinset) : b<K := by
  have h := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hb)
  exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (lt_of_le_of_lt h hu)

private theorem packet_sum {j K u : ℕ} (hj : 0<j) (hu : u<2^K) :
    (∑ n ∈ packet j K u, (1:ℚ)/n) = u/(j*(2:ℚ)^K) := by
  rw [packet, sum_image]
  · have hterm (b : ℕ) (hb : b∈u.bitIndices.toFinset) :
        (1:ℚ)/(j*2^(K-b):ℕ) = (2:ℚ)^b/(j*2^K) := by
      have h := bits_lt hu hb
      push_cast
      have he : (2:ℚ)^K = 2^b*2^(K-b) := by rw [← pow_add]; congr 1; omega
      rw [he]; field_simp
    rw [sum_congr rfl hterm, ← sum_div]
    have hsum : ∑ b ∈ u.bitIndices.toFinset, 2^b = u := by
      rw [List.sum_toFinset _ Nat.bitIndices_sorted.nodup, Nat.sum_map_two_pow_bitIndices]
    exact_mod_cast congrArg (fun t : ℚ => t/(j*(2:ℚ)^K)) (show (∑ b ∈ u.bitIndices.toFinset, (2:ℚ)^b) = u by exact_mod_cast hsum)
  · intro b hb c hc he
    have powEq := Nat.eq_of_mul_eq_mul_left hj he
    have h := Nat.pow_right_injective (by decide : 2≤2) powEq
    have := bits_lt hu hb; have := bits_lt hu hc; omega

private theorem packet_even {j K u n : ℕ} (hu : u<2^K) (hn : n∈packet j K u) : Even n := by
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hn
  have h := bits_lt hu hb
  have he : K-b = (K-b-1)+1 := by omega
  rw [he,pow_succ]; exact even_two.mul_left _ |>.mul_left _

private theorem odd_unique {a b i j : ℕ} (ha : Odd a) (hb : Odd b)
    (he : a*2^i = b*2^j) : a=b := by
  apply Nat.dvd_antisymm
  · apply (ha.coprime_two_right.pow_right j).dvd_of_dvd_mul_right
    exact he ▸ dvd_mul_right a _
  · apply (hb.coprime_two_right.pow_right i).dvd_of_dvd_mul_right
    exact he.symm ▸ dvd_mul_right b _

private theorem packet_sep {j j' K u u' : ℕ} (hj : Odd j) (hj' : Odd j') (hne : j≠j') :
    Disjoint (packet j K u) (packet j' K u') := by
  rw [disjoint_left]
  intro n hn hm
  obtain ⟨b,_,rfl⟩ := mem_image.mp hn
  obtain ⟨a,_,he⟩ := mem_image.mp hm
  exact hne (odd_unique hj hj' he.symm)

private theorem packet_bounds {j K u n : ℕ} (hj : 1≤j) (hj' : j≤2^K)
    (hu : u<2^K) (hn : n∈packet j K u) : 2≤n ∧ n≤(2^K)^2 := by
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hn
  have h := bits_lt hu hb
  constructor
  · calc 2 = 1*2^1 := by norm_num
         _ ≤ j*2^(K-b) := Nat.mul_le_mul hj (Nat.pow_le_pow_right (by decide) (by omega))
  · rw [pow_two]
    exact Nat.mul_le_mul hj' (Nat.pow_le_pow_right (by decide) (Nat.sub_le ..))

private theorem residue (j : ℕ) (hj : 0<j) (a : ℤ) :
    ∃ u : ℕ, u<j ∧ ∃ b : ℤ, a+u=b*j := by
  let r := (-a) % (j:ℤ)
  have h0 : 0≤r := Int.emod_nonneg _ (by exact_mod_cast hj.ne')
  have h1 : r < j := Int.emod_lt_of_pos _ (by exact_mod_cast hj)
  refine ⟨r.toNat, by omega, -((-a)/(j:ℤ)), ?_⟩
  rw [Int.toNat_of_nonneg h0]
  dsimp [r]
  rw [Int.emod_def]; ring

private theorem correct {K : ℕ} {r : ℚ} (hr : spanQ (oddPool (2^K)) r)
    (hr0 : 0<r) (hr8 : r≤8) :
    ∃ D : Finset ℕ, (∀ n ∈ D, Even n ∧ 2≤n ∧ n≤(2^K)^2) ∧
      ∃ d : ℕ, 0<d ∧ d≤10 ∧ r + (∑ n ∈ D, (1:ℚ)/n) = d := by
  classical
  let L : ℕ := 2^K
  let S := oddPool L
  obtain ⟨z,hz⟩ := hr
  have hL : 0<L := by dsimp [L]; positivity
  have hLq : (L:ℚ) = 2^K := by simp [L]
  have hS {j} (hj : j ∈ S) : (2≤j ∧ j≤L) ∧ Odd j :=
    ⟨mem_Icc.mp (mem_filter.mp hj).1, (mem_filter.mp hj).2⟩
  have ex : ∀ j : ℕ, ∃ u : ℕ, ∃ b : ℤ, j∈S → u<j ∧ (L:ℤ)*z j + u=b*j := by
    intro j; by_cases hj : j∈S
    · obtain ⟨u,hu,b,hb⟩ := residue j (by have := (hS hj).1; omega) ((L:ℤ)*z j)
      exact ⟨u,b,fun _ => ⟨hu,hb⟩⟩
    · exact ⟨0,0,by simp [hj]⟩
  choose u b hub using ex
  let C := S.biUnion fun j => packet j K (u j)
  have hult {j} (hj : j∈S) : u j < 2^K := (hub j hj).1.trans_le (hS hj).1.2
  have hsum : (∑ n ∈ C, (1:ℚ)/n) = ∑ j ∈ S, (u j:ℚ)/(j*L) := by
    rw [Finset.sum_biUnion]
    · exact sum_congr rfl fun j hj => by rw [packet_sum (by have := (hS hj).1; omega) (hult hj), hLq]
    · intro j hj j' hj' hne
      exact packet_sep (hS hj).2 (hS hj').2 hne
  have hsBound : (∑ n ∈ C, (1:ℚ)/n) ≤ 1 := by
    rw [hsum]
    have hcard : S.card ≤ L := by
      calc S.card ≤ (Icc 1 L).card := card_le_card fun j hj => mem_Icc.mpr ⟨by have := (hS hj).1; omega,(hS hj).1.2⟩
           _ = _ := by simp
    calc
      _ ≤ ∑ _j ∈ S, (1:ℚ)/L := by
        apply sum_le_sum
        intro j hj
        have hj0 : 0<j := by have := (hS hj).1; omega
        rw [← div_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact (div_le_one (by positivity)).mpr (by exact_mod_cast (hub j hj).1.le)
      _ = S.card / (L:ℚ) := by simp [nsmul_eq_mul, div_eq_mul_inv]
      _ ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hcard)
  let B := ∑ j ∈ S, b j
  have eqB : r + (∑ n ∈ C, (1:ℚ)/n) = (B:ℚ)/L := by
    rw [hz, hsum, ← sum_add_distrib, Int.cast_sum, sum_div]
    apply sum_congr rfl
    intro j hj
    have hj0 : 0<j := by have := (hS hj).1; omega
    have hb : (L:ℚ)*(z j:ℚ)+(u j:ℚ) = (b j:ℚ)*j := by exact_mod_cast (hub j hj).2
    field_simp
    all_goals nlinarith
  obtain ⟨v,hv,d,hd⟩ := residue L hL B
  let V := packet 1 K v
  have hV : (∑ n ∈ V, (1:ℚ)/n) = v/(L:ℚ) := by
    simpa [V,hLq] using packet_sum (j:=1) (by decide) hv
  have disj : Disjoint C V := by
    rw [disjoint_left]
    intro n hn hnv
    obtain ⟨j,hj,hnj⟩ := mem_biUnion.mp hn
    exact disjoint_left.mp (packet_sep (K:=K) (u:=u j) (u':=v) (hS hj).2 (by decide : Odd 1)
      (by have := (hS hj).1; omega)) hnj hnv
  have hD : r + ∑ n ∈ C ∪ V, (1:ℚ)/n = (d:ℚ) := by
    rw [sum_union disj, ← add_assoc, eqB, hV, ← add_div, div_eq_iff (by positivity)]
    exact_mod_cast hd
  have hd0 : 0<d := by
    have hnon : 0 ≤ ∑ n ∈ C ∪ V, (1:ℚ)/n := sum_nonneg fun _ _ => by positivity
    exact_mod_cast (show (0:ℚ)<d by linarith)
  have hd10 : d ≤ 10 := by
    have h1 : (v:ℚ)/L ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hv.le)
    rw [sum_union disj,hV] at hD
    exact_mod_cast (show (d:ℚ) ≤ 10 by linarith)
  refine ⟨C ∪ V, ?_, d.toNat, by omega, by omega, by rw [hD]; exact_mod_cast (Int.toNat_of_nonneg hd0.le).symm⟩
  intro n hn
  rcases mem_union.mp hn with hc|hv'
  · obtain ⟨j,hj,hnj⟩ := mem_biUnion.mp hc
    exact ⟨packet_even (hult hj) hnj, packet_bounds (by have := (hS hj).1; omega) (hS hj).1.2 (hult hj) hnj⟩
  · exact ⟨packet_even hv hv', packet_bounds (by decide) hL hv hv'⟩

private def minimal (B : Finset ℕ) : Prop :=
  ∃ δ : ℕ → ℤˣ, (∑ n ∈ B, (δ n:ℚ)/n) = 0 ∧
    ∀ B' ⊂ B, B'.Nonempty → (∑ n ∈ B', (δ n:ℚ)/n) ≠ 0

private theorem minimal_of_one {S : Finset ℕ} (hm : ∀ n ∈ S, 2≤n)
    (h : (∑ n ∈ S, (1:ℚ)/n)=1) : minimal (insert 1 S) := by
  let δ (n : ℕ) : ℤˣ := if n=1 then -1 else 1
  have hs : 1∉S := fun hn => by have := hm 1 hn; omega
  have val {n : ℕ} (hn : n≠1) : (δ n:ℚ) = 1 := by simp [δ,hn]
  have good {n : ℕ} (hn : n∈insert 1 S) (h' : n≠1) : 0 < (δ n:ℚ)/n := by
    rw [val h']; have := hm n (mem_of_mem_insert_of_ne hn h')
    positivity
  have total : (∑ n ∈ insert 1 S, (δ n:ℚ)/n) = 0 := by
    rw [sum_insert hs]
    have e : (∑ n ∈ S, (δ n:ℚ)/n) = ∑ n ∈ S, (1:ℚ)/n :=
      sum_congr rfl fun n hn => by rw [val (fun h => hs (h ▸ hn))]
    rw [e,h]; norm_num [δ]
  refine ⟨δ,total,?_⟩
  intro B hB hne
  by_cases h1 : 1∈B
  · have hpos : 0 < ∑ n ∈ (insert 1 S) \ B, (δ n:ℚ)/n := by
      apply sum_pos _ (sdiff_nonempty.mpr hB.not_ge)
      intro n hn
      obtain ⟨hx,hy⟩ := mem_sdiff.mp hn
      exact good hx (by rintro rfl; exact hy h1)
    have he := sum_sdiff hB.subset (f:=fun n => (δ n:ℚ)/n)
    rw [total] at he
    linarith
  · exact (sum_pos (fun n hn => good (hB.subset hn) (by rintro rfl; exact h1 hn)) hne).ne'

private theorem scaled (k : ℕ) (hk : 1≤k)
    (hj : ∀ j≥k, 1 ≤ (64*((j:ℝ)+1))*mass (primes (16^j) (16^(j+1)))) :
    ∃ B : Finset ℕ, B ⊆ Icc 1 (10*(16^18)^k) ∧ minimal B ∧
      (((16^18)^k:ℕ):ℝ)/(16*576^2) ≤ B.card := by
  let T : ℕ := 16^k
  let N := T^18
  let K := 36*k
  have hT : 16≤T := (Nat.pow_le_pow_right (by decide : 0<16) hk : 16^1≤16^k)
  have eL : 2^K = T^9 := by
    dsimp [K,T]; rw [show (16:ℕ)=2^4 by decide, ← pow_mul, ← pow_mul]; congr 1; ring
  have eN : (16^18)^k = N := by change ((16:ℕ)^18)^k = (16^k)^18; rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have eN' : (2^K)^2 = N := by rw [eL, ← pow_mul]
  have win (b : ℕ) (hb : 1≤b) (hb' : b≤8) :
      1/576 ≤ mass (primes (T^b) (T^(b+1))) := by
    convert window k b hk hb hb' hj using 2; dsimp [T]; simp only [← pow_mul]; ring_nf
  obtain ⟨A,hcard,hA⟩ := many T hT (win 6 (by decide) (by decide)) (win 8 (by decide) (by decide))
  have hlo : 0<N := by dsimp [N]; positivity
  have hpA : A.Nonempty := by
    by_contra! h
    have hpos : 0 < (T:ℝ)^18/(16*576^2) := by positivity
    rw [h,card_empty,Nat.cast_zero] at hcard
    linarith
  have hAb : A ⊆ Icc 1 N := fun a ha => mem_Icc.mpr ⟨by have := (hA a ha).1; omega,(hA a ha).2.2.1⟩
  have hcN : A.card ≤ N := (card_le_card hAb).trans (by simp)
  let r : ℚ := ∑ n ∈ A, 1/(n:ℚ)
  have hr0 : 0<r := sum_pos (fun n hn => by have := (hA n hn).1; positivity) hpA
  have hr8 : r≤8 := by
    calc
      _ ≤ ∑ _n ∈ A, (8:ℚ)/N := by
        apply sum_le_sum; intro n hn
        have nn := (hA n hn).1
        rw [div_le_div_iff₀ (by positivity : (0:ℚ)<n) (by positivity)]
        simpa using (show (N:ℚ) ≤ 8*n by exact_mod_cast (hA n hn).2.2.2.1)
      _ = A.card * (8:ℚ)/N := by simp [nsmul_eq_mul,mul_div_assoc]
      _ ≤ _ := by rw [div_le_iff₀ (by positivity)]; nlinarith [show (A.card:ℚ) ≤ N by exact_mod_cast hcN]
  have hr : spanQ (oddPool (2^K)) r := by
    rw [eL]; exact rep_sum fun n hn => (hA n hn).2.2.2.2
  obtain ⟨D,hD,d,hd,hd10,he⟩ := correct hr hr0 hr8
  have ad : Disjoint A D := disjoint_left.mpr fun n hn hm => (Nat.not_even_iff_odd.mpr (hA n hn).2.1) (hD n hm).1
  let X := A∪D
  have hx {n} (hn : n∈X) : 2≤n ∧ n≤N := by
    rcases mem_union.mp hn with ha|hd
    · exact ⟨(hA n ha).1,(hA n ha).2.2.1⟩
    · exact ⟨(hD n hd).2.1,eN' ▸ (hD n hd).2.2⟩
  have hsum : (∑ n ∈ X, (1:ℚ)/n) = d := by rw [sum_union ad]; exact he
  let f : ℕ ↪ ℕ := ⟨fun n => d*n, by intro a b h; exact Nat.eq_of_mul_eq_mul_left hd h⟩
  let S := X.map f
  have hs {n} (hn : n∈S) : 2≤n ∧ n≤10*N := by
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hn
    have bound := hx ha
    exact ⟨(by change 2≤d*a; nlinarith [Nat.mul_le_mul_right a hd]),Nat.mul_le_mul hd10 bound.2⟩
  have hs1 : (∑ n ∈ S, (1:ℚ)/n)=1 := by
    rw [sum_map]
    change ∑ n ∈ X, (1:ℚ)/(d*n:ℕ) = 1
    simp only [Nat.cast_mul,one_div,mul_inv_rev,← sum_mul]
    simp only [one_div] at hsum
    rw [hsum]; simp [hd.ne']
  rw [eN]
  refine ⟨insert 1 S, ?_, minimal_of_one (fun _ hn => (hs hn).1) hs1, ?_⟩
  · intro n hn; rcases mem_insert.mp hn with rfl|h
    · exact mem_Icc.mpr ⟨le_rfl,by omega⟩
    · exact mem_Icc.mpr ⟨by have := (hs h).1; omega,(hs h).2⟩
  · apply le_trans (by simpa [N] using hcard)
    exact_mod_cast (show A.card ≤ (insert 1 S).card from
      (card_le_card (show A ⊆ X from subset_union_left)).trans
        ((by simp [S] : X.card ≤ S.card).trans (card_le_card (subset_insert ..))))

end
end DenseEgyptian

open DenseEgyptian

theorem OMA.solution : type_of% @Erdos319.erdos_319.variants.isTheta := by
  intro _ c h
  have basic (N : ℕ) : 0≤c N ∧ c N≤N := by
    obtain ⟨A,hA,_,e⟩ := (h N).1
    rw [← e]
    refine ⟨by positivity, ?_⟩
    exact_mod_cast ((card_le_card hA).trans (by simp : (Icc 1 N).card ≤ N))
  constructor
  · apply Asymptotics.IsBigO.of_bound 1
    exact Filter.Eventually.of_forall fun N => by
      simpa [Erdos319.erdos_319.variants.isTheta.answer, Real.norm_eq_abs, abs_of_nonneg (basic N).1]
        using (basic N).2
  · let b : ℕ := 16^18
    have hb : 1<b := by decide
    obtain ⟨J,hJ⟩ := eventually_atTop.mp shell
    apply Asymptotics.IsBigO.of_bound ((20:ℝ)*b*(16*576^2))
    filter_upwards [eventually_ge_atTop (10*b^(J+1))] with n hn
    let k := Nat.log b (n/10)
    have hdiv : b^(J+1) ≤ n/10 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
    have hk : J+1 ≤ k := Nat.le_log_of_pow_le hb hdiv
    have hpow : 0<b^(J+1) := pow_pos (by omega) _
    have hNk : 10*b^k ≤ n := by
      have e := Nat.pow_log_le_self b (show n/10 ≠ 0 by omega)
      change b^k ≤ n/10 at e
      omega
    have nbound : n ≤ 20*b*(b^k) := by
      have e := Nat.lt_pow_succ_log_self hb (n/10)
      change n/10 < b^(k+1) at e
      rw [pow_succ] at e
      nlinarith [Nat.div_add_mod n 10, Nat.mod_lt n (by decide : 0<10)]
    obtain ⟨B,hB,hmin,hcard⟩ := scaled k (by omega) (fun j hj => hJ j (by omega))
    have hBc : (B.card:ℝ) ≤ c n := (h n).2 ⟨B,fun x hx =>
      mem_Icc.mpr ⟨(mem_Icc.mp (hB hx)).1, ((mem_Icc.mp (hB hx)).2).trans hNk⟩, hmin, rfl⟩
    change ((b^k:ℕ):ℝ)/(16*576^2) ≤ B.card at hcard
    have scaledBound : ((b^k:ℕ):ℝ) ≤ (16*576^2)*c n := by
      simpa only [mul_comm] using (div_le_iff₀ (by norm_num : 0<(16*576^2:ℝ))).mp (hcard.trans hBc)
    have nn : (n:ℝ) ≤ 20*(b:ℝ)*((b^k:ℕ):ℝ) := by exact_mod_cast nbound
    have mult := mul_le_mul_of_nonneg_left scaledBound (show 0 ≤ 20*(b:ℝ) by positivity)
    simp only [Erdos319.erdos_319.variants.isTheta.answer,Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg n (α:=ℝ)),abs_of_nonneg (basic n).1]
    linarith
