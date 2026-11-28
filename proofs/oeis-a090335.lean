import OMAStatements.S_oeis_a090335

/-!
# The binary prefix-code conjecture OEIS A090335

Proof submitted by James Coholan with Codex. The prime-counting argument uses
Chebyshev's bounds, as in Robert Leshner's proof of the related prime-power
result A088862 (open-math-agents PR #8119).

Take a product of n distinct primes in one short interval [P, P + W).
Two divisors greater than one can collide under binary truncation only if
their counts of prime factors differ by some positive d, and the least
integer with d-th power at least 2^k is in a short window about P.
Below W², with W = 2^J, both d and k are bounded. Discarding a bounded
number of intervals per possible root leaves enough primes to find one
surviving interval with n primes for sufficiently large J. The least
eligible integer then exists by well-ordering.
-/

open Finset

namespace A090335

theorem mul_pow_window (P W s i : ℕ) (hi : i * W ≤ s)
    (hs : s ≤ P) :
    (P - s) * (P + W)^i ≤ (P - s + i * W) * P^i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i * W ≤ s := by rw [Nat.succ_mul] at hi; omega
    have hcap : P - s + i * W ≤ P := by omega
    have hstep : (P - s + i * W) * (P + W) ≤
        (P - s + (i + 1) * W) * P := by
      calc
        _ = (P - s + i * W) * P + (P - s + i * W) * W := by ring
        _ ≤ (P - s + i * W) * P + P * W :=
          Nat.add_le_add_left (Nat.mul_le_mul_right W hcap) _
        _ = _ := by ring
    calc
      _ = ((P - s) * (P + W)^i) * (P + W) := by rw [pow_succ, mul_assoc]
      _ ≤ ((P - s + i * W) * P^i) * (P + W) :=
        Nat.mul_le_mul_right _ (ih hi')
      _ = ((P - s + i * W) * (P + W)) * P^i := by ring
      _ ≤ ((P - s + (i + 1) * W) * P) * P^i :=
        Nat.mul_le_mul_right _ hstep
      _ = _ := by ring

theorem prefix_window {P W n i j a b k : ℕ}
    (hW : 0 < W) (hP : 2 * ((n+1)*W) ≤ P)
    (hi : 0 < i) (hiN : i ≤ n) (hjN : j ≤ n)
    (haL : P^i ≤ a) (haU : a ≤ (P+W)^i)
    (hbL : P^j ≤ b) (hbU : b ≤ (P+W)^j)
    (hk : 0 < k) (hdiv : b / 2^k = a) :
    let s := (n+1)*W
    ∃ d : ℕ, 0 < d ∧ d ≤ n ∧ (P-s)^d < 2^k ∧ 2^k ≤ (P+W+4*s)^d := by
  dsimp only
  let s := (n+1)*W
  let Q := P+W
  change ∃ d : ℕ, 0 < d ∧ d ≤ n ∧ (P-s)^d < 2^k ∧ 2^k ≤ (Q+4*s)^d
  change 2*s ≤ P at hP
  change a ≤ Q^i at haU
  change b ≤ Q^j at hbU
  have hWs : W ≤ s := by dsimp [s]; rw [Nat.add_mul]; omega
  have hPpos : 0 < P := by omega
  have hSpos : 0 < P-s := by omega
  have hPQ : P ≤ Q := by dsimp [Q]; omega
  have hpow (t : ℕ) (ht : t ≤ n) : (P-s)*Q^t ≤ (P-W)*P^t := by
    have htw : t*W ≤ n*W := Nat.mul_le_mul_right _ ht
    have hsw : s = n*W+W := by dsimp [s]; rw [Nat.add_mul, one_mul]
    exact (mul_pow_window P W s t (by omega) (by omega)).trans
      (Nat.mul_le_mul_right _ (by omega))
  have hKpos : 0 < 2^k := by positivity
  have hlower : a * 2^k ≤ b :=
    (Nat.le_div_iff_mul_le hKpos).mp (by omega)
  have hupper : b < (a+1)*2^k :=
    (Nat.div_lt_iff_lt_mul hKpos).mp (by omega)
  have hjgt : i < j := by
    by_contra! hji
    have hq : Q^j < 2*P^j := by
      apply Nat.lt_of_mul_lt_mul_left (a := P-s)
      calc
        _ ≤ (P-W)*P^j := hpow j hjN
        _ < P * P^j := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
        _ ≤ (2*(P-s))*P^j := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
    have hk2 : 2 ≤ 2^k := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ k by omega)
    have hbad : b < a * 2^k := calc
      b ≤ Q^j := hbU
      _ < 2*P^j := hq
      _ ≤ 2*P^i := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hPpos hji)
      _ ≤ 2*a := Nat.mul_le_mul_left 2 haL
      _ ≤ a*2^k := by rw [mul_comm 2 a]; exact Nat.mul_le_mul_left a hk2
    omega
  obtain ⟨e, rfl⟩ : ∃ e, j = i + (e+1) := ⟨j-i-1, by omega⟩
  refine ⟨e+1, by omega, by omega, ?_, ?_⟩
  · have hadd : (a+1)*(P-s) ≤ P^(i+1) := by
      have hsmall : P-s ≤ W*P^i := calc
        _ ≤ P := Nat.sub_le _ _
        _ ≤ P^i := by
          simpa using Nat.pow_le_pow_right hPpos (show 1 ≤ i by omega)
        _ ≤ _ := by
          simpa using Nat.mul_le_mul_right (P^i) (show 1 ≤ W by omega)
      calc
        _ ≤ (Q^i+1)*(P-s) := Nat.mul_le_mul_right _ (by omega)
        _ = (P-s)*Q^i + (P-s) := by ring
        _ ≤ (P-W)*P^i + W*P^i := Nat.add_le_add (hpow i hiN) hsmall
        _ = P^(i+1) := by
          rw [← add_mul, Nat.sub_add_cancel (show W ≤ P by omega), pow_succ, mul_comm]
    have hb : (a+1)*(P-s)^(e+1) ≤ b := calc
      _ = ((a+1)*(P-s))*(P-s)^e := by rw [pow_succ', ← mul_assoc]
      _ ≤ P^(i+1)*P^e := Nat.mul_le_mul hadd (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
      _ = P^(i+(e+1)) := by rw [← pow_add]; congr 1; omega
      _ ≤ b := hbL
    exact Nat.lt_of_mul_lt_mul_left (hb.trans_lt hupper)
  · have hmul : P*Q ≤ (P-s)*(Q+4*s) := by
      have hQ : Q ≤ 4*(P-s) := by dsimp [Q]; omega
      have hsq := Nat.mul_le_mul_left s hQ
      have hsplit : P-s+s = P := Nat.sub_add_cancel (by omega)
      calc
        P*Q = (P-s)*Q+s*Q := by rw [← add_mul, hsplit]
        _ ≤ (P-s)*Q + s*(4*(P-s)) := Nat.add_le_add_left hsq _
        _ = _ := by ring
    have hpower : P*Q^(e+1) ≤ (P-s)*(Q+4*s)^(e+1) := calc
      _ = (P*Q)*Q^e := by rw [pow_succ', ← mul_assoc]
      _ ≤ ((P-s)*(Q+4*s))*(Q+4*s)^e :=
        Nat.mul_le_mul hmul (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by simp only [pow_succ', mul_assoc]
    have hub : b ≤ P^i*(Q+4*s)^(e+1) := by
      apply Nat.le_of_mul_le_mul_left _ hSpos
      calc
        (P-s)*b ≤ (P-s)*Q^(i+(e+1)) := Nat.mul_le_mul_left _ hbU
        _ = ((P-s)*Q^i)*Q^(e+1) := by rw [pow_add, mul_assoc]
        _ ≤ ((P-W)*P^i)*Q^(e+1) := Nat.mul_le_mul_right _ (hpow i hiN)
        _ ≤ (P*P^i)*Q^(e+1) := Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
        _ = P^i*(P*Q^(e+1)) := by ring
        _ ≤ P^i*((P-s)*(Q+4*s)^(e+1)) := Nat.mul_le_mul_left _ hpower
        _ = _ := by ring
    apply Nat.le_of_mul_le_mul_left _ (show 0 < P^i by positivity)
    exact ((Nat.mul_le_mul_right _ haL).trans hlower).trans hub


theorem dyadicRoot_exists (d k : ℕ) (hd : 0 < d) :
    ∃ r : ℕ, 2^k ≤ r^d := by
  refine ⟨2^k, ?_⟩
  calc
    _ = (2^k)^1 := by simp
    _ ≤ _ := Nat.pow_le_pow_right (by positivity) (by omega)

/-- The least integer whose d-th power reaches 2^k. Only positive d matters. -/
noncomputable def dyadicRoot (d k : ℕ) : ℕ :=
  if h : 0 < d then Nat.find (dyadicRoot_exists d k h) else 0

theorem dyadicRoot_bounds {d k lo hi : ℕ} (hd : 0 < d)
    (hlo : lo^d < 2^k) (hhi : 2^k ≤ hi^d) :
    lo < dyadicRoot d k ∧ dyadicRoot d k ≤ hi := by
  simp only [dyadicRoot, dif_pos hd]
  refine ⟨lt_of_not_ge (fun h => hlo.not_ge ?_), Nat.find_min' _ hhi⟩
  have hroot : 2^k ≤ (Nat.find (dyadicRoot_exists d k hd))^d :=
    Nat.find_spec (dyadicRoot_exists d k hd)
  exact hroot.trans (Nat.pow_le_pow_left h d)

/-- Chebyshev's estimates give a quantitative lower bound on prime counts at powers of 2. -/
theorem prime_count_at_power (K : ℕ) :
    2^K ≤ (2^K).primeCounting*K+(K+1) := by
  have h0 := Chebyshev.psi_ge (2^K)
  have h1 := Chebyshev.psi_le_primeCounting_mul_log (2^K)
  have h2 : (2:ℝ)^K+1 ≤ 2^(K+1) := by
    rw [pow_succ]
    have : (1:ℝ) ≤ 2^K := one_le_pow₀ (by norm_num)
    linarith
  have h3 := Real.log_le_log (by positivity : 0 < (2:ℝ)^K+1) h2
  push_cast at h0 h1
  rw [Real.log_pow] at h1 h3
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : (2:ℝ)^K ≤ (((2^K).primeCounting : ℕ):ℝ)*K + (K+1) := by
    apply le_of_mul_le_mul_right _ hl
    push_cast at h3
    nlinarith [h0.trans h1]
  exact_mod_cast he

theorem exists_large_power (C : ℕ) : ∃ J : ℕ, 1 ≤ J ∧ C*J^2 < 2^J := by
  have hh := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ) < 2)
  have hv : Filter.Tendsto (fun J : ℕ => (C:ℝ) * ((J:ℝ)^2 / (2:ℝ)^J))
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa using hh.const_mul (C:ℝ)
  rw [Metric.tendsto_nhds] at hv
  have he : ∀ᶠ J : ℕ in Filter.atTop, dist ((C:ℝ) * ((J:ℝ)^2 / (2:ℝ)^J)) 0 < 1 :=
    hv 1 (by norm_num)
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp he
  refine ⟨J+1, by omega, ?_⟩
  have hbound := hJ (J+1) (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hbound
  have hr : (C:ℝ)*((↑(J+1) : ℝ)^2) < (2:ℝ)^(J+1) := by
    rw [← mul_div_assoc] at hbound
    simpa using (div_lt_iff₀ (by positivity : 0 < (2:ℝ)^(J+1))).mp hbound
  exact_mod_cast hr

noncomputable def badBuckets (n J W : ℕ) : Finset ℕ :=
  range (2*(n+1)) ∪
    ((range (n+1)) ×ˢ (range (2*J*n+1))).biUnion
      (fun dk =>
        let c := dyadicRoot dk.1 dk.2 / W
        let R := 6*(n+1)+1
        Icc (c-R) (c+R))

theorem badBuckets_le (n J W : ℕ) :
    (badBuckets n J W).card ≤ 2*(n+1)+(n+1)*(2*J*n+1)*(2*(6*(n+1)+1)+1) := by
  unfold badBuckets
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · simp
  · have h := Finset.card_biUnion_le_card_mul
      (range (n+1) ×ˢ range (2*J*n+1))
      (fun dk =>
        let c := dyadicRoot dk.1 dk.2 / W
        let R := 6*(n+1)+1
        Icc (c-R) (c+R))
      (2*(6*(n+1)+1)+1) (by
        intro dk _
        dsimp only
        rw [Nat.card_Icc]
        omega)
    simpa only [Finset.card_product, Finset.card_range] using h

theorem mem_badBuckets_of_root {n J W q d k : ℕ}
    (hW : 0 < W) (hq : 2*(n+1) ≤ q) (hd : d ≤ n) (hk : k ≤ 2*J*n)
    (hl : q*W-(n+1)*W < dyadicRoot d k)
    (hu : dyadicRoot d k ≤ q*W+W+4*((n+1)*W)) :
    q ∈ badBuckets n J W := by
  let x := dyadicRoot d k
  let R := 6*(n+1)+1
  have hlow : (q-(n+1))*W ≤ x := by
    rw [Nat.sub_mul]
    exact hl.le
  have hup : x < (q+R+1)*W := by
    change x ≤ q*W+W+4*((n+1)*W) at hu
    calc
      x ≤ (q+1+4*(n+1))*W := by
        simpa only [Nat.add_mul, one_mul, Nat.mul_assoc] using hu
      _ < (q+R+1)*W := Nat.mul_lt_mul_of_pos_right (by dsimp [R]; omega) hW
  have hdivlo := (Nat.le_div_iff_mul_le hW).mpr hlow
  have hdivup := (Nat.div_lt_iff_lt_mul hW).mpr hup
  refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(d,k), ?_, ?_⟩)
  · simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  · change q ∈ Icc (x/W-R) (x/W+R)
    rw [Finset.mem_Icc]
    dsimp [R] at *
    omega

theorem exists_bucket (n : ℕ) :
    ∃ J q : ℕ,
      q ∉ badBuckets n J (2^J) ∧
      n ≤ ((Nat.primesLE ((2^J)^2)).filter (fun p => p / 2^J = q)).card := by
  let R := 6*(n+1)+1
  let A := 2*(n+1)+(n+1)*(2*n+1)*(2*R+1)+2*n
  obtain ⟨J, hJ, hlarge⟩ := exists_large_power (2*A+3)
  let W : ℕ := 2^J
  change (2*A+3)*J^2 < W at hlarge
  let bad := badBuckets n J W
  let good := (Finset.range (W+1)).filter (fun q => q ∉ bad)
  let primes := Nat.primesLE (W^2)
  let fiber := fun q => primes.filter (fun p => p/W=q)
  change ∃ J' q, q ∉ badBuckets n J' (2^J') ∧
    n ≤ ((Nat.primesLE ((2^J')^2)).filter (fun p => p / 2^J' = q)).card
  by_contra! hall
  have hgood q (hq : q ∈ good) : (fiber q).card ≤ n :=
    (hall J q (Finset.mem_filter.mp hq).2).le
  have hw : 0 < W := by dsimp [W]; positivity
  have hbad q : (fiber q).card ≤ W := by
    have hsub : fiber q ⊆ Ico (q*W) ((q+1)*W) := by
      intro p hp
      have hpq : p/W=q := (Finset.mem_filter.mp hp).2
      rw [Finset.mem_Ico]
      exact ⟨(Nat.le_div_iff_mul_le hw).mp (by omega),
        (Nat.div_lt_iff_lt_mul hw).mp (by omega)⟩
    refine (Finset.card_le_card hsub).trans ?_
    rw [Nat.card_Ico, Nat.add_mul, one_mul]
    omega
  have hcover : primes ⊆ bad.biUnion fiber ∪ good.biUnion fiber := by
    intro p hp
    let q := p/W
    have hf : p ∈ fiber q := Finset.mem_filter.mpr ⟨hp, rfl⟩
    by_cases hq : q ∈ bad
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q, hq, hf⟩)
    · have hpX : p ≤ W^2 := (Nat.mem_primesLE.mp hp).1
      have hqW : q < W+1 := by
        apply (Nat.div_lt_iff_lt_mul hw).mpr
        rw [Nat.add_mul, one_mul, sq] at *
        omega
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqW,hq⟩, hf⟩)
  have hgsize : good.card ≤ W+1 := by
    simpa [good] using Finset.card_filter_le (s := Finset.range (W+1)) (fun q => q ∉ bad)
  have hpi : primes.card ≤ bad.card*W+(W+1)*n := calc
    _ ≤ _ := Finset.card_le_card hcover
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add
      (Finset.card_biUnion_le_card_mul bad fiber W (fun q _ => hbad q))
      ((Finset.card_biUnion_le_card_mul good fiber n hgood).trans (Nat.mul_le_mul_right _ hgsize))
  have hcode : 2*J*n+1 ≤ J*(2*n+1) := by nlinarith only [hJ]
  have hbudget : bad.card+2*n ≤ A*J := by
    have h := badBuckets_le n J W
    change bad.card ≤ 2*(n+1)+(n+1)*(2*J*n+1)*(2*R+1) at h
    have hscale := Nat.mul_le_mul_right (2*R+1) (Nat.mul_le_mul_left (n+1) hcode)
    have hbase := Nat.mul_le_mul_left (2*(n+1)+2*n) hJ
    dsimp only [A]
    nlinarith only [h, hscale, hbase]
  have hpi' : (W^2).primeCounting ≤ A*J*W := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    have h := Nat.mul_le_mul_right W hbudget
    have hw' : W+1 ≤ 2*W := by omega
    have h2 := Nat.mul_le_mul_right n hw'
    change primes.card ≤ _
    nlinarith only [hpi, h, h2]
  have hx := prime_count_at_power (2*J)
  have hx' : 2^(2*J) = W^2 := by dsimp [W]; rw [mul_comm 2 J, pow_mul]
  rw [hx'] at hx
  have hax := Nat.mul_le_mul_right (2*J) hpi'
  have htail : 2*J+1 ≤ 3*J^2*W := by
    have hj2 : J ≤ J^2 := by
      simpa only [mul_one, sq] using Nat.mul_le_mul_left J hJ
    have h := Nat.mul_le_mul_left (3*J^2) (show 1 ≤ W by omega)
    nlinarith only [hj2, h, hJ]
  have hfinal : W^2 ≤ ((2*A+3)*J^2)*W := by
    nlinarith only [hx, hax, htail]
  exact (Nat.not_lt_of_ge (Nat.le_of_mul_le_mul_right (by simpa [sq] using hfinal) hw)) hlarge


theorem eligible_exists (n : ℕ) : ∃ m, OMA.S_oeis_a090335.eligible n m := by
  obtain ⟨J,q,hgood,hcount⟩ := exists_bucket n
  let W : ℕ := 2^J
  let P := q*W
  let X := W^2
  obtain ⟨S,hS,hcard⟩ := Finset.exists_subset_card_eq hcount
  have hW : 0 < W := by dsimp [W]; positivity
  have hq : 2*(n+1) ≤ q := by
    by_contra! h
    apply hgood
    exact Finset.mem_union_left _ (Finset.mem_range.mpr h)
  have hP : 2*((n+1)*W) ≤ P := by
    simpa only [P, Nat.mul_assoc] using Nat.mul_le_mul_right W hq
  have hpinfo (p : ℕ) (hp : p ∈ S) : p.Prime ∧ P ≤ p ∧ p ≤ P+W ∧ p ≤ X := by
    have ⟨hpX,hpq⟩ := Finset.mem_filter.mp (hS hp)
    change p/W=q at hpq
    change p ∈ Nat.primesLE X at hpX
    have hb := (Nat.div_lt_iff_lt_mul hW).mp (show p/W < q+1 by omega)
    rw [Nat.add_mul, one_mul] at hb
    exact ⟨(Nat.mem_primesLE.mp hpX).2,
      (Nat.le_div_iff_mul_le hW).mp hpq.ge, hb.le, (Nat.mem_primesLE.mp hpX).1⟩
  let m : ℕ := ∏ p ∈ S, p
  have hm : 0 < m := Finset.prod_pos (fun p hp => (hpinfo p hp).1.pos)
  have hmS : m.primeFactors = S :=
    Nat.primeFactors_prod (fun p hp => (hpinfo p hp).1)
  have hmsq : Squarefree m := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime (f := id)
    · intro p hp r hr hpr
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hpinfo p hp).1 (hpinfo r hr).1).mpr hpr)
    · exact fun p hp => (hpinfo p hp).1.squarefree
  have divisor_bounds (a : ℕ) (ha : a ∣ m) (ha1 : 1 < a) :
      let i := a.primeFactors.card
      0 < i ∧ i ≤ n ∧ P^i ≤ a ∧ a ≤ (P+W)^i ∧ a ≤ X^i := by
    let T := a.primeFactors
    have hT : T ⊆ S := hmS ▸ Nat.primeFactors_mono ha hm.ne'
    have hprod : ∏ p ∈ T, p = a :=
      Nat.prod_primeFactors_of_squarefree (hmsq.squarefree_of_dvd ha)
    have hpos : 0 < T.card := by
      rw [Finset.card_pos]
      by_contra! h
      rw [h, Finset.prod_empty] at hprod
      omega
    change 0 < T.card ∧ T.card ≤ n ∧ P^T.card ≤ a ∧
      a ≤ (P+W)^T.card ∧ a ≤ X^T.card
    refine ⟨hpos, hcard ▸ Finset.card_le_card hT, ?_, ?_, ?_⟩
    · rw [← hprod, ← Finset.prod_const]
      exact Finset.prod_le_prod' (fun p hp => (hpinfo p (hT hp)).2.1)
    · rw [← hprod, ← Finset.prod_const]
      exact Finset.prod_le_prod' (fun p hp => (hpinfo p (hT hp)).2.2.1)
    · rw [← hprod, ← Finset.prod_const]
      exact Finset.prod_le_prod' (fun p hp => (hpinfo p (hT hp)).2.2.2)
  refine ⟨m, hm, by rwa [hmS], ?_⟩
  intro a ha ha1 b hb hb1 k hk
  cases k with
  | zero => simpa using hk.symm
  | succ k =>
    have ⟨hi,hic,hal,hau,_⟩ := divisor_bounds a ha ha1
    have ⟨_,hjc,hbl,hbu,hbx⟩ := divisor_bounds b hb hb1
    have hbase : 0 < X := by dsimp [X]; positivity
    have hbp : b ≤ X^n :=
      hbx.trans (Nat.pow_le_pow_right hbase hjc)
    have hki : 2^(k+1) ≤ b := by
      have hle : 1 ≤ b / 2^(k+1) := by rw [hk]; omega
      simpa only [one_mul] using
        (Nat.le_div_iff_mul_le (by positivity : 0 < 2^(k+1))).mp hle
    have hx : X^n = 2^(2*J*n) := by
      dsimp [X,W]
      rw [← pow_mul, ← pow_mul, mul_comm 2 J, ← mul_assoc]
    rw [hx] at hbp
    have hkbound : k+1 ≤ 2*J*n := by
      by_contra! hl
      exact (Nat.pow_lt_pow_right (by decide : 1 < 2) hl).not_ge (hki.trans hbp)
    obtain ⟨d,hd,hdn,hdlo,hdhi⟩ :=
      prefix_window hW hP hi hic hjc hal hau hbl hbu (Nat.succ_pos k) hk
    have ⟨hrootlo,hroothi⟩ := dyadicRoot_bounds hd hdlo hdhi
    exact (hgood <| mem_badBuckets_of_root hW hq hdn hkbound hrootlo hroothi).elim

end A090335

theorem OMA.solution : type_of% @OMA.S_oeis_a090335.main := by
  classical
  intro n
  obtain ⟨m,hm⟩ := A090335.eligible_exists n
  let h : ∃ x, OMA.S_oeis_a090335.eligible n x := ⟨m, hm⟩
  exact ⟨Nat.find h, Nat.find_spec h, fun _ hx => Nat.find_min' h hx⟩


