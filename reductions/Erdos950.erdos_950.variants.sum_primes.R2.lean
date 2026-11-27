import FormalConjectures.ErdosProblems.«950»

/-! Stability of the lower bound for the reciprocal energy of ordered primes. -/

namespace OMA.R_Erdos950_erdos_950_variants_sum_primes_R2

open Filter Finset Erdos950
open scoped Topology Asymptotics Nat.Prime BigOperators

/-- Real distances to the r-th predecessor have total at most r times the span. -/
lemma sum_rank_gap (a : ℕ → ℝ) {m r : ℕ} (hr : r ≤ m) {X : ℝ}
    (ha : ∀ i < m, 0 ≤ a i ∧ a i ≤ X) :
    (∑ j ∈ range (m-r), (a (r+j) - a j)) ≤ r*X := by
  have he (k n : ℕ) := sum_range_add a k n
  have heq : (∑ j ∈ range (m-r), (a (r+j) - a j)) =
      (∑ j ∈ range r, a (m-r+j)) - ∑ j ∈ range r, a j := by
    rw [sum_sub_distrib]
    have h₁ := he r (m-r)
    have h₂ := he (m-r) r
    rw [show r+(m-r) = m by omega] at h₁
    rw [show m-r+r = m by omega] at h₂
    linarith
  rw [heq]
  have hb : (∑ j ∈ range r, a (m-r+j)) ≤ ∑ _j ∈ range r, X :=
    sum_le_sum fun j hj => (ha _ (by have := mem_range.mp hj; omega)).2
  have hl : 0 ≤ ∑ j ∈ range r, a j :=
    sum_nonneg fun j hj => (ha j (lt_of_lt_of_le (mem_range.mp hj) hr)).1
  simpa using (show (∑ j ∈ range r, a (m-r+j)) - ∑ j ∈ range r, a j ≤ ∑ _j ∈ range r, X by linarith)

/-- Split a column at its first valid endpoint. -/
lemma column_split {m r : ℕ} (hr : r ≤ m) (F : ℕ → ℝ) (z : ℝ) :
    (∑ i ∈ range m, if r ≤ i then F (i-r) else z) =
      r*z + ∑ j ∈ range (m-r), F j := by
  conv_lhs => rw [show m = r+(m-r) by omega]
  rw [sum_range_add]
  congr 1
  · rw [show (∑ i ∈ range r, if r ≤ i then F (i-r) else z) = ∑ _i ∈ range r, z by
          apply sum_congr rfl
          intro i hi
          simp [not_le.mpr (mem_range.mp hi)]]
    simp
  · simp

lemma abs_reciprocal_error (d b t : ℝ) (hd : 0 < d) (ht : 0 < t) :
    |1/d-b| ≤ t*(1/d) + (1/d-2*b+b^2*d)/(4*t) := by
  rw [abs_le]
  constructor
  · field_simp
    nlinarith [sq_nonneg (1-b*d+2*t)]
  · field_simp
    nlinarith [sq_nonneg (1-b*d-2*t)]

/-- Re-index all primes below a cutoff by their ranks, including the strict upper endpoint. -/
lemma sum_primes_by_rank (x : ℕ) (F : ℕ → ℝ) :
    (∑ p ∈ x.primesBelow, F p) = ∑ i ∈ range (π' x), F (Nat.nth Nat.Prime i) := by
  classical
  let a := Nat.nth Nat.Prime
  have ha : StrictMono a := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have heq : x.primesBelow = (range (π' x)).image a := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpx, hpr⟩ := Nat.mem_primesBelow.mp hp
      exact mem_image.mpr ⟨π' p, mem_range.mpr (Nat.count_strict_mono hpr hpx), Nat.nth_count hpr⟩
    · intro hp
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      exact Nat.mem_primesBelow.mpr ⟨Nat.nth_lt_of_lt_count (mem_range.mp hi), Nat.prime_nth_prime i⟩
  rw [heq, sum_image]
  exact fun _ _ _ _ h => ha.injective h

lemma f_by_rank (i : ℕ) :
    f (Nat.nth Nat.Prime i) = ∑ j ∈ range i,
      1/((Nat.nth Nat.Prime i : ℝ) - Nat.nth Nat.Prime (i-1-j)) := by
  rw [show f (Nat.nth Nat.Prime i) = ∑ q ∈ (Nat.nth Nat.Prime i).primesBelow,
        1/((Nat.nth Nat.Prime i : ℝ)-q) by simp only [f, Nat.primesBelow, Nat.prime_iff],
      sum_primes_by_rank, Nat.primeCounting'_nth_eq]
  exact (sum_range_reflect _ _).symm

/-- A stable lower bound for the reciprocal pair energy of an ordered set.
The harmonic contribution of missing predecessors near the left boundary sums to m*c. -/
lemma rank_stability (a : ℕ → ℝ) (m : ℕ) (X c t : ℝ) (ha : StrictMono a)
    (hab : ∀ i < m, 0 ≤ a i ∧ a i ≤ X) (hc : 0 ≤ c) (hcX : c*X = m)
    (ht : 0 < t) (F : ℕ → ℝ)
    (hF : ∀ i < m, F i = ∑ j ∈ range i, 1/(a i-a (i-1-j))) :
    let s := ∑ j ∈ range m, c/((j:ℝ)+1)
    let E := ∑ i ∈ range m, F i
    m*s-2*m*c ≤ E ∧
    (∑ i ∈ range m, |F i-s|) ≤
      t*E + (E - (m:ℝ)*s + 2*m*c)/(4*t) + m*c := by
  classical
  let b (j : ℕ) := c/((j:ℝ)+1)
  let g (i j : ℕ) := a i - a (i-(j+1))
  let u (i j : ℕ) : ℝ := if j+1 ≤ i then 1/g i j else 0
  let v (i j : ℕ) : ℝ := if j+1 ≤ i then b j else 0
  let w (i j : ℕ) : ℝ := if j+1 ≤ i then (b j)^2*g i j else 0
  let s := ∑ j ∈ range m, b j
  let E := ∑ i ∈ range m, F i
  change (m*s-2*m*c ≤ E) ∧ (∑ i ∈ range m, |F i-s|) ≤ t*E + (E-m*s+2*m*c)/(4*t)+m*c
  have row i (hi : i < m) : (∑ j ∈ range m, u i j) = F i := by
    rw [hF i hi]
    change (∑ j ∈ range m, if j+1 ≤ i then 1/g i j else 0) = _
    rw [← sum_filter]
    have hs : (range m).filter (fun j => j+1 ≤ i) = range i := by
      ext j
      simp only [mem_filter, mem_range]
      omega
    rw [hs]
    apply sum_congr rfl
    intro j _
    simp only [g, show i-(j+1) = i-1-j by omega]
  have totalU : (∑ i ∈ range m, ∑ j ∈ range m, u i j) = E :=
    sum_congr rfl fun i hi => row i (mem_range.mp hi)
  have colV j (hj : j < m) :
      (∑ i ∈ range m, v i j) = m*b j-c := by
    let r := j+1
    have h := column_split (m:=m) (r:=r) (by dsimp [r]; omega) (fun _ => b j) 0
    change (∑ i ∈ range m, if r ≤ i then b j else 0) = _
    rw [h]
    simp only [mul_zero, zero_add, sum_const, card_range, nsmul_eq_mul,
      Nat.cast_sub (show r ≤ m by dsimp [r]; omega)]
    dsimp [r,b]
    push_cast
    field_simp
  have totalV : (∑ i ∈ range m, ∑ j ∈ range m, v i j) = m*s-m*c := by
    rw [sum_comm]
    calc
      _ = ∑ j ∈ range m, (m*b j-c) := sum_congr rfl fun j hj => colV j (mem_range.mp hj)
      _ = _ := by simp [s, sum_sub_distrib, mul_sum]
  have colW j (hj : j < m) : (∑ i ∈ range m, w i j) ≤ m*b j := by
    let r := j+1
    have hr : r ≤ m := by dsimp [r]; omega
    have hw : (∑ i ∈ range m, w i j) =
        (b j)^2 * ∑ k ∈ range (m-r), (a (r+k)-a k) := by
      have h := column_split hr (fun k => (b j)^2*(a (r+k)-a k)) 0
      rw [← mul_sum] at h
      simp only [mul_zero, zero_add] at h
      refine Eq.trans (sum_congr rfl fun i _ => ?_) h
      dsimp [w,g,r]
      split_ifs with hji
      · rw [show j+1+(i-(j+1)) = i by omega]
      · rfl
    rw [hw]
    calc
      _ ≤ (b j)^2 * ((r:ℝ)*X) := mul_le_mul_of_nonneg_left (sum_rank_gap a hr hab) (sq_nonneg _)
      _ = m*b j := by
        dsimp [b,r]
        push_cast
        field_simp
        linear_combination c * hcX
  have totalW : (∑ i ∈ range m, ∑ j ∈ range m, w i j) ≤ m*s := by
    rw [sum_comm]
    dsimp [s]
    rw [mul_sum]
    exact sum_le_sum fun j hj => colW j (mem_range.mp hj)
  constructor
  · have hpos (i j : ℕ) : 0 ≤ u i j - 2*v i j + w i j := by
      dsimp only [u,v,w]
      split_ifs with hij
      · have hgap : 0 < g i j := sub_pos.mpr (ha (by omega : i-(j+1) < i))
        have hsq := sq_nonneg (1-b j*g i j)
        have h := (div_nonneg hsq hgap.le)
        field_simp [hgap.ne'] at h ⊢
        nlinarith
      · norm_num
    have hnum := sum_nonneg (s:=range m) fun i _ => sum_nonneg (s:=range m) fun j _ => hpos i j
    simp only [sum_add_distrib,sum_sub_distrib,← mul_sum] at hnum
    rw [totalU,totalV] at hnum
    linarith
  have hcell (i j : ℕ) : |u i j - b j| ≤
      t*u i j + (u i j - 2*v i j + w i j)/(4*t) + (b j - v i j) := by
    dsimp only [u,v,w]
    by_cases h : j+1 ≤ i
    · simp only [if_pos h, sub_self, add_zero]
      exact abs_reciprocal_error _ _ _ (sub_pos.mpr (ha (by omega : i-(j+1) < i))) ht
    · have hb : 0 ≤ b j := div_nonneg hc (by positivity)
      simp [h, abs_of_nonneg hb]
  have htotal := sum_le_sum (s:=range m) fun i (_ : i ∈ range m) =>
    sum_le_sum (s:=range m) fun j (_ : j ∈ range m) => hcell i j
  simp only [sum_add_distrib, sum_sub_distrib, ← sum_div, ← mul_sum,
    sum_const, nsmul_eq_mul, card_range] at htotal
  change (∑ i ∈ range m, ∑ j ∈ range m, |u i j-b j|) ≤
    t*(∑ i ∈ range m, ∑ j ∈ range m, u i j) +
    ((∑ i ∈ range m, ∑ j ∈ range m, u i j) -
    2*(∑ i ∈ range m, ∑ j ∈ range m, v i j) + ∑ i ∈ range m, ∑ j ∈ range m, w i j)/(4*t) +
    ((m:ℝ)*s - ∑ i ∈ range m, ∑ j ∈ range m, v i j) at htotal
  rw [totalU,totalV] at htotal
  calc
    _ ≤ ∑ i ∈ range m, ∑ j ∈ range m, |u i j-b j| := by
      apply sum_le_sum
      intro i hi
      rw [← row i (mem_range.mp hi)]
      dsimp [s]
      rw [← sum_sub_distrib]
      exact abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply htotal.trans
      have hnum : E-2*((m:ℝ)*s-m*c)+(∑ i ∈ range m, ∑ j ∈ range m, w i j) ≤
          E-m*s+2*m*c := by linarith
      linarith [div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ 4*t)]


/-- The ordinary prime number theorem, in strict-count form. -/
def H1 : Prop :=
  Tendsto (fun x : ℕ => (π' x : ℝ)/x * Real.log x) atTop (𝓝 1)

/-- A sharp upper estimate involving only pairs of primes. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
    (∑ p ∈ x.primesBelow, f p) ≤ (1+ε)*(π' x)

/-- A bounded third absolute moment suffices for uniform integrability of the square. -/
def H3 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
    (∑ p ∈ x.primesBelow, |f p-1|^3) ≤ C*(π' x)

lemma calibrate (h : H1) :
    Tendsto (fun x : ℕ => (π' x : ℝ)/x) atTop (𝓝 0) ∧
    Tendsto (fun x : ℕ => (π' x : ℝ)/x*(harmonic (π' x) : ℝ)) atTop (𝓝 1) := by
  let c (x : ℕ) : ℝ := (π' x : ℝ)/x
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto c atTop (𝓝 0) := by
    apply (h.div_atTop hlog).congr'
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hlogx := Real.log_pos (show 1 < (x:ℝ) by exact_mod_cast hx)
    simp [c,hlogx.ne']
  refine ⟨hc, ?_⟩
  have hclog : Tendsto (fun x => c x*Real.log (c x)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_mul_log.tendsto 0).comp hc
  have hmain : Tendsto (fun x => c x * Real.log (π' x : ℝ)) atTop (𝓝 1) := by
    apply (show Tendsto _ _ (𝓝 (1:ℝ)) from (add_zero (1:ℝ)) ▸ h.add hclog).congr'
    filter_upwards [eventually_gt_atTop 0, Nat.tendsto_primeCounting'.eventually (eventually_gt_atTop 0)]
      with x hx hm
    have hx' : (x:ℝ) ≠ 0 := by positivity
    have hm' : (π' x : ℝ) ≠ 0 := by positivity
    dsimp [c]
    rw [Real.log_div hm' hx']
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain
    (show Tendsto _ _ (𝓝 (1:ℝ)) from (zero_add (1:ℝ)) ▸ hc.add hmain)
  · filter_upwards [Nat.tendsto_primeCounting'.eventually (eventually_gt_atTop 0)] with x hx
    have hm : 0 < (π' x : ℝ) := by positivity
    have hle : Real.log (π' x : ℝ) ≤ Real.log ((π' x+1 : ℕ):ℝ) :=
      Real.log_le_log hm (by push_cast; linarith)
    exact mul_le_mul_of_nonneg_left (hle.trans (log_add_one_le_harmonic _)) (by dsimp [c]; positivity)
  · filter_upwards with x
    dsimp [c]
    simpa [mul_add] using mul_le_mul_of_nonneg_left (harmonic_le_one_add_log (π' x))
      (show 0 ≤ (π' x:ℝ)/x by positivity)

lemma prime_rank_L1 (x : ℕ) (hx : 0 < x) (t : ℝ) (ht : 0 < t) :
    let m := (π' x : ℝ)
    let c := m/x
    let s := c*(harmonic (π' x):ℝ)
    let E := ∑ p ∈ x.primesBelow, f p
    m*s-2*m*c ≤ E ∧ (∑ p ∈ x.primesBelow, |f p-s|) ≤ t*E + (E-m*s+2*m*c)/(4*t) + m*c := by
  let a (i : ℕ) : ℝ := Nat.nth Nat.Prime i
  let c := (π' x:ℝ)/x
  have ha : StrictMono a := fun i j h => by
    dsimp [a]
    exact_mod_cast Nat.nth_strictMono Nat.infinite_setOfPred_prime h
  have hb i (hi : i < π' x) : 0 ≤ a i ∧ a i ≤ (x:ℝ) := by
    refine ⟨by dsimp [a]; positivity, ?_⟩
    dsimp [a]
    exact_mod_cast (Nat.nth_lt_of_lt_count (p:=Nat.Prime) hi).le
  have hs : (∑ j ∈ range (π' x), c/((j:ℝ)+1)) = c*(harmonic (π' x):ℝ) := by
    simp [harmonic, div_eq_mul_inv, mul_sum]
  have h := rank_stability a (π' x) x c t ha hb (by dsimp [c]; positivity)
    (by dsimp [c]; field_simp) ht (fun i => f (Nat.nth Nat.Prime i)) (fun i _ => f_by_rank i)
  dsimp only at h ⊢
  rw [hs] at h
  simpa only [sum_primes_by_rank, c] using h

lemma prime_L1 (hd : H1) (he : H2) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ x.primesBelow, |f p-1|) ≤ δ*(π' x) := by
  intro δ hδ
  let t := min 1 (δ/8)
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htδ : 8*t ≤ δ := by linarith [show t ≤ δ/8 from min_le_right _ _]
  obtain ⟨hc,hs⟩ := calibrate hd
  have hsmall := Metric.tendsto_nhds.mp hs (t^2) (by positivity)
  have hsmallc := Metric.tendsto_nhds.mp hc (t^2) (by positivity)
  filter_upwards [hsmall,hsmallc,he (t^2) (by positivity),eventually_gt_atTop 0] with x hsx hcx hex hx
  let m := (π' x:ℝ)
  let c := m/x
  let s := c*(harmonic (π' x):ℝ)
  let E := ∑ p ∈ x.primesBelow, f p
  rw [Real.dist_eq] at hsx hcx
  change |s-1| < t^2 at hsx
  change |c-0| < t^2 at hcx
  change E ≤ (1+t^2)*m at hex
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hcard : (x.primesBelow.card : ℝ) = m := by rw [Nat.primesBelow_card_eq_primeCounting']
  have hc' : c ≤ t^2 := by linarith [(abs_lt.mp hcx).2]
  have hs' : 1-t^2 ≤ s := by linarith [(abs_lt.mp hsx).1]
  have ht2 : t^2 ≤ t := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht1)]
  have step := (prime_rank_L1 x hx t ht).2
  change (∑ p ∈ x.primesBelow, |f p-s|) ≤ t*E+(E-m*s+2*m*c)/(4*t)+m*c at step
  have ec : m*c ≤ t^2*m := by simpa [mul_comm] using mul_le_mul_of_nonneg_left hc' hm
  have es := mul_le_mul_of_nonneg_left hs' hm
  have enum : (E-m*s+2*m*c)/(4*t) ≤ t*m := by
    apply (div_le_iff₀ (by positivity : 0 < 4*t)).mpr
    nlinarith
  have et : t*E ≤ 2*t*m := by
    have hb : E ≤ 2*m := hex.trans (mul_le_mul_of_nonneg_right (by linarith) hm)
    linarith [mul_le_mul_of_nonneg_left hb ht.le]
  calc
    _ ≤ ∑ p ∈ x.primesBelow, (|f p-s|+|s-1|) :=
      sum_le_sum fun p _ => abs_sub_le _ _ _
    _ = (∑ p ∈ x.primesBelow, |f p-s|) + m*|s-1| := by simp [sum_add_distrib,hcard]
    _ ≤ δ*m := by
      have hms := mul_le_mul_of_nonneg_left hsx.le hm
      have hmt := mul_le_mul_of_nonneg_right ht2 hm
      have hmtδ := mul_le_mul_of_nonneg_right htδ hm
      nlinarith


/-- The lower estimate for the square mean requires only global prime density. -/
lemma prime_square_lower (hd : H1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, (1-ε)*(π' x : ℝ) ≤ ∑ p ∈ x.primesBelow, (f p)^2 := by
  obtain ⟨hc,hs⟩ := calibrate hd
  filter_upwards [Metric.tendsto_nhds.mp hc (ε/8) (by positivity),
      Metric.tendsto_nhds.mp hs (ε/8) (by positivity), eventually_gt_atTop 0] with x hcx hsx hx
  let m := (π' x:ℝ)
  let c := m/x
  let s := c*(harmonic (π' x):ℝ)
  have hm : 0 ≤ m := by positivity
  rw [Real.dist_eq] at hcx hsx
  change |c-0| < ε/8 at hcx
  change |s-1| < ε/8 at hsx
  have he := (prime_rank_L1 x hx 1 zero_lt_one).1
  change m*s-2*m*c ≤ ∑ p ∈ x.primesBelow, f p at he
  have hsq := sum_le_sum (s:=x.primesBelow) fun p (_ : p ∈ x.primesBelow) =>
    (show 2*f p - 1 ≤ (f p)^2 by nlinarith [sq_nonneg (f p-1)])
  simp only [sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one,
    Nat.primesBelow_card_eq_primeCounting'] at hsq
  change 2*(∑ p ∈ x.primesBelow, f p) - m ≤ _ at hsq
  have hcl := mul_le_mul_of_nonneg_left (show c ≤ ε/8 by linarith [(abs_lt.mp hcx).2]) hm
  have hsl := mul_le_mul_of_nonneg_left (show 1-ε/8 ≤ s by linarith [(abs_lt.mp hsx).1]) hm
  change (1-ε)*m ≤ _
  nlinarith

lemma prime_L2 (hd : H1) (he : H2) (ht : H3) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ x.primesBelow, (f p-1)^2) ≤ δ*(π x) := by
  obtain ⟨C, hC, hcube⟩ := ht
  intro δ hδ
  filter_upwards [prime_L1 hd he (δ^2/C) (by positivity), hcube] with x hx hy
  let u (p : ℕ) := |f p-1|
  let m := (π' x:ℝ)
  have hm : 0 ≤ m := by positivity
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul (r:=fun p => (f p-1)^2)
    (f:=u) (g:=fun p => (u p)^3) x.primesBelow
    (fun p _ => abs_nonneg _) (fun p _ => pow_nonneg (abs_nonneg _) _) (by
      intro p _
      change ((f p-1)^2)^2 ≤ |f p-1| * |f p-1|^3
      rw [show |f p-1| * |f p-1|^3 = (|f p-1|^2)^2 by ring, sq_abs])
  have h' : (∑ p ∈ x.primesBelow, (f p-1)^2)^2 ≤ (δ*m)^2 := by
    refine h.trans ((mul_le_mul hx hy (sum_nonneg fun p _ => pow_nonneg (abs_nonneg _) _)
      (by positivity)).trans ?_)
    change δ^2/C*m*(C*m) ≤ (δ*m)^2
    apply le_of_eq
    field_simp
  have hπ : m ≤ (π x:ℝ) := by
    dsimp [m]
    exact_mod_cast Nat.monotone_primeCounting' (Nat.le_succ x)
  apply le_trans _ (mul_le_mul_of_nonneg_left hπ hδ.le)
  exact (le_abs_self _).trans (abs_le_of_sq_le_sq h' (by positivity))

lemma count_endpoints (x : ℕ) :
    x.primesBelow.card ≤ π x ∧ π x ≤ x.primesBelow.card + 1 := by
  rw [Nat.primesBelow_card_eq_primeCounting', Nat.primeCounting, Nat.primeCounting', Nat.count_succ]
  split <;> omega

lemma moment_of_centered (hv : ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,
    (∑ p ∈ x.primesBelow, (f p-1)^2) ≤ δ * π x) :
    (fun x : ℕ => ∑ p ∈ x.primesBelow, (f p)^2) ~[atTop] (fun x => (π x : ℝ)) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let d := min 1 (ε/8)
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdε : 4*d < ε := by linarith [show d ≤ ε/8 from min_le_right _ _]
  have hpi : Tendsto (fun x : ℕ => (π x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  filter_upwards [hv (d^2) (by positivity), hpi.eventually (eventually_ge_atTop (1/d))]
    with x hvx hpx
  let P := x.primesBelow
  let y := (π x : ℝ)
  let v := ∑ p ∈ P, (f p-1)^2
  let m := ∑ p ∈ P, (f p-1)
  change 1/d ≤ y at hpx
  have hy : 0 < y := lt_of_lt_of_le (by positivity : 0 < 1/d) hpx
  have hlast : 1 ≤ d*y := by linarith [(div_le_iff₀ hd).mp hpx]
  have hc : (P.card : ℝ) ≤ y := by dsimp [P,y]; exact_mod_cast (count_endpoints x).1
  have hc' : y ≤ (P.card : ℝ) + 1 := by dsimp [P,y]; exact_mod_cast (count_endpoints x).2
  change v ≤ d^2*y at hvx
  have hv0 : 0 ≤ v := sum_nonneg (by intros; positivity)
  have hvsmall : v ≤ d*y := by
    calc
      _ ≤ d^2*y := hvx
      _ ≤ d*y := by nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd1 hd.le) hy.le]
  have hm : |m| ≤ d*y := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    calc
      _ ≤ (P.card : ℝ)*v := sq_sum_le_card_mul_sum_sq
      _ ≤ y*(d^2*y) := mul_le_mul hc hvx hv0 hy.le
      _ = _ := by ring
  have hexp : (∑ p ∈ P, (f p)^2) = v + 2*m + P.card := by
    calc
      _ = ∑ p ∈ P, ((f p-1)^2+2*(f p-1)+1) := by
        apply sum_congr rfl
        intro p _
        ring
      _ = _ := by simp only [v, m, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one]
  rw [Real.dist_eq]
  change |(∑ p ∈ P, (f p)^2)/y-1| < ε
  rw [hexp, abs_lt]
  obtain ⟨hmlo, hmhi⟩ := abs_le.mp hm
  constructor
  · apply lt_sub_iff_add_lt.mpr
    apply (lt_div_iff₀ hy).mpr
    linarith [mul_lt_mul_of_pos_right hdε hy]
  · apply sub_lt_iff_lt_add.mpr
    apply (div_lt_iff₀ hy).mpr
    linarith [mul_lt_mul_of_pos_right hdε hy]

theorem main : H1 → H2 → H3 → type_of% @Erdos950.erdos_950.variants.sum_primes := by
  intro hd he ht
  simpa only [Nat.primesBelow, Nat.prime_iff] using moment_of_centered (prime_L2 hd he ht)

end OMA.R_Erdos950_erdos_950_variants_sum_primes_R2
