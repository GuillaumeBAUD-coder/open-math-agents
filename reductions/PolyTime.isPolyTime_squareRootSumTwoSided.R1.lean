import FormalConjectures.Wikipedia.SquareRootSum

/-!
# Comparing square-root sums on one residue class

Split the signed sum into two real numbers according to a binary square-class
test. Their signs and the sign of the difference of their squares determine
the original comparison, including equality. Three such splits remove the
valuation parity and the two odd-unit distinctions at 2. Finally, each
surviving radical expands to at most two roots with radicands 1 modulo 8.
Each split produces four queries. In the squared comparisons the number of
terms is the sum of the squares of the two block lengths, so the three fixed
splits have polynomial output size.
Integer square-root enclosures answer every query outside an exponentially
narrow interval. The near-tie comparator may choose any fixed positive integer
precision exponent and must also handle equality.

Credit: @desenyon
-/

open ComplexityTheory
namespace OMA.R_PolyTime_isPolyTime_squareRootSumTwoSided_R1

/-- A comparator for near ties among radicands congruent to 1 modulo 8.
The precision exponent is fixed once for the whole algorithm. -/
def H1 : Prop :=
  let S := fun l : List ℕ => (l.map (fun n : ℕ => Real.sqrt (n : ℝ))).sum
  ∃ (d : ℕ) (f : List ℕ × List ℕ → Bool), IsPolyTime f ∧
    ∀ (a b : List ℕ), (∀ n ∈ a ++ b, n % 8 = 1) →
      |(2 : ℝ)^(((BitstringEncoding.bitEncode (a,b)).length + 1)^(d + 1)) * (S a - S b)| < 1 →
      f (a, b) = decide (S a ≤ S b)

/-- Polynomial-time list operations on binary naturals. The filters read the
parity of the number of trailing zero bits or a residue of the odd part. -/
def H2 : Prop :=
  let P := fun (f : List ℕ × List ℕ → List ℕ) => IsPolyTime f
  P Prod.fst ∧ P Prod.snd ∧
  (∀ f g, P f → P g →
    P (fun x => f x ++ g x) ∧ P (fun x => (f x).flatMap fun a => (g x).map (a * ·))) ∧
  (∀ f, P f → ∀ r : ℕ, P (fun x => (f x).map (r * ·))) ∧
  (∀ f, P f → ∀ (k : ℕ) (b : Bool), P (fun x => (f x).filter fun n =>
    (if k = 0 then decide (padicValNat 2 n % 2 = 0)
     else decide (n = 0 ∨ n.divMaxPow 2 % k = 1)) == b)) ∧
  (∀ f, P f → P (fun x => (f x).flatMap fun n =>
    if n = 0 then [] else if padicValNat 2 n = 0 then [n] else
      [n.divMaxPow 2, (2 ^ (padicValNat 2 n / 2) - 1)^2 * n.divMaxPow 2]))

/-- Pairing inputs to a comparator and combining four Boolean replies. -/
def H3 : Prop :=
  (∀ (f : List ℕ × List ℕ → Bool) (a b : List ℕ × List ℕ → List ℕ),
    IsPolyTime f → IsPolyTime a → IsPolyTime b → IsPolyTime (fun x => f (a x, b x))) ∧
  (∀ (op : Bool → Bool → Bool → Bool → Bool) (a b c d : List ℕ × List ℕ → Bool),
    IsPolyTime a → IsPolyTime b → IsPolyTime c → IsPolyTime d →
    IsPolyTime (fun x => op (a x) (b x) (c x) (d x)))

/-- Two fixed-precision tests using only integer square roots and binary arithmetic. -/
def H4 : Prop :=
  ∀ d : ℕ,
    let scale := fun x : List ℕ × List ℕ =>
      (x.1.length + x.2.length + 1) * 2^(((BitstringEncoding.bitEncode x).length + 1)^(d + 1))
    let lower (m : ℕ) (l : List ℕ) := (l.map (fun n => Nat.sqrt (m^2*n))).sum
    IsPolyTime (fun x => decide (lower (scale x) x.1 + x.1.length ≤ lower (scale x) x.2)) ∧
    IsPolyTime (fun x => decide (lower (scale x) x.1 ≤ lower (scale x) x.2 + x.2.length))

/-- The scaled integer square root encloses the exact value within one unit. -/
theorem scaled_root_bounds (m n : ℕ) :
    let k := Nat.sqrt (m^2*n)
    (k : ℝ) ≤ (m : ℝ) * Real.sqrt (n : ℝ) ∧
      (m : ℝ) * Real.sqrt (n : ℝ) ≤ (k : ℝ) + 1 := by
  intro k
  have lo : (k : ℝ)^2 ≤ ((m^2*n : ℕ) : ℝ) := by exact_mod_cast Nat.sqrt_le' (m^2*n)
  have hi : ((m^2*n : ℕ) : ℝ) < ((k : ℝ) + 1)^2 := by exact_mod_cast Nat.lt_succ_sqrt' (m^2*n)
  have hs : Real.sqrt (((m^2*n : ℕ) : ℝ)) = (m : ℝ) * Real.sqrt (n : ℝ) := by
    push_cast
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  rw [← hs]
  exact ⟨Real.le_sqrt_of_sq_le lo, Real.sqrt_le_iff.mpr ⟨by positivity, hi.le⟩⟩

private theorem scaled_sum_bounds (m : ℕ) (l : List ℕ) :
    let lo := (l.map (fun n => Nat.sqrt (m^2*n))).sum
    let s := (l.map (fun n : ℕ => Real.sqrt (n : ℝ))).sum
    (lo : ℝ) ≤ (m : ℝ)*s ∧ (m : ℝ)*s ≤ (lo : ℝ) + l.length := by
  induction l with
  | nil => simp
  | cons n l ih =>
    obtain ⟨hn₁,hn₂⟩ := scaled_root_bounds m n
    obtain ⟨hl₁,hl₂⟩ := ih
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, mul_add]
    exact ⟨by linarith, by linarith⟩

private theorem handle_far (h₁ : H1) (h₃ : H3) (h₄ : H4) :
    let S := fun l : List ℕ => (l.map (fun n : ℕ => Real.sqrt (n : ℝ))).sum
    ∃ f : List ℕ × List ℕ → Bool, IsPolyTime f ∧ ∀ a b : List ℕ,
      (∀ n ∈ a ++ b, n % 8 = 1) → f (a,b) = decide (S a ≤ S b) := by
  intro S
  obtain ⟨d, near, hnear, spec⟩ := h₁
  let K := fun x : List ℕ × List ℕ => 2^(((BitstringEncoding.bitEncode x).length+1)^(d + 1))
  let M := fun x : List ℕ × List ℕ => (x.1.length+x.2.length+1) * K x
  let lower (m : ℕ) (l : List ℕ) := (l.map (fun n => Nat.sqrt (m^2*n))).sum
  let yes := fun x : List ℕ × List ℕ => decide (lower (M x) x.1 + x.1.length ≤ lower (M x) x.2)
  let possible := fun x : List ℕ × List ℕ => decide (lower (M x) x.1 ≤ lower (M x) x.2 + x.2.length)
  obtain ⟨hyes,hpos⟩ := h₄ d
  refine ⟨fun x => yes x || (possible x && near x),
    h₃.2 (fun a b c _ => a || (b && c)) yes possible near near hyes hpos hnear hnear, ?_⟩
  intro a b hrad
  let x := (a,b)
  let A := lower (M x) a
  let B := lower (M x) b
  have mk : 0 < K x := Nat.pow_pos (by decide)
  have mm : (0:ℝ) < (M x : ℝ) := by dsimp only [M]; exact_mod_cast Nat.mul_pos (by omega) mk
  obtain ⟨la,ua⟩ : (A : ℝ) ≤ (M x : ℝ)*S a ∧ (M x : ℝ)*S a ≤ (A : ℝ)+a.length :=
    scaled_sum_bounds _ _
  obtain ⟨lb,ub⟩ : (B : ℝ) ≤ (M x : ℝ)*S b ∧ (M x : ℝ)*S b ≤ (B : ℝ)+b.length :=
    scaled_sum_bounds _ _
  change (decide (A+a.length ≤ B) || (decide (A ≤ B+b.length) && near x)) = _
  by_cases y : A + a.length ≤ B
  · have yr : (A : ℝ) + a.length ≤ B := by exact_mod_cast y
    have hs : S a ≤ S b := (mul_le_mul_iff_right₀ mm).mp (by linarith)
    simp [y, hs]
  by_cases z : A ≤ B + b.length
  · simp only [y,z,decide_false,decide_true,Bool.false_or,Bool.true_and]
    apply spec a b hrad
    have yr : (B : ℝ) < (A : ℝ)+a.length := by exact_mod_cast lt_of_not_ge y
    have zr : (A : ℝ) ≤ (B : ℝ)+b.length := by exact_mod_cast z
    let N : ℝ := (a.length : ℝ) + b.length + 1
    have hN : 0 < N := by dsimp [N]; positivity
    have hm : (M x : ℝ) = N * (K x : ℝ) := by simp [M,x,N]
    have hab : |(M x : ℝ)*(S a-S b)| < N := by
      rw [abs_lt, mul_sub]
      dsimp only [N]
      constructor <;> linarith
    rw [hm, mul_assoc, abs_mul, abs_of_pos hN] at hab
    have hsmall : |(K x : ℝ)*(S a-S b)| < 1 :=
      (mul_lt_mul_iff_right₀ hN).mp (by simpa only [mul_one] using hab)
    simpa only [K, Nat.cast_pow, Nat.cast_ofNat, x] using hsmall
  · have zr : (B : ℝ)+b.length < A := by exact_mod_cast lt_of_not_ge z
    have hs : S b < S a := (mul_lt_mul_iff_right₀ mm).mp (by linarith)
    simp [y,z,not_le.mpr hs]

private theorem sum_scale (r : ℕ) (l : List ℕ) :
    ((l.map (r * ·)).map (fun n : ℕ => Real.sqrt (n : ℝ))).sum =
      Real.sqrt (r : ℝ) * (l.map (fun n : ℕ => Real.sqrt (n : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Nat.cast_mul, Real.sqrt_mul (by positivity : (0:ℝ) ≤ r), ih, mul_add]

private theorem sum_cross (a b : List ℕ) :
    ((a.flatMap (fun n => b.map (n * ·))).map (fun n : ℕ => Real.sqrt (n : ℝ))).sum =
    (a.map (fun n : ℕ => Real.sqrt (n : ℝ))).sum * (b.map (fun n : ℕ => Real.sqrt (n : ℝ))).sum := by
  induction a with
  | nil => simp
  | cons n l ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, sum_scale,
      ih, List.map_cons, List.sum_cons, add_mul]

private theorem split_sum (t : ℕ → Bool) (l : List ℕ) :
    ((l.filter (fun n => t n == true)).map (fun n : ℕ => Real.sqrt (n : ℝ))).sum +
    ((l.filter (fun n => t n == false)).map (fun n : ℕ => Real.sqrt (n : ℝ))).sum =
    (l.map (fun n : ℕ => Real.sqrt (n : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons n l ih => cases h : t n <;> simp_all [add_left_comm, add_assoc]

private theorem sign_from_squares (g b : ℝ) :
    (if decide (g ≤ 0) then decide (b ≤ 0) || decide (b^2 ≤ g^2)
     else decide (b ≤ 0) && decide (g^2 ≤ b^2)) = decide (g + b ≤ 0) := by
  by_cases hg : g ≤ 0 <;> by_cases hb : b ≤ 0 <;> simp [hg, hb]
  all_goals first | linarith | skip
  · rw [← neg_sq g, sq_le_sq₀ (by linarith) (by linarith)]
    constructor <;> intro h <;> linarith
  · rw [← neg_sq b, sq_le_sq₀ (by linarith) (by linarith)]
    constructor <;> intro h <;> linarith

/-- Lift a comparison through one binary split. Products from the same block
are in the permitted class. Scaling the other block by the positive radical
of `r` preserves its sign and puts its terms in that class as well. -/
private theorem lift_class (P : ℕ → Prop) (t : ℕ → Bool) (r : ℕ) (hr : 0 < r)
    (h₂ : H2) (h₃ : H3)
    (ht : ∀ (f : List ℕ × List ℕ → List ℕ), IsPolyTime f → ∀ b : Bool,
      IsPolyTime (fun x => (f x).filter (fun n => t n == b)))
    (hmul : ∀ a b, P a → P b → t a = t b → P (a*b) ∧ t (a*b) = true)
    (hscale : ∀ b, P b → t b = false → P (r*b) ∧ t (r*b) = true) :
    let S := fun l : List ℕ => (l.map (fun n : ℕ => Real.sqrt (n : ℝ))).sum
    let solves := fun Q : ℕ → Prop => ∃ f : List ℕ × List ℕ → Bool, IsPolyTime f ∧
      ∀ a b : List ℕ, (∀ n ∈ a ++ b, Q n) → f (a,b) = decide (S a ≤ S b)
    solves (fun n => P n ∧ t n = true) → solves P := by
  intro S solves ⟨oracle, hOracle, spec⟩
  obtain ⟨hFst, hSnd, hOps, hMap, _⟩ := h₂
  let L := List ℕ × List ℕ → List ℕ
  let g : L := fun x => x.1.filter (fun n => t n == true)
  let h : L := fun x => x.2.filter (fun n => t n == true)
  let b : L := fun x => x.1.filter (fun n => t n == false)
  let c : L := fun x => x.2.filter (fun n => t n == false)
  let cross (l m : L) : L := fun x => (l x).flatMap (fun n => (m x).map (n * ·))
  let plus (l m : L) : L := fun x => l x ++ m x
  -- (G₁-G₂)² - (B₁-B₂)², with negative terms moved to the other list.
  let side (i j k l : L) : L := plus (plus (cross i i) (cross j j)) (plus (cross k l) (cross k l))
  let u := side g h b c
  let v := side b c g h
  let ask (l m : L) := fun x => oracle (l x, m x)
  let scaled (l : L) : L := fun x => (l x).map (r * ·)
  let A := ask g h
  let B := ask (scaled b) (scaled c)
  let C := ask v u
  let D := ask u v
  have hg := ht _ hFst true
  have hh := ht _ hSnd true
  have hb := ht _ hFst false
  have hc := ht _ hSnd false
  have hSide (i j k l : L) (hi : IsPolyTime i) (hj : IsPolyTime j)
      (hk : IsPolyTime k) (hl : IsPolyTime l) : IsPolyTime (side i j k l) := by
    apply (hOps _ _ _ _).1
    · exact (hOps _ _ (hOps i i hi hi).2 (hOps j j hj hj).2).1
    · exact (hOps _ _ (hOps k l hk hl).2 (hOps k l hk hl).2).1
  have hu := hSide _ _ _ _ hg hh hb hc
  have hv := hSide _ _ _ _ hb hc hg hh
  refine ⟨fun x => if A x then B x || C x else B x && D x,
    h₃.2 (fun a b c d => if a then b || c else b && d) _ _ _ _ (h₃.1 _ _ _ hOracle hg hh)
      (h₃.1 _ _ _ hOracle (hMap _ hb r) (hMap _ hc r))
      (h₃.1 _ _ _ hOracle hv hu) (h₃.1 _ _ _ hOracle hu hv), ?_⟩
  intro left right hp
  let x := (left, right)
  let Good := fun n => P n ∧ t n = true
  let tagged := fun (q : Bool) (l : List ℕ) => ∀ n ∈ l, P n ∧ t n = q
  have filtered (l : List ℕ) (hl : ∀ n ∈ l, P n) (q : Bool) :
      tagged q (l.filter (fun n => t n == q)) := by
    intro n hn
    obtain ⟨hmem, htag⟩ := List.mem_filter.mp hn
    exact ⟨hl n hmem, by simpa using htag⟩
  have hleft : ∀ n ∈ left, P n := fun n hn => hp n (List.mem_append_left _ hn)
  have hright : ∀ n ∈ right, P n := fun n hn => hp n (List.mem_append_right _ hn)
  have tg : tagged true (g x) := filtered _ hleft _
  have th : tagged true (h x) := filtered _ hright _
  have tb : tagged false (b x) := filtered _ hleft _
  have tc : tagged false (c x) := filtered _ hright _
  have scaleGood (l : L) (hl : tagged false (l x)) : ∀ n ∈ scaled l x, Good n := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
    exact hscale _ (hl _ ha).1 (hl _ ha).2
  have crossGood (q : Bool) (l m : L) (hl : tagged q (l x)) (hm : tagged q (m x)) :
      ∀ n ∈ cross l m x, Good n := by
    intro n hn
    obtain ⟨a, ha, hmem⟩ := List.mem_flatMap.mp hn
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hmem
    exact hmul _ _ (hl _ ha).1 (hm _ hb').1 ((hl _ ha).2.trans (hm _ hb').2.symm)
  have sideGood (q s : Bool) (i j k l : L) (hi : tagged q (i x)) (hj : tagged q (j x))
      (hk : tagged s (k x)) (hl : tagged s (l x)) : ∀ n ∈ side i j k l x, Good n := by
    simpa only [side, plus, List.forall_mem_append]
      using And.intro (And.intro (crossGood _ _ _ hi hi) (crossGood _ _ _ hj hj))
        (And.intro (crossGood _ _ _ hk hl) (crossGood _ _ _ hk hl))
  have tu := sideGood _ _ _ _ _ _ tg th tb tc
  have tv := sideGood _ _ _ _ _ _ tb tc tg th
  have query (l m : L) (hl : ∀ n ∈ l x, Good n) (hm : ∀ n ∈ m x, Good n) :
      ask l m x = decide (S (l x) ≤ S (m x)) := by
    apply spec
    simpa only [List.forall_mem_append] using And.intro hl hm
  have evalSide (i j k l : L) :
      S (side i j k l x) = S (i x)^2 + S (j x)^2 + 2*S (k x)*S (l x) := by
    simp only [S, side, plus, cross, List.map_append, List.sum_append, sum_cross]
    ring
  let G := S (g x) - S (h x)
  let J := S (b x) - S (c x)
  have qa : A x = decide (G ≤ 0) := by rw [show A x = _ from query g h tg th]; simp [G]
  have qb : B x = decide (J ≤ 0) := by
    rw [show B x = _ from query _ _ (scaleGood _ tb) (scaleGood _ tc)]
    simp only [scaled, S, sum_scale, mul_le_mul_iff_right₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hr)), J, sub_nonpos]
  have qsq : S (u x) - S (v x) = G^2 - J^2 := by
    dsimp only [u, v, G, J]
    rw [evalSide, evalSide]
    ring
  have qc : C x = decide (J^2 ≤ G^2) := by
    rw [show C x = _ from query v u tv tu]
    congr 1
    apply propext
    constructor <;> intro h' <;> linarith only [qsq, h']
  have qd : D x = decide (G^2 ≤ J^2) := by
    rw [show D x = _ from query u v tu tv]
    congr 1
    apply propext
    constructor <;> intro h' <;> linarith only [qsq, h']
  change (if A x then B x || C x else B x && D x) = _
  rw [qa, qb, qc, qd, sign_from_squares]
  congr 1
  apply propext
  have hL : S (g x) + S (b x) = S left := split_sum t left
  have hR : S (h x) + S (c x) = S right := split_sum t right
  dsimp only [G, J]
  constructor <;> intro h' <;> linarith only [hL, hR, h']

private theorem oddPart_mul (a b : ℕ) :
    (a*b).divMaxPow 2 = a.divMaxPow 2 * b.divMaxPow 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) (padicValNat 2 (a*b)))
  rw [Nat.pow_padicValNat_mul_divMaxPow, padicValNat.mul ha hb, pow_add]
  calc
    a*b = (2 ^ padicValNat 2 a * a.divMaxPow 2) *
        (2 ^ padicValNat 2 b * b.divMaxPow 2) := by
      rw [Nat.pow_padicValNat_mul_divMaxPow, Nat.pow_padicValNat_mul_divMaxPow]
    _ = _ := by ring

private theorem parity_product (a b : ℕ)
    (h : (padicValNat 2 a % 2 = 0) ↔ (padicValNat 2 b % 2 = 0)) :
    padicValNat 2 (a*b) % 2 = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  rw [padicValNat.mul ha hb]
  omega

private theorem unit_product_four (a b : ℕ)
    (h : (a = 0 ∨ a.divMaxPow 2 % 4 = 1) ↔ (b = 0 ∨ b.divMaxPow 2 % 4 = 1)) :
    a*b = 0 ∨ (a*b).divMaxPow 2 % 4 = 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  simp only [ha, hb, false_or] at h
  have oa := Nat.not_dvd_divMaxPow (by decide : 1 < 2) ha
  have ob := Nat.not_dvd_divMaxPow (by decide : 1 < 2) hb
  right
  rw [oddPart_mul, Nat.mul_mod]
  rcases (show a.divMaxPow 2 % 4 = 1 ∨ a.divMaxPow 2 % 4 = 3 by omega) with h1 | h3
  · rw [h1, h.mp h1]
  · have hb3 : b.divMaxPow 2 % 4 = 3 := by omega
    rw [h3, hb3]

private theorem unit_product_eight (a b : ℕ)
    (ha4 : a = 0 ∨ a.divMaxPow 2 % 4 = 1) (hb4 : b = 0 ∨ b.divMaxPow 2 % 4 = 1)
    (h : (a = 0 ∨ a.divMaxPow 2 % 8 = 1) ↔ (b = 0 ∨ b.divMaxPow 2 % 8 = 1)) :
    a*b = 0 ∨ (a*b).divMaxPow 2 % 8 = 1 := by
  rcases ha4 with rfl | ha4
  · simp
  rcases hb4 with rfl | hb4
  · simp
  have ha : a ≠ 0 := by rintro rfl; simp at ha4
  have hb : b ≠ 0 := by rintro rfl; simp at hb4
  simp only [ha, hb, false_or] at h
  right
  rw [oddPart_mul, Nat.mul_mod]
  rcases (show a.divMaxPow 2 % 8 = 1 ∨ a.divMaxPow 2 % 8 = 5 by omega) with h1 | h5
  · rw [h1, h.mp h1]
  · have hb5 : b.divMaxPow 2 % 8 = 5 := by omega
    rw [h5, hb5]

/-- Remove powers of four without listing exponentially many copies of a radical.
For a nonzero even exponent, both coefficients 1 and 2^(v/2)-1 are odd. -/
private theorem expand_one (n : ℕ) (h : n = 0 ∨
    (padicValNat 2 n % 2 = 0 ∧ n.divMaxPow 2 % 8 = 1)) :
    let v := padicValNat 2 n
    let u := n.divMaxPow 2
    let terms := if n = 0 then [] else if v = 0 then [n] else [u, (2^(v/2)-1)^2*u]
    (∀ a ∈ terms, a % 8 = 1) ∧
      (terms.map (fun a : ℕ => Real.sqrt (a : ℝ))).sum = Real.sqrt (n : ℝ) := by
  intro v u terms
  rcases eq_or_ne n 0 with rfl | hn
  · simp [terms]
  obtain ⟨hv, hu⟩ := h.resolve_left hn
  change v % 2 = 0 at hv
  change u % 8 = 1 at hu
  have fac : 2^v*u = n := Nat.pow_padicValNat_mul_divMaxPow 2 n
  by_cases hv0 : v = 0
  · have hun : u = n := by simpa [hv0] using fac
    have hn8 : n % 8 = 1 := hun ▸ hu
    simp [terms, hn, hv0, hn8]
  let m : ℕ := 2^(v/2)
  have hm : 0 < m := pow_pos (by decide) _
  have hv2 : v/2 = v/2-1+1 := by omega
  have hme : Even m := by
    dsimp [m]
    conv => arg 1; arg 2; rw [hv2]
    rw [pow_succ]
    exact even_two.mul_left _
  have hm8 : (m-1)^2 % 8 = 1 := by
    obtain ⟨k, hk⟩ := hme
    have odd : (m-1)%2 = 1 := by omega
    rw [sq, Nat.mul_mod]
    have choices : (m-1)%8 = 1 ∨ (m-1)%8 = 3 ∨ (m-1)%8 = 5 ∨ (m-1)%8 = 7 := by omega
    rcases choices with z | z | z | z <;> rw [z]
  have hres : ((m-1)^2*u)%8 = 1 := by rw [Nat.mul_mod, hm8, hu]
  have hpow : m^2*u = n := by
    dsimp [m]
    rw [← pow_mul, show v/2*2 = v by omega]
    exact fac
  have sqrt_mul_sq (d : ℕ) : Real.sqrt (((d^2*u : ℕ) : ℝ)) =
      (d : ℝ) * Real.sqrt (u : ℝ) := by
    push_cast
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  change (∀ a ∈ (if n = 0 then [] else if v = 0 then [n] else [u,(m-1)^2*u]), a % 8 = 1) ∧ _
  constructor
  · simp [hn, hv0, hu, hres]
  · simp only [terms, hn, hv0, if_false, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    change Real.sqrt (u : ℝ) + Real.sqrt ((((m-1)^2*u : ℕ) : ℝ)) = _
    rw [sqrt_mul_sq, ← hpow, sqrt_mul_sq, Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    ring

theorem main : H1 → H2 → H3 → H4 → type_of% @PolyTime.isPolyTime_squareRootSumTwoSided := by
  intro h₁ h₂ h₃ h₄
  let S := fun l : List ℕ => (l.map (fun n : ℕ => Real.sqrt (n : ℝ))).sum
  let solves := fun P : ℕ → Prop => ∃ f : List ℕ × List ℕ → Bool, IsPolyTime f ∧
    ∀ a b : List ℕ, (∀ n ∈ a ++ b, P n) → f (a,b) = decide (S a ≤ S b)
  let t (k n : ℕ) := if k = 0 then decide (padicValNat 2 n % 2 = 0)
                       else decide (n = 0 ∨ n.divMaxPow 2 % k = 1)
  let P₀ := fun _ : ℕ => True
  let P₁ := fun n => P₀ n ∧ t 0 n = true
  let P₂ := fun n => P₁ n ∧ t 4 n = true
  let P₃ := fun n => P₂ n ∧ t 8 n = true
  let closed := fun P : ℕ → Prop => ∀ a b, P a → P b → P (a*b)
  let same := fun (P : ℕ → Prop) (k : ℕ) =>
    ∀ a b, P a → P b → t k a = t k b → t k (a*b) = true
  have e₀ : same P₀ 0 := by
    intro a b _ _ he
    simpa [t] using parity_product a b (by simpa [t] using he)
  have e₁ : same P₁ 4 := by
    intro a b _ _ he
    simpa [t] using unit_product_four a b (decide_eq_decide.mp he)
  have e₂ : same P₂ 8 := by
    intro a b ha hb he
    simpa [t] using unit_product_eight a b (by simpa [t] using ha.2)
      (by simpa [t] using hb.2) (decide_eq_decide.mp he)
  have closure (P : ℕ → Prop) (k : ℕ) (hp : closed P) (hk : same P k) :
      closed (fun n => P n ∧ t k n = true) :=
    fun a b ha hb => ⟨hp a b ha.1 hb.1, hk a b ha.1 hb.1 (ha.2.trans hb.2.symm)⟩
  have c₀ : closed P₀ := fun _ _ _ _ => trivial
  have c₁ : closed P₁ := closure _ _ c₀ e₀
  have c₂ : closed P₂ := closure _ _ c₁ e₁
  obtain ⟨projLeft, projRight, _, _, filterTime, expandTime⟩ := (show H2 from h₂)
  have lift (P : ℕ → Prop) (k r : ℕ) (hr : 0 < r) (pr : P r) (tr : t k r = false)
      (hp : closed P) (hk : same P k) :
      solves (fun n => P n ∧ t k n = true) → solves P :=
    lift_class P (t k) r hr h₂ h₃ (fun f hf b => filterTime f hf k b)
      (fun a b ha hb he => ⟨hp a b ha hb, hk a b ha hb he⟩)
      (fun b hb he => ⟨hp r b pr hb, hk r b pr hb (tr.trans he.symm)⟩)
  have restricted : solves P₃ := by
    obtain ⟨f, hf, hspec⟩ := handle_far h₁ h₃ h₄
    let terms (n : ℕ) : List ℕ :=
      if n = 0 then [] else if padicValNat 2 n = 0 then [n] else
        [n.divMaxPow 2, (2^(padicValNat 2 n / 2)-1)^2*n.divMaxPow 2]
    have one (n : ℕ) (h : P₃ n) : (∀ a ∈ terms n, a % 8 = 1) ∧
        S (terms n) = Real.sqrt (n : ℝ) := by
      apply expand_one
      have hv : padicValNat 2 n % 2 = 0 := by simpa [t] using h.1.1.2
      have hu : n = 0 ∨ n.divMaxPow 2 % 8 = 1 := by simpa [t] using h.2
      tauto
    have expand (l : List ℕ) (hl : ∀ n ∈ l, P₃ n) :
        (∀ n ∈ l.flatMap terms, n % 8 = 1) ∧ S (l.flatMap terms) = S l := by
      induction l with
      | nil => simp [S]
      | cons a l ih =>
        obtain ⟨ha, hl⟩ := List.forall_mem_cons.mp hl
        obtain ⟨ra, sa⟩ := one a ha
        obtain ⟨rl, sl⟩ := ih hl
        constructor
        · simpa only [List.flatMap_cons, List.forall_mem_append] using And.intro ra rl
        · change (List.map _ ((terms a) ++ l.flatMap terms)).sum = _
          rw [List.map_append, List.sum_append]
          change S (terms a) + S (l.flatMap terms) = _
          rw [sa, sl]
          rfl
    refine ⟨fun x => f (x.1.flatMap terms, x.2.flatMap terms),
      h₃.1 _ _ _ hf (expandTime _ projLeft) (expandTime _ projRight), ?_⟩
    intro a b h
    obtain ⟨ra,sa⟩ := expand a (fun n hn => h n (List.mem_append_left _ hn))
    obtain ⟨rb,sb⟩ := expand b (fun n hn => h n (List.mem_append_right _ hn))
    change f (a.flatMap terms, b.flatMap terms) = _
    rw [hspec (a.flatMap terms) (b.flatMap terms) (by simpa only [List.forall_mem_append] using And.intro ra rb)]
    change decide (S (a.flatMap terms) ≤ S (b.flatMap terms)) = _
    rw [sa, sb]
  have m5 := Nat.maxPowDvdDiv_of_not_dvd (by decide : ¬2 ∣ 5)
  have m3 := Nat.maxPowDvdDiv_of_not_dvd (by decide : ¬2 ∣ 3)
  have sol₂ : solves P₂ := lift P₂ 8 5 (by decide)
    (by simp only [P₂, P₁, P₀, t, padicValNat, Nat.divMaxPow, m5]; decide)
    (by simp only [t, Nat.divMaxPow, m5]; decide) c₂ e₂ restricted
  have sol₁ : solves P₁ := lift P₁ 4 3 (by decide)
    (by simp only [P₁, P₀, t, padicValNat, m3]; decide)
    (by simp only [t, Nat.divMaxPow, m3]; decide) c₁ e₁ sol₂
  obtain ⟨f, hf, hspec⟩ := lift P₀ 0 2 (by decide) trivial
    (by norm_num [t, padicValNat_base (by decide : 1 < 2)]) c₀ e₀ sol₁
  have eqTarget : f = Function.uncurry PolyTime.squareRootSumTwoSided := by
    funext ⟨a,b⟩
    rw [hspec a b (fun _ _ => trivial)]
    simp only [Function.uncurry_apply_pair, PolyTime.squareRootSumTwoSided, S, List.bind_eq_flatMap,
      pure, ← List.map_eq_flatMap, List.map_map, Function.comp_def]
  exact eqTarget ▸ hf

end OMA.R_PolyTime_isPolyTime_squareRootSumTwoSided_R1
