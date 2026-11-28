import OMAStatements.S_oeis_a000531


open Finset
open scoped BigOperators

namespace A000531Geometry

def score {m : ℕ} (s a : Fin m → ℝ) : ℝ := ∑ i, s i * a i

def suffix {m : ℕ} (s : Fin m → ℝ) (k : ℕ) : ℝ :=
  ∑ i, if k ≤ i.val then s i else 0

private lemma suffix_tail {m : ℕ} (s : Fin (m + 1) → ℝ) (k : ℕ) :
    suffix (fun i : Fin m => s i.succ) k = suffix s (k + 1) := by
  unfold suffix
  rw [Fin.sum_univ_succ]
  simp

private lemma score_le {m : ℕ} (s a : Fin m → ℝ) (C T : ℝ)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (ha : Monotone a)
    (hab : ∀ i, 0 ≤ a i ∧ a i ≤ C) (hs : ∀ k, suffix s k ≤ T) :
    score s a ≤ C * T := by
  induction m generalizing C with
  | zero => simpa [score] using mul_nonneg hC hT
  | succ m ih =>
    let b (i : Fin m) := a i.succ - a 0
    have hb (i : Fin m) : 0 ≤ b i ∧ b i ≤ C - a 0 := by
      constructor
      · exact sub_nonneg.mpr (ha (Fin.zero_le _))
      · exact sub_le_sub_right (hab i.succ).2 _
    have hmono : Monotone b := fun _ _ h => sub_le_sub_right (ha (Fin.succ_le_succ_iff.mpr h)) _
    have htail := ih (fun i : Fin m => s i.succ) b (C - a 0)
      (sub_nonneg.mpr (hab 0).2) hmono hb (fun k => (suffix_tail s k).symm ▸ hs (k + 1))
    have hsplit : score s a = a 0 * suffix s 0 +
        score (fun i : Fin m => s i.succ) b := by
      simp only [score, suffix, Nat.zero_le, if_true, Fin.sum_univ_succ, b,
        mul_sub, sum_sub_distrib, ← sum_mul, mul_add]
      ring
    rw [hsplit]
    calc
      _ ≤ a 0 * T + (C - a 0) * T := add_le_add
        (mul_le_mul_of_nonneg_left (hs 0) (hab 0).1) htail
      _ = C * T := by ring

private lemma bound_of_attains {m : ℕ} (s a : Fin m → ℝ) (T : ℝ)
    (hT : 0 < T) (ha : StrictMono a) (hab : ∀ i, 0 < a i ∧ a i < 1)
    (he : score s a = T) : ∃ k, T < suffix s k := by
  by_contra! hs
  cases m with
  | zero => simp [score] at he; linarith
  | succ m =>
    have hC := hab (Fin.last m)
    have hb (i : Fin (m + 1)) : 0 ≤ a i ∧ a i ≤ a (Fin.last m) :=
      ⟨(hab i).1.le, ha.monotone (Fin.le_last i)⟩
    have h := score_le s a (a (Fin.last m)) T hC.1.le hT.le ha.monotone hb hs
    rw [he] at h
    nlinarith [mul_pos (sub_pos.mpr hC.2) hT]

private lemma attainable {m : ℕ} (s : Fin m → ℝ) (k : ℕ) (T : ℝ) (hT : 0 < T)
    (hk : T < suffix s k) :
    ∃ a : Fin m → ℝ, StrictMono a ∧ (∀ i, 0 < a i ∧ a i < 1) ∧ score s a = T := by
  let b (i : Fin m) : ℝ := (i.val + 1) / (m + 1)
  let v (i : Fin m) : ℝ := if k ≤ i.val then 1 else 0
  let B := score s b
  let M := suffix s k
  have hb (i : Fin m) : 0 < b i ∧ b i < 1 := by
    unfold b
    have hi : (i.val : ℝ) < m := by exact_mod_cast i.isLt
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]
      linarith
  have hbm : StrictMono b := by
    intro i j hij
    have h : (i.val : ℝ) < j.val := by exact_mod_cast hij
    apply div_lt_div_of_pos_right (by linarith) (by positivity)
  have hvm : Monotone v := by
    intro i j hij
    by_cases hi : k ≤ i.val
    · have hj : k ≤ j.val := hi.trans hij
      simp [v, hi, hj]
    · simp only [v, hi, if_false]
      split <;> norm_num
  have hv (i : Fin m) : 0 ≤ v i ∧ v i ≤ 1 := by unfold v; split <;> norm_num
  have hM : score s v = M := by
    unfold M score suffix
    apply sum_congr rfl
    intro i _
    by_cases hi : k ≤ i.val <;> simp [v, hi]
  have hopen : IsOpen {d : ℝ | d < 1 ∧ d * B < T ∧ T < d * B + (1 - d) * M} := by
    exact (isOpen_lt continuous_id continuous_const).inter
      ((isOpen_lt (continuous_id.mul continuous_const) continuous_const).inter
       (isOpen_lt continuous_const ((continuous_id.mul continuous_const).add
          ((continuous_const.sub continuous_id).mul continuous_const))))
  have hin : (0 : ℝ) ∈ {d : ℝ | d < 1 ∧ d * B < T ∧ T < d * B + (1 - d) * M} := by
    simp [M, hT, hk]
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp hopen 0 hin
  let d := r / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdb : d ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hd]
    dsimp [d]
    linarith
  obtain ⟨hd1, hlow, hhigh⟩ := hrball hdb
  have hMp : 0 < M := lt_trans hT hk
  let e := (T - d * B) / M
  have he : 0 < e := div_pos (sub_pos.mpr hlow) hMp
  have he1 : e < 1 - d := by
    unfold e
    rw [div_lt_iff₀ hMp]
    linarith
  let a (i : Fin m) := d * b i + e * v i
  refine ⟨a, ?_, ?_, ?_⟩
  · intro i j hij
    exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hbm hij) hd)
      (mul_le_mul_of_nonneg_left (hvm hij.le) he.le)
  · intro i
    refine ⟨add_pos_of_pos_of_nonneg (mul_pos hd (hb i).1) (mul_nonneg he.le (hv i).1), ?_⟩
    have h1 := mul_lt_mul_of_pos_left (hb i).2 hd
    have h2 := mul_le_mul_of_nonneg_left (hv i).2 he.le
    dsimp only [a]
    linarith
  · have hscore : score s a = d * B + e * M := by
      unfold score a B
      rw [← hM]
      unfold score
      simp only [mul_add, sum_add_distrib, mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intro i _ <;> ring
    rw [hscore]
    dsimp only [e]
    rw [div_mul_cancel₀ _ hMp.ne']
    ring

def realSigns (n : ℕ) (s : Fin (2 * n) → Bool) (i : Fin (2 * n)) : ℝ :=
  if s i then 1 else -1

theorem attains_iff_suffix (n : ℕ) (s : Fin (2 * n) → Bool) (j : Fin n) :
    OMA.S_oeis_a000531.AttainsOddSum n s j ↔
      ∃ k, 2 * (j.val : ℝ) + 1 < suffix (realSigns n s) k := by
  have ht : 0 < 2 * (j.val : ℝ) + 1 := by positivity
  have hrewrite (a : Fin (2 * n) → ℝ) :
      score (realSigns n s) a = ∑ i, if s i then a i else -a i := by
    apply sum_congr rfl
    intro i _
    by_cases h : s i <;> simp [realSigns, h]
  constructor
  · rintro ⟨a, ha, hb, he⟩
    exact bound_of_attains _ a _ ht ha hb ((hrewrite a).trans he)
  · rintro ⟨k, hk⟩
    obtain ⟨a, ha, hb, he⟩ := attainable _ k _ ht hk
    exact ⟨a, ha, hb, (hrewrite a).symm.trans he⟩

end A000531Geometry


open Finset
open scoped BigOperators

namespace A000531Walk

def step (b : Bool) : ℤ := if b then 1 else -1

def endpoint {m : ℕ} (s : Fin m → Bool) : ℤ := ∑ i, step (s i)

def peak : (m : ℕ) → (Fin m → Bool) → ℤ
  | 0, _ => 0
  | m+1, s => max 0 (step (s (Fin.last m)) + peak m (fun i => s i.castSucc))

private lemma sum_snoc {m : ℕ} (f : (Fin (m + 1) → Bool) → ℕ) :
    ∑ s, f s = (∑ s : Fin m → Bool, f (Fin.snoc s false)) +
      (∑ s : Fin m → Bool, f (Fin.snoc s true)) := by
  let e : Bool × (Fin m → Bool) ≃ (Fin (m + 1) → Bool) := Fin.snocEquiv (fun _ => Bool)
  calc
    ∑ s, f s = ∑ p, f (e p) := (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.sum_prod_type, Fintype.sum_bool, add_comm]; rfl

private lemma endpoint_snoc {m : ℕ} (b : Bool) (s : Fin m → Bool) :
    endpoint (Fin.snoc s b) = step b + endpoint s := by
  unfold endpoint
  rw [Fin.sum_univ_castSucc]
  simp [add_comm]

private lemma endpoint_compl {m : ℕ} (s : Fin m → Bool) :
    endpoint (fun i => !(s i)) = -endpoint s := by
  unfold endpoint
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i _
  cases h : s i <;> simp [step, h]

def hits (m : ℕ) (k : ℤ) : ℕ :=
  ∑ s : Fin m → Bool, if k ≤ peak m s then 1 else 0

def above (m : ℕ) (k : ℤ) : ℕ :=
  ∑ s : Fin m → Bool, if k ≤ endpoint s then 1 else 0

private lemma above_succ (m : ℕ) (k : ℤ) :
    above (m+1) k = above m (k+1) + above m (k-1) := by
  unfold above
  rw [sum_snoc]
  congr 1 <;> apply sum_congr rfl <;> intro s _ <;>
    rw [endpoint_snoc] <;> simp only [step, Bool.false_eq_true, if_false, if_true] <;>
    split_ifs <;> first | rfl | omega

private lemma hits_succ (m : ℕ) (k : ℤ) (hk : 0 < k) :
    hits (m+1) k = hits m (k+1) + hits m (k-1) := by
  unfold hits
  rw [sum_snoc]
  have hp (b : Bool) (s : Fin m → Bool) :
      peak (m + 1) (Fin.snoc s b) = max 0 (step b + peak m s) := by
    simp only [peak, Fin.snoc_last, Fin.snoc_castSucc]
  congr 1 <;> apply sum_congr rfl <;> intro s _ <;>
    rw [hp] <;> simp only [le_max_iff, hk.not_ge, false_or,
      step, Bool.false_eq_true, if_false, if_true] <;>
    split_ifs <;> first | rfl | omega

private lemma above_zero_total (m : ℕ) : above m 0 + above m 1 = 2 ^ m := by
  unfold above
  let e : (Fin m → Bool) ≃ (Fin m → Bool) :=
    { toFun := fun s i => !(s i)
      invFun := fun s i => !(s i)
      left_inv := by intro s; funext i; simp
      right_inv := by intro s; funext i; simp }
  have h :
      (∑ s : Fin m → Bool, if (1 : ℤ) ≤ endpoint s then 1 else 0) =
        ∑ s : Fin m → Bool, if (1 : ℤ) ≤ -endpoint s then 1 else 0 := by
    apply Fintype.sum_equiv e
    intro s
    change (if (1 : ℤ) ≤ endpoint s then 1 else 0) =
      if (1 : ℤ) ≤ -endpoint (fun i => !(s i)) then 1 else 0
    rw [endpoint_compl, neg_neg]
  rw [h, ← sum_add_distrib]
  calc
    _ = ∑ _ : Fin m → Bool, (1 : ℕ) := by
      apply sum_congr rfl
      intro s _
      by_cases hs : 0 ≤ endpoint s
      · simp [hs, show ¬ 1 ≤ -endpoint s by omega]
      · simp [hs, show 1 ≤ -endpoint s by omega]
    _ = _ := by simp

private lemma hits_zero_total (m : ℕ) : hits m 0 = 2 ^ m := by
  unfold hits
  cases m
  · simp [peak]
  · simp [peak]

theorem hits_eq_above (m : ℕ) (k : ℤ) (hk : 0 ≤ k) :
    hits m k = above m k + above m (k + 1) := by
  induction m generalizing k with
  | zero =>
    by_cases h : k = 0
    · subst k
      rw [hits_zero_total, zero_add, above_zero_total]
    · have hp : 0 < k := lt_of_le_of_ne hk (Ne.symm h)
      simp [hits, peak, above, endpoint, hp.not_ge, show ¬ k + 1 ≤ 0 by omega]
  | succ m ih =>
    by_cases h : k = 0
    · subst k
      rw [hits_zero_total, zero_add, above_zero_total]
    · have hp : 0 < k := lt_of_le_of_ne hk (Ne.symm h)
      rw [hits_succ _ _ hp, above_succ, above_succ, ih (k+1) (by omega), ih (k-1) (by omega)]
      ring_nf

def suffixZ {m : ℕ} (s : Fin m → Bool) (k : ℕ) : ℤ :=
  ∑ i, if k ≤ i.val then step (s i) else 0

private lemma suffixZ_empty {m : ℕ} (s : Fin m → Bool) (k : ℕ) (hk : m ≤ k) :
    suffixZ s k = 0 := by
  unfold suffixZ
  apply sum_eq_zero
  intro i _
  have hi : ¬ k ≤ i.val := by omega
  simp [hi]

private lemma suffixZ_extend {m : ℕ} (s : Fin (m + 1) → Bool) (k : ℕ) (hk : k ≤ m) :
    suffixZ s k = suffixZ (fun i : Fin m => s i.castSucc) k + step (s (Fin.last m)) := by
  unfold suffixZ
  rw [Fin.sum_univ_castSucc]
  simp [hk]

theorem peak_iff_suffix {m : ℕ} (s : Fin m → Bool) (t : ℤ) :
    t ≤ peak m s ↔ ∃ k ≤ m, t ≤ suffixZ s k := by
  induction m generalizing t with
  | zero => simp [peak, suffixZ]
  | succ m ih =>
    rw [peak, le_max_iff]
    constructor
    · rintro (h | h)
      · exact ⟨m + 1, le_rfl, by simpa [suffixZ_empty s (m + 1) le_rfl] using h⟩
      · have h' : t - step (s (Fin.last m)) ≤ peak m (fun i => s i.castSucc) := by omega
        obtain ⟨k, hk, ht⟩ := (ih _ _).mp h'
        exact ⟨k, by omega, by rw [suffixZ_extend _ _ hk]; omega⟩
    · rintro ⟨k, hk, ht⟩
      by_cases h : k = m + 1
      · subst k
        exact Or.inl (by simpa [suffixZ_empty s (m + 1) le_rfl] using ht)
      · have hkm : k ≤ m := by omega
        rw [suffixZ_extend _ _ hkm] at ht
        have h' := (ih (fun i => s i.castSucc) (t - step (s (Fin.last m)))).mpr ⟨k, hkm, by omega⟩
        exact Or.inr (by omega)

def heads {m : ℕ} (s : Fin m → Bool) : ℕ := ∑ i, if s i then 1 else 0

private lemma heads_snoc {m : ℕ} (s : Fin m → Bool) (b : Bool) :
    heads (Fin.snoc s b) = heads s + if b then 1 else 0 := by
  unfold heads
  rw [Fin.sum_univ_castSucc]
  simp

private lemma heads_le {m : ℕ} (s : Fin m → Bool) : heads s ≤ m := by
  unfold heads
  calc
    _ ≤ ∑ _ : Fin m, (1 : ℕ) := by
      apply sum_le_sum
      intro i _
      split <;> decide
    _ = _ := by simp

private lemma endpoint_heads {m : ℕ} (s : Fin m → Bool) :
    endpoint s = 2 * (heads s : ℤ) - m := by
  unfold endpoint heads
  push_cast
  have h (i : Fin m) : step (s i) = 2 * (if s i then (1 : ℤ) else 0) - 1 := by
    cases ho : s i <;> norm_num [step, ho]
  simp only [h, sum_sub_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

private def exactHeads (m k : ℕ) : ℕ :=
  ∑ s : Fin m → Bool, if heads s = k then 1 else 0

private lemma exactHeads_choose (m k : ℕ) : exactHeads m k = m.choose k := by
  induction m generalizing k with
  | zero =>
    cases k <;> simp [exactHeads, heads, Nat.choose_zero_succ]
  | succ m ih =>
    unfold exactHeads
    rw [sum_snoc]
    simp only [heads_snoc, Bool.false_eq_true, if_false, add_zero, if_true]
    cases k with
    | zero =>
      change exactHeads m 0 + (∑ s : Fin m → Bool, if heads s + 1 = 0 then 1 else 0) = _
      rw [ih]
      simp
    | succ k =>
      simp only [Nat.succ.injEq, ← Nat.succ_eq_add_one]
      change exactHeads m k.succ + exactHeads m k = _
      rw [ih, ih, Nat.choose_succ_succ]
      ac_rfl

private lemma sum_heads (m : ℕ) (f : ℕ → ℕ) :
    ∑ s : Fin m → Bool, f (heads s) = ∑ k ∈ range (m+1), m.choose k * f k := by
  have hmem (s : Fin m → Bool) (_ : s ∈ (univ : Finset (Fin m → Bool))) :
      heads s ∈ range (m+1) := mem_range.mpr (Nat.lt_succ_of_le (heads_le s))
  rw [← sum_fiberwise_of_maps_to hmem (fun s => f (heads s))]
  apply sum_congr rfl
  intro k _
  calc
    _ = ∑ s ∈ univ.filter (fun s : Fin m → Bool => heads s = k), f k := by
      apply sum_congr rfl
      intro s hs
      rw [(mem_filter.mp hs).2]
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, ← exactHeads_choose]
      unfold exactHeads
      simp only [sum_boole, Nat.cast_id]

theorem above_distribution (m : ℕ) (t : ℤ) :
    above m t = ∑ k ∈ range (m+1), if t ≤ 2*(k : ℤ)-m then m.choose k else 0 := by
  unfold above
  simp_rw [endpoint_heads]
  rw [sum_heads m (fun k => if t ≤ 2*(k : ℤ)-m then 1 else 0)]
  apply sum_congr rfl
  intro k _
  split <;> simp_all

end A000531Walk


open Finset
open scoped BigOperators

namespace A000531Binomial

def high (n : ℕ) : ℕ := ∑ i ∈ range n, (2*n).choose (n+i+1)

def weighted (n : ℕ) : ℕ := ∑ i ∈ range n, (2*i+1) * (2*n).choose (n+i+1)

private lemma split_choose (n : ℕ) :
    2 * high n + (2*n).choose n = 4 ^ n := by
  have hr : (∑ i ∈ range n, (2*n).choose i) = high n := by
    unfold high
    rw [← sum_range_reflect (fun i => (2*n).choose i) n]
    apply sum_congr rfl
    intro i hi
    have h : i < n := mem_range.mp hi
    rw [← Nat.choose_symm (show n+i+1 ≤ 2*n by omega)]
    congr 1
    omega
  have h := Nat.sum_range_choose (2*n)
  rw [show 2*n+1 = (n+1)+n by omega, sum_range_add, sum_range_succ, hr] at h
  rw [show 2 ^ (2*n) = 4 ^ n by rw [pow_mul]; norm_num] at h
  have h' : (∑ i ∈ range n, (2*n).choose (n+1+i)) = high n := by
    unfold high
    apply sum_congr rfl
    intro i _
    congr 1
    omega
  rw [h'] at h
  omega

private lemma telescope_point (n i : ℕ) (hi : i < n) :
    ((i : ℤ) + 1) * ((2*n).choose (n+i+1) : ℤ) =
      (n : ℤ) * (((2*n-1).choose (n+i) : ℤ) - ((2*n-1).choose (n+i+1) : ℤ)) := by
  have h0 : 2*n-1+1 = 2*n := by omega
  have h1 := Nat.choose_mul_succ_eq (2*n-1) (n+i)
  have h2 := Nat.choose_mul_succ_eq (2*n-1) (n+i+1)
  rw [h0] at h1 h2
  rw [← Nat.choose_succ_right_eq] at h1
  have h1' : ((2*n-1).choose (n+i) : ℤ) * (2*(n : ℤ)) =
      ((2*n).choose (n+i+1) : ℤ) * ((n : ℤ) + i + 1) := by
    exact_mod_cast h1
  have h2' : ((2*n-1).choose (n+i+1) : ℤ) * (2*(n : ℤ)) =
      ((2*n).choose (n+i+1) : ℤ) * (2*(n : ℤ) - (n+i+1)) := by
    have h := congrArg (fun v : ℕ => (v : ℤ)) h2
    push_cast [Nat.cast_sub (by omega : n+i+1 ≤ 2*n)] at h
    exact h
  nlinarith [h1', h2']

private lemma weighted_identity (n : ℕ) (hn : 0 < n) :
    weighted n + high n = n * (2*n).choose n := by
  have hc : 2 * (2*n-1).choose n = (2*n).choose n := by
    have h := Nat.choose_mul_right (m := 2) (n := n) hn.ne'
    have hs := Nat.choose_symm (show n ≤ 2*n-1 by omega)
    rw [show 2*n-1-n = n-1 by omega] at hs
    rw [h, hs]
  have hs (i : ℕ) (hi : i ∈ range n) :
      ((2*i+1) * (2*n).choose (n+i+1) : ℤ) + ((2*n).choose (n+i+1) : ℤ) =
        (2*(n : ℤ)) * (((2*n-1).choose (n+i) : ℤ) - ((2*n-1).choose (n+i+1) : ℤ)) := by
    linear_combination 2 * telescope_point n i (mem_range.mp hi)
  have hsum := sum_congr (rfl : range n = range n) hs
  rw [sum_add_distrib, ← mul_sum] at hsum
  let u (i : ℕ) : ℤ := ((2*n-1).choose (n+i) : ℤ)
  have ht : (∑ i ∈ range n, (((2*n-1).choose (n+i) : ℤ) - ((2*n-1).choose (n+i+1) : ℤ))) =
      ((2*n-1).choose n : ℤ) := by
    have hu : (∑ i ∈ range n, (((2*n-1).choose (n+i) : ℤ) - ((2*n-1).choose (n+i+1) : ℤ))) =
        (∑ i ∈ range n, (u i - u (i+1))) := by
      apply sum_congr rfl
      intro i _
      simp [u, add_assoc]
    rw [hu, sum_range_sub']
    simp [u, show n+n = 2*n by omega, Nat.choose_eq_zero_of_lt (show 2*n-1 < 2*n by omega)]
  rw [ht] at hsum
  have hc' : (2 : ℤ)*((2*n-1).choose n : ℤ) = ((2*n).choose n : ℤ) := by exact_mod_cast hc
  have hprod := congrArg ((n : ℤ) * ·) hc'
  have h : (weighted n : ℤ) + (high n : ℤ) = (n : ℤ) * ((2*n).choose n : ℤ) := by
    unfold weighted high
    push_cast at *
    linear_combination hsum + hprod
  exact_mod_cast h

theorem weighted_closed (n : ℕ) (hn : 0 < n) :
    weighted n = ((2*n+1) * (2*n).choose n - 4^n) / 2 := by
  have h1 := split_choose n
  have h2 := weighted_identity n hn
  have h3 : (2*n+1) * (2*n).choose n = 2 * (n * (2*n).choose n) + (2*n).choose n := by ring
  omega

end A000531Binomial

namespace A000531Proof

open Finset
open A000531Geometry A000531Walk A000531Binomial

private lemma real_suffix_eq (n : ℕ) (s : Fin (2*n) → Bool) (k : ℕ) :
    suffix (realSigns n s) k = (suffixZ s k : ℝ) := by
  unfold suffix suffixZ
  push_cast
  apply sum_congr rfl
  intro i _
  by_cases hk : k ≤ i.val
  · cases hs : s i <;> norm_num [realSigns, step, hk, hs]
  · simp [hk]

private lemma attains_iff_hits (n : ℕ) (s : Fin (2*n) → Bool) (j : Fin n) :
    OMA.S_oeis_a000531.AttainsOddSum n s j ↔
      2 * (j.val : ℤ) + 2 ≤ peak (2*n) s := by
  rw [attains_iff_suffix, peak_iff_suffix]
  simp_rw [real_suffix_eq]
  constructor
  · rintro ⟨k, h⟩
    have hb : k ≤ 2*n := by
      by_contra! hh
      have hz : suffixZ s k = 0 := by
        unfold suffixZ
        apply sum_eq_zero
        intro i _
        simp [show ¬ k ≤ i.val by omega]
      rw [hz, Int.cast_zero] at h
      have ht : 0 ≤ 2 * (j.val : ℝ) + 1 := by positivity
      linarith
    have hz : 2 * (j.val : ℤ) + 1 < suffixZ s k := by exact_mod_cast h
    exact ⟨k, hb, by omega⟩
  · rintro ⟨k, _, h⟩
    have hz : 2 * (j.val : ℤ) + 1 < suffixZ s k := by omega
    exact ⟨k, by exact_mod_cast hz⟩

private def cut (threshold k : ℕ) : ℕ := if threshold ≤ k then 1 else 0

private lemma sum_cuts (n a k : ℕ) (h : k+1-a ≤ n) :
    ∑ j ∈ range n, cut (a+j) k = k+1-a := by
  unfold cut
  rw [sum_boole]
  have hf : (range n).filter (fun j => a+j ≤ k) = range (k+1-a) := by
    ext j
    simp only [mem_filter, mem_range]
    omega
  rw [hf, card_range]
  rfl

private lemma hits_expand (n j : ℕ) :
    hits (2*n) (2*(j : ℤ)+2) =
      ∑ k ∈ range (2*n+1),
        (2*n).choose k * (cut (n+1+j) k + cut (n+2+j) k) := by
  rw [hits_eq_above _ _ (by positivity), above_distribution, above_distribution, ← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  have h1 : (2 * (j : ℤ) + 2 ≤ 2 * (k : ℤ) - ((2*n : ℕ) : ℤ)) ↔ n+1+j ≤ k := by
    push_cast
    omega
  have h2 : (2 * (j : ℤ) + 2 + 1 ≤ 2 * (k : ℤ) - ((2*n : ℕ) : ℤ)) ↔ n+2+j ≤ k := by
    push_cast
    omega
  simp only [h1, h2]
  by_cases ha : n+1+j ≤ k <;> by_cases hb : n+2+j ≤ k <;>
    simp [cut, ha, hb, Nat.mul_succ, Nat.mul_comm]

private lemma hits_weighted (n : ℕ) :
    ∑ j ∈ range n, hits (2*n) (2*(j : ℤ)+2) = weighted n := by
  simp_rw [hits_expand]
  rw [sum_comm]
  have hcol (k : ℕ) (hk : k ∈ range (2*n+1)) :
      (∑ j ∈ range n, (2*n).choose k * (cut (n+1+j) k + cut (n+2+j) k)) =
        (2*n).choose k * ((k+1-(n+1)) + (k+1-(n+2))) := by
    rw [← mul_sum, sum_add_distrib, sum_cuts, sum_cuts]
    all_goals have h := mem_range.mp hk; omega
  calc
    _ = ∑ k ∈ range (2*n+1), (2*n).choose k * ((k+1-(n+1)) + (k+1-(n+2))) :=
      sum_congr rfl hcol
    _ = weighted n := by
      rw [show 2*n+1 = (n+1)+n by omega, sum_range_add]
      have hz :
          (∑ k ∈ range (n+1), (2*n).choose k * ((k+1-(n+1)) + (k+1-(n+2)))) = 0 := by
        apply sum_eq_zero
        intro k hk
        have h := mem_range.mp hk
        simp [show k+1-(n+1)=0 by omega, show k+1-(n+2)=0 by omega]
      rw [hz, zero_add]
      unfold weighted
      apply sum_congr rfl
      intro k _
      rw [show n+1+k = n+k+1 by omega, show (n+k+1+1-(n+1)) + (n+k+1+1-(n+2)) = 2*k+1 by omega,
        Nat.mul_comm]

end A000531Proof

open Finset A000531Walk A000531Proof A000531Binomial in
theorem OMA.solution : type_of% @OMA.S_oeis_a000531.main := by
  intro n hn
  classical
  have hc := Finset.sum_boole (R := ℕ) (fun x : (Fin (2*n) → Bool) × Fin n =>
    OMA.S_oeis_a000531.AttainsOddSum n x.1 x.2) univ
  simp only [Nat.cast_id] at hc
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hc, Fintype.sum_prod_type, sum_comm]
  simp_rw [attains_iff_hits]
  change (∑ j : Fin n, hits (2*n) (2*(j.val : ℤ)+2)) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => hits (2*n) (2*(j : ℤ)+2)),
    hits_weighted, weighted_closed _ (by omega)]
