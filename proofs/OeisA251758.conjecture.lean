import FormalConjectures.OEIS.«251758»
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# First occurrence of eight in OEIS A251758

Divisor reflection expresses the normalized sum as a sum of adjacent reciprocal
products. Below the proposed first index, an integer with no prime divisor below
11 has at most seven distinct prime factors. If it lacks one of the first seven,
compare its sorted divisors by rank with seven small primes and rough composites.
If all seven divide it, a single finite list covers its small divisors. Beyond
each cutoff, the gaps between odd divisors give a telescoping bound.
-/

namespace A251758Candidate

theorem primorial_value :
    Nat.kthPrimorial 12 / Nat.kthPrimorial (Nat.primeCounting' 8) = 35336848261 := by
  rw [show Nat.primeCounting' 8 = 4 by decide]
  norm_num [Nat.kthPrimorial_succ]

theorem sorted_divisors (n : ℕ) (hn : 0 < n) :
    (List.range (n + 1)).filter (· ∣ n) = n.divisors.sort := by
  apply ((List.sortedLT_range _).pairwise.filter _).sortedLT.eq_of_mem_iff n.divisors.sortedLT_sort
  intro d
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, Finset.mem_sort, Nat.mem_divisors]
  exact ⟨fun h => ⟨h.2, hn.ne'⟩, fun h => ⟨Nat.lt_succ_of_le (Nat.le_of_dvd hn h.1), h.1⟩⟩

private def candidateDivisors : List ℕ :=
   [1, 11, 13, 17, 19, 23, 29, 31,
    37, 143, 187, 209, 221, 247, 253, 299,
    319, 323, 341, 377, 391, 403, 407, 437,
    481, 493, 527, 551, 589, 629, 667, 703,
    713, 851, 899, 1073, 1147, 2431, 2717, 3289,
    3553, 4147, 4199, 4301, 4433, 4807, 5083, 5291,
    5423, 5681, 5797, 6061, 6409, 6479, 6851, 6919,
    7163, 7337, 7429, 7657, 7733, 7843, 8177, 8671,
    9139, 9269, 9361, 9367, 9889, 10013, 11063, 11339,
    11687, 11803, 11951, 12121, 12617, 12673, 13547, 13949,
    14467, 14911, 15283, 16169, 17081, 18241, 19499, 20387,
    20677, 21793, 24679, 26381, 33263, 46189, 55913, 62491,
    70499, 75361, 78793, 81719, 84227, 89947, 95381, 96577,
    100529, 101959, 103037, 110143, 121693, 121771, 124729, 128557,
    130169, 131461, 133331, 139403, 147407, 149017, 153439, 155363,
    157573, 159137, 164021, 164749, 168113, 176111, 177859, 187891,
    188071, 198679, 200651, 210197, 214489, 215441, 222053, 224257,
    227447, 230299, 237133, 239723, 253487, 265031, 268801, 271469,
    274873, 283309, 290191, 290377, 320827, 342953, 346579, 351509,
    365893, 370481, 392863, 419543, 432419, 448477, 468901, 501239,
    565471, 631997, 765049, 1062347, 1339481, 1431859, 1621477, 1708993,
    1733303, 1812239, 1937221, 2068781, 2185469, 2312167, 2369851, 2442583,
    2533289, 2608463, 2788357, 2800733, 2915341, 2956811, 2993887, 3023603,
    3116399, 3194147, 3529097, 3573349, 3772483, 3774901, 3812369, 3866599,
    4075291, 4321493, 4505527, 4569617, 4614973, 4756609, 4816253, 4933247,
    5107219, 5157911, 5454059, 5513629, 5830201, 6095713, 6220181, 6516107,
    6678671, 6951967, 7351123, 7971317, 8215961, 8415539, 8521063, 9945637,
    10743949, 13005833, 14535931, 30808063, 32932757, 39306839, 41523911, 49560797,
    50265787, 52978783, 56179409, 59994649, 64132211, 67052843, 71677177, 73465381,
    80862353, 86822723, 87684487, 90375571, 93731693, 103627121, 109402007, 110773819,
    118183439, 139671337, 143064163, 159895241, 169075829, 188967103, 247110827, 955049953,
    1139898331, 1218512009, 1536384707, 1859834119, 2078638133, 2718219097, 3212440751, 35336848261]

private theorem divisor_count : (35336848261 : ℕ).divisors.card = 256 := by
  rw [show (35336848261 : ℕ) = 955049953 * 37 by decide,
    Nat.Coprime.card_divisors_mul (show Nat.Coprime 955049953 37 by decide)]
  rw [show (955049953 : ℕ) = 30808063 * 31 by decide,
    Nat.Coprime.card_divisors_mul (show Nat.Coprime 30808063 31 by decide)]
  rw [show (30808063 : ℕ) = 1062347 * 29 by decide,
    Nat.Coprime.card_divisors_mul (show Nat.Coprime 1062347 29 by decide)]
  rw [show (1062347 : ℕ) = 46189 * 23 by decide,
    Nat.Coprime.card_divisors_mul (show Nat.Coprime 46189 23 by decide)]
  rw [show (46189 : ℕ) = 2431 * 19 by decide,
    Nat.Coprime.card_divisors_mul (show Nat.Coprime 2431 19 by decide)]
  rw [show (2431 : ℕ) = 143 * 17 by decide,
    Nat.Coprime.card_divisors_mul (show Nat.Coprime 143 17 by decide)]
  rw [show (143 : ℕ) = 11 * 13 by decide,
    Nat.Coprime.card_divisors_mul (show Nat.Coprime 11 13 by decide)]
  decide

private theorem divisors_complete {n : ℕ} (hn : n ≠ 0) (l : List ℕ) (hs : l.SortedLT)
    (hd : ∀ d ∈ l, d ∣ n) (hc : n.divisors.card = l.length) : n.divisors.sort = l := by
  have eq : l.toFinset = n.divisors := by
    apply Finset.eq_of_subset_of_card_le
    · intro d h
      exact Nat.mem_divisors.mpr ⟨hd d (List.mem_toFinset.mp h), hn⟩
    · rw [hc, List.toFinset_card_of_nodup hs.nodup]
  exact n.divisors.sortedLT_sort.eq_of_mem_iff hs fun d => by simp [← eq]

set_option maxRecDepth 4000 in
theorem candidate_value : OeisA251758.a 35336848261 = 8 := by
  have computed : (35336848261 : ℕ).divisors.sort = candidateDivisors := by
    apply divisors_complete (by decide)
    · decide
    · have h : candidateDivisors.all (fun d => decide (d ∣ 35336848261)) = true := by decide
      simpa using List.all_eq_true.mp h
    · exact divisor_count
  unfold OeisA251758.a
  rw [sorted_divisors _ (by decide), computed]
  decide

end A251758Candidate

/- Divisor reflection and bounds for the value eight. -/

namespace A251758Proof

def ds (n : ℕ) := (List.range (n + 1)).filter (· ∣ n)

def recip (l : List ℕ) : ℚ :=
  ((l.zip l.tail).map (fun p => 1 / ((p.1 : ℚ) * p.2))).sum

theorem mem_ds {d n : ℕ} (hn : 0 < n) : d ∈ ds n ↔ d ∣ n := by
  simp [ds, and_iff_right_of_imp (fun hd : d ∣ n => Nat.le_of_dvd hn hd)]

theorem ds_sorted (n : ℕ) : (ds n).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

private theorem reflect_list {n : ℕ} (hn : 0 < n) :
    ((ds n).map (n / ·)).reverse = ds n := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·)) _ (ds_sorted n)
  · intro x
    simp only [List.mem_reverse, List.mem_map, mem_ds hn]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact Nat.div_dvd_of_dvd hd
    · intro hx
      exact ⟨n / x, Nat.div_dvd_of_dvd hx, Nat.div_div_self hx hn.ne'⟩
  · apply List.pairwise_reverse.mpr
    apply List.pairwise_map.mpr
    apply (ds_sorted n).imp_of_mem
    intro x y hx hy hxy
    have dx := (mem_ds hn).mp hx
    have dy := (mem_ds hn).mp hy
    have hx0 := Nat.pos_of_dvd_of_pos dx hn
    have hy0 := Nat.pos_of_dvd_of_pos dy hn
    have hqy := Nat.div_pos (Nat.le_of_dvd hn dy) hy0
    exact (Nat.lt_div_iff_mul_lt_of_dvd hx0.ne' dx).mpr (by
      calc n / y * x < n / y * y := Nat.mul_lt_mul_of_pos_left hxy hqy
           _ = n := Nat.div_mul_cancel dy)

private def adj {R : Type} [AddMonoid R] (f : ℕ → ℕ → R) (l : List ℕ) : R :=
  ((l.zip l.tail).map (fun p => f p.1 p.2)).sum

private theorem adj_cons {R : Type} [AddMonoid R] (f : ℕ → ℕ → R) (x y : ℕ) (l : List ℕ) :
    adj f (x :: y :: l) = f x y + adj f (y :: l) := rfl

private theorem adj_snoc {R : Type} [AddMonoid R] (f : ℕ → ℕ → R) (l : List ℕ) (x y : ℕ) :
    adj f (l ++ [x,y]) = adj f (l ++ [x]) + f x y := by
  induction l with
  | nil => simp [adj]
  | cons a l ih =>
    cases l with
    | nil => simp [adj]
    | cons b l =>
      simpa only [List.cons_append, adj_cons, add_assoc] using congrArg (f a b + ·) ih

private theorem adj_reverse {R : Type} [AddCommMonoid R] (f : ℕ → ℕ → R)
    (hf : ∀ x y, f x y = f y x) : ∀ l, adj f l.reverse = adj f l
  | [] => rfl
  | [x] => rfl
  | x :: y :: l => by
    rw [List.reverse_cons, List.reverse_cons, List.append_assoc]
    change adj f (l.reverse ++ [y,x]) = _
    rw [adj_snoc, ← List.reverse_cons, adj_reverse f hf (y :: l), adj_cons, hf y x, add_comm]

private def total (l : List ℕ) := adj (· * ·) l

private theorem reflect_sum {n : ℕ} (hn : 0 < n) (l : List ℕ) (h : ∀ d ∈ l, d ∣ n) :
    ((total (l.map (n / ·)) : ℕ) : ℚ) = (n : ℚ)^2 * recip l := by
  match l with
  | [] => simp [total, adj, recip]
  | [x] => simp [total, adj, recip]
  | x :: y :: l =>
    have dx := h x (by simp)
    have dy := h y (by simp)
    have ex : (n / x : ℕ) * (x : ℚ) = n := by exact_mod_cast Nat.div_mul_cancel dx
    have ey : (n / y : ℕ) * (y : ℚ) = n := by exact_mod_cast Nat.div_mul_cancel dy
    have hx : (x : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_dvd_of_pos dx hn).ne'
    have hy : (y : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_dvd_of_pos dy hn).ne'
    have term : (n / x : ℕ) * (n / y : ℕ) = (n : ℚ)^2 * (1 / ((x : ℚ)*y)) := by
      field_simp
      calc _ = ((n / x : ℕ) * (x : ℚ)) * ((n / y : ℕ) * (y : ℚ)) := by ring
           _ = _ := by rw [ex,ey]; ring
    have ih := reflect_sum hn (y :: l) (fun d hd => h d (List.mem_cons_of_mem _ hd))
    change ((n / x * (n / y) + total ((y :: l).map (n / ·)) : ℕ) : ℚ) =
      (n : ℚ)^2 * (1 / ((x : ℚ)*y) + recip (y :: l))
    rw [Nat.cast_add, Nat.cast_mul, ih, mul_add]
    exact congrArg (· + _) term

theorem total_reflection {n : ℕ} (hn : 0 < n) :
    ((total (ds n) : ℕ) : ℚ) = (n : ℚ)^2 * recip (ds n) := by
  calc
    _ = (total (((ds n).map (n / ·)).reverse) : ℚ) := by rw [reflect_list hn]
    _ = (total ((ds n).map (n / ·)) : ℚ) := by
      unfold total
      rw [adj_reverse (· * ·) Nat.mul_comm]
    _ = _ := reflect_sum hn _ (fun _ hd => (mem_ds hn).mp hd)

theorem bounds_of_eight {n : ℕ} (hn : 2 ≤ n) (h : OeisA251758.a n = 8) :
    1 / 9 < recip (ds n) ∧ recip (ds n) ≤ 1 / 8 := by
  change (if total (ds n) = 0 then 0 else n^2 / total (ds n)) = 8 at h
  split at h
  · contradiction
  rename_i hs
  have hs' : 0 < total (ds n) := Nat.pos_of_ne_zero hs
  have hlo : n ^ 2 < 9 * total (ds n) := (Nat.div_lt_iff_lt_mul hs').mp (by omega)
  have hhi : 8 * total (ds n) ≤ n ^ 2 := (Nat.le_div_iff_mul_le hs').mp (by omega)
  have hlo' : (n : ℚ)^2 < 9 * (total (ds n) : ℚ) := by exact_mod_cast hlo
  have hhi' : 8 * (total (ds n) : ℚ) ≤ (n : ℚ)^2 := by exact_mod_cast hhi
  rw [total_reflection (by omega)] at hlo' hhi'
  have hn' : 0 < (n : ℚ)^2 := by positivity
  constructor
  · apply lt_of_mul_lt_mul_left (a := (n : ℚ)^2) _ hn'.le
    linarith
  · apply le_of_mul_le_mul_left (a := (n : ℚ)^2) _ hn'
    linarith

private theorem recip_nonneg (l : List ℕ) : 0 ≤ recip l := by
  unfold recip
  apply List.sum_nonneg
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intros
  positivity

theorem small_excluded {n p : ℕ} (hn : 2 ≤ n) (hp : 2 ≤ p) (hsmall : p ≤ 7)
    (hd : p ∣ n) : OeisA251758.a n ≠ 8 := by
  intro h
  have hb := (bounds_of_eight hn h).2
  have hn0 : 0 < n := by omega
  have h1 : 1 ∈ ds n := (mem_ds hn0).mpr (one_dvd _)
  have hp' : p ∈ ds n := (mem_ds hn0).mpr hd
  have hs := ds_sorted n
  generalize he : ds n = l at h1 hp' hs hb
  cases l with
  | nil => simp at h1
  | cons x l =>
    have hx : x = 1 := by
      rcases List.mem_cons.mp h1 with hx | h1
      · exact hx.symm
      · have hlt := (List.pairwise_cons.mp hs).1 _ h1
        have hxd : x ∣ n := (mem_ds hn0).mp (he ▸ List.mem_cons_self ..)
        have := Nat.pos_of_dvd_of_pos hxd hn0
        omega
    subst x
    have hp'' : p ∈ l := (List.mem_cons.mp hp').resolve_left (by omega)
    cases l with
    | nil => simp at hp''
    | cons y l =>
      have hy : y ≤ p := by
        rcases List.mem_cons.mp hp'' with rfl | hp''
        · rfl
        · exact ((List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 p hp'').le
      have hypos := (List.pairwise_cons.mp hs).1 y (by simp)
      change 1 / ((1 : ℚ)*y) + recip (y :: l) ≤ 1 / 8 at hb
      rw [one_mul] at hb
      have ht := recip_nonneg (y :: l)
      have hy7 : (y : ℚ) < 8 := by exact_mod_cast (show y < 8 by omega)
      have hy0 : (0 : ℚ) < y := by exact_mod_cast (show 0 < y by omega)
      have hy8 : (1 : ℚ) / 8 < 1 / y := by
        exact one_div_lt_one_div_of_lt hy0 hy7
      linarith

end A251758Proof

/- A telescoping bound for the reciprocal tail on odd divisors. -/

namespace A251758Proof

def fromRec (a : ℕ) : List ℕ → ℚ
  | [] => 0
  | b :: bs => 1 / ((a : ℚ) * b) + fromRec b bs

theorem recip_cons_eq (a : ℕ) (xs : List ℕ) : recip (a :: xs) = fromRec a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    change 1 / ((a : ℚ)*b) + recip (b :: bs) = 1 / ((a : ℚ)*b) + fromRec b bs
    rw [ih]

theorem odd_tail {a : ℕ} {xs : List ℕ} (ha : 0 < a) (hoa : Odd a)
    (hs : (a :: xs).Pairwise (· < ·)) (hos : ∀ x ∈ xs, Odd x) :
    fromRec a xs ≤ 1 / (2 * (a : ℚ)) := by
  induction xs generalizing a with
  | nil => simp [fromRec]
  | cons b bs ih =>
    have hb := (List.pairwise_cons.mp hs).1 b (by simp)
    have hb0 := lt_trans ha hb
    have hob := hos b (by simp)
    have hab : a + 2 ≤ b := by
      obtain ⟨u, hu⟩ := hoa
      obtain ⟨v, hv⟩ := hob
      omega
    have ha' : 0 < (a : ℚ) := by exact_mod_cast ha
    have hb' : 0 < (b : ℚ) := by exact_mod_cast hb0
    have hab' : (a : ℚ) + 2 ≤ b := by exact_mod_cast hab
    calc
      fromRec a (b :: bs) = 1 / ((a : ℚ) * b) + fromRec b bs := rfl
      _ ≤ 1 / ((a : ℚ) * b) + 1 / (2 * (b : ℚ)) := by
        apply add_le_add_right
        exact ih hb0 hob (List.pairwise_cons.mp hs).2 (fun x hx => hos x (by simp [hx]))
      _ ≤ 1 / (2 * (a : ℚ)) := by
        field_simp
        linarith

end A251758Proof

namespace A251758Proof

private theorem fromRec_nonneg (a : ℕ) (xs : List ℕ) : 0 ≤ fromRec a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    exact add_nonneg (by positivity) (ih b)

private theorem one_over_pair {a x y : ℕ} (ha : 0 < a) (hx : 0 < x) (h : x ≤ y) :
    1 / ((a : ℚ) * y) ≤ 1 / ((a : ℚ) * x) := by
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) (by positivity)

/-- Compare a divisor list with a sorted list containing all of its small entries.
The last comparison point bounds the edge crossing the cutoff. -/
private theorem cover_from {k : ℕ} (hk : 0 < k) (cover : List ℕ)
    (sc : cover.Pairwise (· < ·)) (hc : ∀ x ∈ cover, 0 < x ∧ x < k)
    (a : ℕ) (ha : 0 < a) (xs : List ℕ) (sx : xs.Pairwise (· < ·))
    (ox : ∀ x ∈ xs, Odd x) (incl : ∀ x ∈ xs, x < k → x ∈ cover) :
    fromRec a xs ≤ fromRec a (cover ++ [k]) + 1 / (2 * (k : ℚ)) := by
  induction cover generalizing a xs with
  | nil =>
    cases xs with
    | nil => exact add_nonneg (fromRec_nonneg ..) (by positivity)
    | cons b bs =>
      have hkb : k ≤ b := by
        by_contra! h
        simpa using incl b (by simp) h
      have hb := lt_of_lt_of_le hk hkb
      have ob := ox b (by simp)
      have ht := odd_tail hb ob sx (fun x hx => ox x (List.mem_cons_of_mem b hx))
      simp only [List.nil_append, fromRec, add_zero]
      apply add_le_add (one_over_pair ha hk hkb)
      refine ht.trans (one_div_le_one_div_of_le (by positivity) ?_)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hkb) (by positivity)
  | cons c cs ih =>
    obtain ⟨hc0,hck⟩ := hc c (by simp)
    obtain ⟨cmin,scs⟩ := List.pairwise_cons.mp sc
    have hcs := fun x hx => hc x (List.mem_cons_of_mem c hx)
    cases xs with
    | nil => exact add_nonneg (fromRec_nonneg ..) (by positivity)
    | cons b bs =>
      obtain ⟨bmin,sbs⟩ := List.pairwise_cons.mp sx
      have hcb : c ≤ b := by
        by_cases hbk : b < k
        · rcases List.mem_cons.mp (incl b (by simp) hbk) with e | mem
          · omega
          · exact (cmin _ mem).le
        · omega
      have hbs : ∀ x ∈ bs, x < k → x ∈ cs := by
        intro x hx hxk
        have hbx := bmin x hx
        exact (List.mem_cons.mp (incl x (List.mem_cons_of_mem b hx) hxk)).resolve_left (by omega)
      by_cases e : b = c
      · subst b
        simp only [List.cons_append, fromRec, add_assoc]
        exact add_le_add_right (ih scs hcs c hc0 bs sbs
          (fun x hx => ox x (List.mem_cons_of_mem c hx)) hbs) _
      · have hrest : ∀ x ∈ b :: bs, x < k → x ∈ cs := by
          intro x hx hxk
          rcases List.mem_cons.mp hx with rfl | hx
          · exact (List.mem_cons.mp (incl x (by simp) hxk)).resolve_left e
          · exact hbs x hx hxk
        have hr := ih scs hcs c hc0 (b :: bs) sx ox hrest
        have edge := one_over_pair ha hc0 hcb
        have nz : 0 ≤ 1 / ((c : ℚ) * b) := by positivity
        simp only [List.cons_append, fromRec] at hr ⊢
        linarith

private theorem one_head {l : List ℕ} (hs : l.Pairwise (· < ·)) (h1 : 1 ∈ l)
    (hp : ∀ x ∈ l, 0 < x) : ∃ xs, l = 1 :: xs := by
  cases l with
  | nil => simp at h1
  | cons a xs =>
    have ha := hp a (by simp)
    have : a = 1 := by
      rcases List.mem_cons.mp h1 with h | h
      · exact h.symm
      · have := (List.pairwise_cons.mp hs).1 1 h
        omega
    exact ⟨xs, by simp [this]⟩

theorem envelope_bounds {n K : ℕ} (hn : 2 ≤ n) (hodd : ¬ 2 ∣ n) (hK : 0 < K)
    {cover : List ℕ} (sc : cover.Pairwise (· < ·)) (hc : ∀ x ∈ cover, 0 < x ∧ x ≤ K)
    (incl : ∀ x, 0 < x → x ≤ K → x ∣ n → x ∈ cover) :
    recip (ds n) ≤ recip (cover ++ [K+1]) + 1 / (2 * ((K+1 : ℕ) : ℚ)) := by
  have hn0 : 0 < n := by omega
  have hp : ∀ x ∈ ds n, 0 < x := fun x hx => Nat.pos_of_dvd_of_pos ((mem_ds hn0).mp hx) hn0
  obtain ⟨xs,ex⟩ := one_head (ds_sorted n) ((mem_ds hn0).mpr (one_dvd _)) hp
  obtain ⟨cs,ec⟩ := one_head sc (incl 1 (by decide) hK (one_dvd _))
    (fun x hx => (hc x hx).1)
  have sx := ds_sorted n
  rw [ex] at sx
  subst cover
  rw [ex, List.cons_append, recip_cons_eq, recip_cons_eq]
  refine cover_from (Nat.succ_pos K) cs (List.pairwise_cons.mp sc).2 ?_ 1 (by decide) xs
    (List.pairwise_cons.mp sx).2 ?_ ?_
  · intro x hx
    obtain ⟨h0,hm⟩ := hc x (List.mem_cons_of_mem 1 hx)
    exact ⟨h0, by omega⟩
  · intro x hx
    have hx' : x ∈ ds n := ex ▸ List.mem_cons_of_mem 1 hx
    exact Nat.odd_iff.mpr (by
      have he : ¬ 2 ∣ x := fun h => hodd (h.trans ((mem_ds hn0).mp hx'))
      omega)
  · intro x hx hk
    have hx' : x ∈ ds n := ex ▸ List.mem_cons_of_mem 1 hx
    have hm := incl x (hp x hx') (by omega) ((mem_ds hn0).mp hx')
    have hx1 := (List.pairwise_cons.mp sx).1 x hx
    exact (List.mem_cons.mp hm).resolve_left (by omega)

end A251758Proof

namespace A251758Proof
/-- Round a unit fraction upward in units of one trillionth. -/
def envWeight (d : ℕ) : ℕ := (1000000000000 + d - 1) / d
end A251758Proof

namespace A251758Proof

def envCostAt (K x : ℕ) : List ℕ → ℕ
  | [] => envWeight (x * (K + 1))
  | y :: ys => envWeight (x * y) + envCostAt K y ys

def envTotalAt (K : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => envCostAt K x xs

def envOKAt (K : ℕ) (l : List ℕ) : Bool :=
  decide (9 * (envTotalAt K l + envWeight (2 * (K + 1))) ≤ 1000000000000)

private theorem weightAt_bound (d : ℕ) (hd : 0 < d) :
    1 / (d : ℚ) ≤ (envWeight d : ℚ) / 1000000000000 := by
  have hmod := Nat.mod_lt (1000000000000 + d - 1) hd
  have heq := Nat.div_add_mod (1000000000000 + d - 1) d
  have h : 1000000000000 ≤ d * envWeight d := by
    unfold envWeight
    omega
  have hq : (1000000000000 : ℚ) ≤ (d : ℚ) * (envWeight d : ℚ) := by exact_mod_cast h
  have hpos : 0 < (d : ℚ) := by exact_mod_cast hd
  apply (div_le_div_iff₀ hpos (by norm_num)).mpr
  simpa [mul_comm] using hq

private theorem costAt_bound (K x : ℕ) (l : List ℕ) (hx : 0 < x)
    (hl : ∀ y ∈ l, 0 < y) :
    fromRec x (l ++ [K+1]) ≤ (envCostAt K x l : ℚ) / 1000000000000 := by
  induction l generalizing x with
  | nil =>
    simpa [envCostAt, fromRec, Nat.cast_mul] using
      weightAt_bound (x * (K+1)) (by positivity)
  | cons y l ih =>
    have hy := hl y (by simp)
    have hw := weightAt_bound (x*y) (Nat.mul_pos hx hy)
    have ht := ih y hy (fun z hz => hl z (List.mem_cons_of_mem _ hz))
    simpa only [List.cons_append, fromRec, envCostAt, Nat.cast_add, Nat.cast_mul, add_div] using
      add_le_add hw ht

theorem envOKAt_sound (K : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, 0 < x)
    (h : envOKAt K l = true) :
    recip (l ++ [K+1]) + 1 / (2 * ((K+1 : ℕ) : ℚ)) ≤ 1 / 9 := by
  have hb : recip (l ++ [K+1]) ≤ (envTotalAt K l : ℚ) / 1000000000000 := by
    cases l with
    | nil => simp [envTotalAt, recip]
    | cons x l =>
      rw [List.cons_append, recip_cons_eq]
      exact costAt_bound K x l (hl x (by simp))
        (fun y hy => hl y (List.mem_cons_of_mem _ hy))
  simp only [envOKAt, decide_eq_true_eq] at h
  have hq : 9 * ((envTotalAt K l : ℚ) + (envWeight (2 * (K+1)) : ℚ)) ≤ 1000000000000 :=
    by exact_mod_cast h
  have hw := weightAt_bound (2 * (K+1)) (by positivity)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hw
  linarith

end A251758Proof

namespace A251758Compression

def primeBase : Fin 8 → ℕ := ![11, 13, 17, 19, 23, 29, 31, 37]

theorem primeRank_le {k : ℕ} (q : Fin k ↪o ℕ)
    (hp : ∀ i, (q i).Prime) (hr : ∀ i, 11 ≤ q i)
    (i : Fin k) (hi : i.val < 8) : primeBase ⟨i.val, hi⟩ ≤ q i := by
  let j : Fin 8 := ⟨i, hi⟩
  let s := (Finset.range (primeBase j)).filter (fun p => 11 ≤ p ∧ p.Prime)
  have hc : ∀ u : Fin 8, ((Finset.range (primeBase u)).filter
      (fun p => 11 ≤ p ∧ p.Prime)).card = u.val := by decide
  by_contra! h
  let f : Fin (i.val+1) → ℕ := fun v => q ⟨v, by omega⟩
  have hf : Function.Injective f := by
    intro u v huv
    change q _ = q _ at huv
    exact Fin.ext (congrArg (fun z : Fin k => z.val) (q.injective huv))
  have sub : Finset.univ.image f ⊆ s := by
    intro v hv
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hr _, hp _⟩
    exact lt_of_le_of_lt (q.monotone (show (⟨u.val,by omega⟩ : Fin k) ≤ i by
      exact Nat.le_of_lt_succ u.isLt)) h
  have := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] at this
  exact Nat.not_succ_le_self _ (this.trans (hc j).le)

theorem sevenFactors {n : ℕ} (hn : 0 < n) (hm : n < 35336848261)
    (hr : ∀ p ∈ n.primeFactors, 11 ≤ p) : n.primeFactors.card ≤ 7 := by
  by_contra! h
  let q := n.primeFactors.orderEmbOfCardLe (show 8 ≤ n.primeFactors.card by omega)
  have mem (i : Fin 8) : q i ∈ n.primeFactors := Finset.orderEmbOfCardLe_mem _ _ _
  have lo (i : Fin 8) : primeBase i ≤ q i :=
    primeRank_le q (fun j => Nat.prime_of_mem_primeFactors (mem j))
      (fun j => hr _ (mem j)) i i.isLt
  have low : (∏ i : Fin 8, primeBase i) ≤ ∏ i : Fin 8, q i :=
    Finset.prod_le_prod' fun i _ => lo i
  have sub : (Finset.univ.image q) ⊆ n.primeFactors := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact mem i
  have dv := Finset.prod_dvd_prod_of_subset _ _ id sub
  rw [Finset.prod_image q.injective.injOn] at dv
  have bound := Nat.le_of_dvd hn (dvd_trans dv (Nat.prod_primeFactors_dvd n))
  have eqn : (∏ i : Fin 8, primeBase i) = 35336848261 := by decide
  exact not_le.mpr hm (by simpa only [eqn, id_eq] using low.trans bound)

end A251758Compression

namespace A251758Proof

def rankCount (l : List ℕ) (t : ℕ) := (l.filter (· ≤ t)).length

private theorem rank_zero {l : List ℕ} {t : ℕ} (h : ∀ x ∈ l, t < x) :
    rankCount l t = 0 := by
  unfold rankCount
  rw [List.filter_eq_nil_iff.mpr (by simpa using h)]
  rfl

private theorem rank_cons_of_le (l : List ℕ) {b t : ℕ} (hb : b ≤ t) :
    rankCount (b :: l) t = rankCount l t + 1 := by simp [rankCount, hb]

private theorem rank_fraction {a b c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (hca : c ≤ a) (hdb : d ≤ b) : 1 / ((a : ℚ) * b) ≤ 1 / ((c : ℚ) * d) := by
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.mul_le_mul hca hdb

private theorem rank_from_nonneg (a : ℕ) (xs : List ℕ) : 0 ≤ fromRec a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih => exact add_nonneg (by positivity) (ih b)

theorem rank_from {k : ℕ} (hk : 0 < k) (env : List ℕ) (he : env.Pairwise (· < ·))
    (hbnd : ∀ x ∈ env, 0 < x ∧ x < k) (a c : ℕ) (hc : 0 < c) (hca : c ≤ a)
    (xs : List ℕ) (hs : xs.Pairwise (· < ·)) (ho : ∀ x ∈ xs, Odd x)
    (hr : ∀ t < k, rankCount xs t ≤ rankCount env t) :
    fromRec a xs ≤ fromRec c (env ++ [k]) + 1 / (2 * (k : ℚ)) := by
  induction env generalizing a c xs with
  | nil =>
    cases xs with
    | nil => exact add_nonneg (rank_from_nonneg ..) (by positivity)
    | cons b bs =>
      have hkb : k ≤ b := by
        by_contra! h
        have lt := hr b h
        rw [rank_cons_of_le _ le_rfl] at lt
        simp [rankCount] at lt
      have ht := odd_tail (lt_of_lt_of_le hk hkb) (ho b (by simp)) hs
        (fun x hx => ho x (List.mem_cons_of_mem b hx))
      simp only [List.nil_append, fromRec, add_zero]
      apply add_le_add (rank_fraction hc hk hca hkb)
      refine ht.trans (one_div_le_one_div_of_le (by positivity) ?_)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hkb) (by positivity)
  | cons d ds ih =>
    have hd := hbnd d (by simp)
    have ⟨hdmin, hes⟩ := List.pairwise_cons.mp he
    cases xs with
    | nil => exact add_nonneg (rank_from_nonneg ..) (by positivity)
    | cons b bs =>
      obtain ⟨hbmin, hbs⟩ := List.pairwise_cons.mp hs
      have hdb : d ≤ b := by
        by_contra! h
        have ht := hr b (h.trans hd.2)
        have hz : rankCount (d :: ds) b = 0 := rank_zero (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h
          · exact h.trans (hdmin x hx))
        rw [rank_cons_of_le _ le_rfl, hz] at ht
        omega
      have tail : ∀ t < k, rankCount bs t ≤ rankCount ds t := by
        intro t htk
        by_cases hbt : b ≤ t
        · have h := hr t htk
          rwa [rank_cons_of_le _ hbt, rank_cons_of_le _ (hdb.trans hbt), Nat.add_le_add_iff_right] at h
        · rw [rank_zero (fun x hx => (Nat.lt_of_not_ge hbt).trans (hbmin x hx))]
          omega
      have hrec := ih hes (fun x hx => hbnd x (List.mem_cons_of_mem d hx)) b d hd.1 hdb bs hbs
        (fun x hx => ho x (List.mem_cons_of_mem b hx)) tail
      have hterm := rank_fraction hc hd.1 hca hdb
      simp only [List.cons_append, fromRec]
      linarith

theorem rank_envelope {k : ℕ} (hk : 0 < k) (xs es : List ℕ)
    (hs : xs.Pairwise (· < ·)) (ho : ∀ x ∈ xs, Odd x) (he : es.Pairwise (· < ·))
    (hb : ∀ x ∈ es, 0 < x ∧ x < k)
    (hr : ∀ t < k, rankCount (1 :: xs) t ≤ rankCount (1 :: es) t) :
    recip (1 :: xs) ≤ recip ((1 :: es) ++ [k]) + 1 / (2 * (k : ℚ)) := by
  simp only [List.cons_append, recip_cons_eq]
  apply rank_from hk es he hb 1 1 (by decide) le_rfl xs hs ho
  intro t ht
  have h := hr t ht
  by_cases h1 : 1 ≤ t
  · rwa [rank_cons_of_le _ h1, rank_cons_of_le _ h1, Nat.add_le_add_iff_right] at h
  · simpa [rankCount, h1] using h

theorem rankCount_finset (l : List ℕ) (hl : l.Nodup) (t : ℕ) :
    rankCount l t = (l.toFinset.filter (· ≤ t)).card := by
  unfold rankCount
  rw [← List.toFinset_card_of_nodup (hl.filter _)]
  congr 1
  ext
  simp

theorem rankCount_ds {n : ℕ} (hn : 0 < n) (t : ℕ) :
    rankCount (ds n) t = (n.divisors.filter (· ≤ t)).card := by
  rw [rankCount_finset _ (ds_sorted n).nodup]
  have he : (ds n).toFinset = n.divisors := by
    ext
    simp [mem_ds hn, Nat.mem_divisors, hn.ne']
  rw [he]

private theorem rank_one_head {l : List ℕ} (hs : l.Pairwise (· < ·))
    (hpos : ∀ x ∈ l, 0 < x) (h1 : 1 ∈ l) : ∃ xs, l = 1 :: xs := by
  cases l with
  | nil => simp at h1
  | cons a xs =>
    have ha := hpos a (by simp)
    have he : a = 1 := by
      rcases List.mem_cons.mp h1 with he | h1
      · exact he.symm
      · have := (List.pairwise_cons.mp hs).1 1 h1
        omega
    exact ⟨xs, by rw [he]⟩

theorem rank_divisor_bound {n k : ℕ} (hn : 0 < n) (hodd : ¬ 2 ∣ n) (hk : 0 < k)
    {env : List ℕ} (he : env.Pairwise (· < ·)) (hb : ∀ x ∈ env, 0 < x ∧ x < k)
    (h1 : 1 ∈ env) (hr : ∀ t < k, (n.divisors.filter (· ≤ t)).card ≤ rankCount env t) :
    recip (ds n) ≤ recip (env ++ [k]) + 1 / (2 * (k : ℚ)) := by
  obtain ⟨xs, hx⟩ := rank_one_head (ds_sorted n)
    (fun _ hm => Nat.pos_of_dvd_of_pos ((mem_ds hn).mp hm) hn) ((mem_ds hn).mpr (one_dvd _))
  obtain ⟨es, ee⟩ := rank_one_head he (fun _ hm => (hb _ hm).1) h1
  subst env
  have hxs := ds_sorted n
  rw [hx] at hxs ⊢
  apply rank_envelope hk _ _ (List.pairwise_cons.mp hxs).2 _ (List.pairwise_cons.mp he).2
    (fun x hm => hb x (List.mem_cons_of_mem _ hm))
  · intro t ht
    simpa only [← hx, rankCount_ds hn] using hr t ht
  · intro d hm
    have hd := (mem_ds hn).mp (hx ▸ List.mem_cons_of_mem 1 hm)
    have hnd : ¬ 2 ∣ d := fun h => hodd (h.trans hd)
    exact Nat.odd_iff.mpr (by omega)

end A251758Proof

namespace A251758Proof

def rankEnv :=
  (List.range' 1 3000).filter (fun d => decide (d ∈ [1,11,13,17,19,23,29,37]) ||
    (decide (¬ d.Prime) && [2,3,5,7].all (fun p => d % p != 0)))

private def trialPrimes : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53]

private def rankComposite (d : ℕ) : Bool :=
  decide (d < 2) || trialPrimes.any (fun p => decide (p < d) && (d % p == 0))

private theorem rankComposite_eq (d : ℕ) (hd : d ≤ 3000) :
    rankComposite d = decide (¬ d.Prime) := by
  apply Bool.eq_iff_iff.mpr
  simp only [rankComposite, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro (hs | ⟨p,hp,hpd,hmod⟩) h
    · exact (Nat.not_lt.mpr h.two_le) hs
    · have lo : ∀ q ∈ trialPrimes, 2 ≤ q := by decide
      rcases (Nat.dvd_prime h).mp (Nat.dvd_of_mod_eq_zero hmod) with h1 | heq
      · have := lo p hp
        omega
      · omega
  · intro h
    by_cases hs : d < 2
    · exact Or.inl hs
    · have sq := Nat.minFac_sq_le_self (by omega : 0 < d) h
      have small : d.minFac < 55 := by nlinarith [sq]
      have pr := Nat.minFac_prime (by omega : d ≠ 1)
      have hmem : ∀ q : Fin 55, q.val.Prime → q.val ∈ trialPrimes := by decide
      exact Or.inr ⟨d.minFac,hmem ⟨d.minFac,small⟩ pr,
        (Nat.not_prime_iff_minFac_lt (by omega)).mp h,
        Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd _)⟩

private def rankBlock (s k : ℕ) := (List.range' s k).filter (fun d =>
  decide (d ∈ [1,11,13,17,19,23,29,37]) ||
    ([2,3,5,7].all (fun p => d % p != 0) && rankComposite d))

private theorem rankBlock_append {s m n : ℕ} {a b : List ℕ}
    (h₁ : rankBlock s m = a) (h₂ : rankBlock (s+m) n = b) :
    rankBlock s (m+n) = a ++ b := by
  unfold rankBlock at *
  rw [← List.range'_append_1, List.filter_append, h₁, h₂]


set_option maxRecDepth 12000 in
private theorem rankBlock1 : rankBlock 1 50 = [1, 11, 13, 17, 19, 23, 29, 37] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock51 : rankBlock 51 50 = [] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock101 : rankBlock 101 50 = [121, 143] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock151 : rankBlock 151 50 = [169, 187] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock201 : rankBlock 201 50 = [209, 221, 247] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock251 : rankBlock 251 50 = [253, 289, 299] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock301 : rankBlock 301 50 = [319, 323, 341] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock351 : rankBlock 351 50 = [361, 377, 391] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock401 : rankBlock 401 50 = [403, 407, 437] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock451 : rankBlock 451 50 = [451, 473, 481, 493] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock501 : rankBlock 501 50 = [517, 527, 529, 533] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock551 : rankBlock 551 50 = [551, 559, 583, 589] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock601 : rankBlock 601 50 = [611, 629, 649] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock651 : rankBlock 651 50 = [667, 671, 689, 697] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock701 : rankBlock 701 50 = [703, 713, 731, 737] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock751 : rankBlock 751 50 = [767, 779, 781, 793, 799] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock801 : rankBlock 801 50 = [803, 817, 841] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock851 : rankBlock 851 50 = [851, 869, 871, 893, 899] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock901 : rankBlock 901 50 = [901, 913, 923, 943, 949] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock951 : rankBlock 951 50 = [961, 979, 989] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1001 : rankBlock 1001 50 = [1003, 1007, 1027, 1037] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1051 : rankBlock 1051 50 = [1067, 1073, 1079, 1081] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1101 : rankBlock 1101 50 = [1111, 1121, 1133, 1139, 1147] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1151 : rankBlock 1151 50 = [1157, 1159, 1177, 1189, 1199] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1201 : rankBlock 1201 50 = [1207, 1219, 1241, 1243, 1247] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1251 : rankBlock 1251 50 = [1261, 1271, 1273] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1301 : rankBlock 1301 50 = [1313, 1331, 1333, 1339, 1343, 1349] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1351 : rankBlock 1351 50 = [1357, 1363, 1369, 1387, 1391, 1397] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1401 : rankBlock 1401 50 = [1403, 1411, 1417, 1441] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1451 : rankBlock 1451 50 = [1457, 1469] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1501 : rankBlock 1501 50 = [1501, 1507, 1513, 1517, 1529, 1537, 1541] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1551 : rankBlock 1551 50 = [1573, 1577, 1591] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1601 : rankBlock 1601 50 = [1633, 1639, 1643, 1649] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1651 : rankBlock 1651 50 = [1651, 1661, 1679, 1681, 1691] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1701 : rankBlock 1701 50 = [1703, 1711, 1717, 1727, 1739] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1751 : rankBlock 1751 50 = [1751, 1763, 1769, 1781, 1793] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1801 : rankBlock 1801 50 = [1807, 1817, 1819, 1829, 1837, 1843, 1849] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1851 : rankBlock 1851 50 = [1853, 1859, 1891] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1901 : rankBlock 1901 50 = [1903, 1909, 1919, 1921, 1927, 1937, 1943] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock1951 : rankBlock 1951 50 = [1957, 1961, 1963, 1969, 1991] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2001 : rankBlock 2001 50 = [2021, 2033, 2041, 2047] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2051 : rankBlock 2051 50 = [2057, 2059, 2071, 2077] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2101 : rankBlock 2101 50 = [2101, 2117, 2119, 2123, 2147] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2151 : rankBlock 2151 50 = [2159, 2167, 2171, 2173, 2183, 2189, 2197] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2201 : rankBlock 2201 50 = [2201, 2209, 2227, 2231, 2249] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2251 : rankBlock 2251 50 = [2257, 2263, 2279, 2291, 2299] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2301 : rankBlock 2301 50 = [2321, 2323, 2327, 2329] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2351 : rankBlock 2351 50 = [2353, 2363, 2369] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2401 : rankBlock 2401 50 = [2407, 2413, 2419, 2431, 2449] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2451 : rankBlock 2451 50 = [2453, 2461, 2479, 2483, 2489, 2491, 2497] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2501 : rankBlock 2501 50 = [2501, 2507, 2509, 2519, 2533, 2537] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2551 : rankBlock 2551 50 = [2561, 2563, 2567, 2573, 2581, 2587, 2599] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2601 : rankBlock 2601 50 = [2603, 2623, 2627, 2629, 2641] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2651 : rankBlock 2651 50 = [2651, 2669] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2701 : rankBlock 2701 50 = [2701, 2717, 2743, 2747] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2751 : rankBlock 2751 50 = [2759, 2761, 2771, 2773, 2783] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2801 : rankBlock 2801 50 = [2809, 2813, 2827, 2831, 2839] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2851 : rankBlock 2851 50 = [2867, 2869, 2873, 2881, 2893, 2899] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2901 : rankBlock 2901 50 = [2911, 2921, 2923, 2929, 2941] := by decide
set_option maxRecDepth 12000 in
private theorem rankBlock2951 : rankBlock 2951 50 = [2951, 2959, 2977, 2981, 2983, 2987, 2993] := by decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
theorem rank_cost : envOKAt 3000 rankEnv = true := by
  have eqn : rankEnv = rankBlock 1 3000 := by
    unfold rankEnv rankBlock
    apply List.filter_congr
    intro d hd
    have hb := List.mem_range'_1.mp hd
    rw [rankComposite_eq d (by omega), Bool.and_comm]
  have blocks : rankBlock 1 3000 = [
    1, 11, 13, 17, 19, 23, 29, 37, 121, 143, 169, 187, 209, 221, 247,
    253, 289, 299, 319, 323, 341, 361, 377, 391, 403, 407, 437, 451, 473, 481,
    493, 517, 527, 529, 533, 551, 559, 583, 589, 611, 629, 649, 667, 671, 689,
    697, 703, 713, 731, 737, 767, 779, 781, 793, 799, 803, 817, 841, 851, 869,
    871, 893, 899, 901, 913, 923, 943, 949, 961, 979, 989, 1003, 1007, 1027, 1037,
    1067, 1073, 1079, 1081, 1111, 1121, 1133, 1139, 1147, 1157, 1159, 1177, 1189, 1199, 1207,
    1219, 1241, 1243, 1247, 1261, 1271, 1273, 1313, 1331, 1333, 1339, 1343, 1349, 1357, 1363,
    1369, 1387, 1391, 1397, 1403, 1411, 1417, 1441, 1457, 1469, 1501, 1507, 1513, 1517, 1529,
    1537, 1541, 1573, 1577, 1591, 1633, 1639, 1643, 1649, 1651, 1661, 1679, 1681, 1691, 1703,
    1711, 1717, 1727, 1739, 1751, 1763, 1769, 1781, 1793, 1807, 1817, 1819, 1829, 1837, 1843,
    1849, 1853, 1859, 1891, 1903, 1909, 1919, 1921, 1927, 1937, 1943, 1957, 1961, 1963, 1969,
    1991, 2021, 2033, 2041, 2047, 2057, 2059, 2071, 2077, 2101, 2117, 2119, 2123, 2147, 2159,
    2167, 2171, 2173, 2183, 2189, 2197, 2201, 2209, 2227, 2231, 2249, 2257, 2263, 2279, 2291,
    2299, 2321, 2323, 2327, 2329, 2353, 2363, 2369, 2407, 2413, 2419, 2431, 2449, 2453, 2461,
    2479, 2483, 2489, 2491, 2497, 2501, 2507, 2509, 2519, 2533, 2537, 2561, 2563, 2567, 2573,
    2581, 2587, 2599, 2603, 2623, 2627, 2629, 2641, 2651, 2669, 2701, 2717, 2743, 2747, 2759,
    2761, 2771, 2773, 2783, 2809, 2813, 2827, 2831, 2839, 2867, 2869, 2873, 2881, 2893, 2899,
    2911, 2921, 2923, 2929, 2941, 2951, 2959, 2977, 2981, 2983, 2987, 2993] := (rankBlock_append (rankBlock_append (rankBlock_append (rankBlock_append (rankBlock_append rankBlock1 (rankBlock_append rankBlock51 rankBlock101)) (rankBlock_append (rankBlock_append rankBlock151 rankBlock201) (rankBlock_append rankBlock251 rankBlock301))) (rankBlock_append (rankBlock_append (rankBlock_append rankBlock351 rankBlock401) (rankBlock_append rankBlock451 rankBlock501)) (rankBlock_append (rankBlock_append rankBlock551 rankBlock601) (rankBlock_append rankBlock651 rankBlock701)))) (rankBlock_append (rankBlock_append (rankBlock_append rankBlock751 (rankBlock_append rankBlock801 rankBlock851)) (rankBlock_append (rankBlock_append rankBlock901 rankBlock951) (rankBlock_append rankBlock1001 rankBlock1051))) (rankBlock_append (rankBlock_append (rankBlock_append rankBlock1101 rankBlock1151) (rankBlock_append rankBlock1201 rankBlock1251)) (rankBlock_append (rankBlock_append rankBlock1301 rankBlock1351) (rankBlock_append rankBlock1401 rankBlock1451))))) (rankBlock_append (rankBlock_append (rankBlock_append (rankBlock_append rankBlock1501 (rankBlock_append rankBlock1551 rankBlock1601)) (rankBlock_append (rankBlock_append rankBlock1651 rankBlock1701) (rankBlock_append rankBlock1751 rankBlock1801))) (rankBlock_append (rankBlock_append (rankBlock_append rankBlock1851 rankBlock1901) (rankBlock_append rankBlock1951 rankBlock2001)) (rankBlock_append (rankBlock_append rankBlock2051 rankBlock2101) (rankBlock_append rankBlock2151 rankBlock2201)))) (rankBlock_append (rankBlock_append (rankBlock_append rankBlock2251 (rankBlock_append rankBlock2301 rankBlock2351)) (rankBlock_append (rankBlock_append rankBlock2401 rankBlock2451) (rankBlock_append rankBlock2501 rankBlock2551))) (rankBlock_append (rankBlock_append (rankBlock_append rankBlock2601 rankBlock2651) (rankBlock_append rankBlock2701 rankBlock2751)) (rankBlock_append (rankBlock_append rankBlock2801 rankBlock2851) (rankBlock_append rankBlock2901 rankBlock2951))))))
  rw [eqn, blocks]
  decide

end A251758Proof

namespace A251758Proof

private def smallPrs : Finset ℕ := {11,13,17,19,23,29,31}
private def modelPrs : Finset ℕ := {11,13,17,19,23,29,37}

private theorem shortCap : ∀ t : Fin 37, ∀ p ∈ smallPrs,
    ((smallPrs.erase p).filter (· ≤ t.val)).card ≤ (modelPrs.filter (· ≤ t.val)).card := by
  decide

private theorem modelPrime (p : ℕ) (hp : p ∈ modelPrs) :
    p.Prime ∧ p ∈ [1,11,13,17,19,23,29,37] ∧ 0 < p ∧ p ≤ 37 := by
  have h : ∀ q ∈ modelPrs, q.Prime ∧ q ∈ [1,11,13,17,19,23,29,37] ∧
      0 < q ∧ q ≤ 37 := by decide
  exact h p hp

theorem rank_dominance {n : ℕ} (hn : 2 ≤ n) (hm : n < 35336848261)
    (hr : ∀ p ∈ [2,3,5,7], ¬ p ∣ n)
    (missing : ∃ p ∈ [11,13,17,19,23,29,31], ¬ p ∣ n)
    (t : ℕ) (ht : t < 3001) : rankCount (ds n) t ≤ rankCount rankEnv t := by
  have hn0 : 0 < n := by omega
  let a := ((ds n).filter (· ≤ t)).toFinset
  let b := (rankEnv.filter (· ≤ t)).toFinset
  have ha (x : ℕ) : x ∈ a ↔ x ∣ n ∧ x ≤ t := by
    simp [a, mem_ds hn0]
  have hb (x : ℕ) : x ∈ b ↔ x ∈ rankEnv ∧ x ≤ t := by simp [b]
  have hb0 {x : ℕ} (hxp : 0 < x) (hxt : x ≤ t)
      (h : x ∈ [1,11,13,17,19,23,29,37] ∨
        (¬x.Prime ∧ ∀ p ∈ [2,3,5,7], ¬p ∣ x)) : x ∈ b := by
    apply (hb x).mpr
    refine ⟨List.mem_filter.mpr ⟨List.mem_range'_1.mpr (by omega), ?_⟩,hxt⟩
    simp only [Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.and_eq_true_eq_eq_true_and_eq_true,
      decide_eq_true_eq, List.all_eq_true, bne_iff_ne]
    rcases h with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, fun p hp hz => h' p hp (Nat.dvd_iff_mod_eq_zero.mpr hz)⟩
  have non : (a.filter (fun x => ¬ x.Prime)).card ≤ (b.filter (fun x => ¬ x.Prime)).card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxa,hp⟩ := Finset.mem_filter.mp hx
    obtain ⟨hd,hxt⟩ := (ha x).mp hxa
    exact Finset.mem_filter.mpr ⟨hb0 (Nat.pos_of_dvd_of_pos hd hn0) hxt
      (Or.inr ⟨hp,fun p hp hpx => hr p hp (dvd_trans hpx hd)⟩),hp⟩
  have lower : (modelPrs.filter (· ≤ t)).card ≤ (b.filter Nat.Prime).card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hp,hxt⟩ := Finset.mem_filter.mp hx
    obtain ⟨prime, hlist, pos, _⟩ := modelPrime x hp
    exact Finset.mem_filter.mpr ⟨hb0 pos hxt (Or.inl hlist), prime⟩
  have rough (p : ℕ) (hp : p.Prime) (hd : p ∣ n) : 11 ≤ p := by
    by_contra! h
    have hsm : ∀ q : Fin 11, q.val.Prime → q.val ∈ [2,3,5,7] := by decide
    exact hr p (hsm ⟨p,h⟩ hp) hd
  have prime : (a.filter Nat.Prime).card ≤ (b.filter Nat.Prime).card := by
    apply le_trans _ lower
    by_cases h : t < 37
    · obtain ⟨p, hp, hpd⟩ := missing
      have hmem : p ∈ smallPrs := by simpa [smallPrs] using hp
      apply le_trans _ (shortCap ⟨t,h⟩ p hmem)
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxa, hprime⟩ := Finset.mem_filter.mp hx
      obtain ⟨hd, hxt⟩ := (ha x).mp hxa
      have hsm : ∀ q : Fin 37, q.val.Prime → 11 ≤ q.val → q.val ∈ smallPrs := by decide
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun heq => hpd (heq ▸ hd),
        hsm ⟨x,by omega⟩ hprime (rough _ hprime hd)⟩, hxt⟩
    · have hfull : modelPrs.filter (· ≤ t) = modelPrs := Finset.filter_true_of_mem
        (fun p hp => (modelPrime p hp).2.2.2.trans (by omega))
      rw [hfull, show modelPrs.card = 7 by decide]
      apply le_trans _ (A251758Compression.sevenFactors hn0 hm (fun p hp =>
        rough p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)))
      apply Finset.card_le_card
      intro p hp
      obtain ⟨hpa, hprime⟩ := Finset.mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨hprime, ((ha p).mp hpa).1, hn0.ne'⟩
  have ac := Finset.card_filter_add_card_filter_not (s := a) Nat.Prime
  have bc := Finset.card_filter_add_card_filter_not (s := b) Nat.Prime
  have alen : a.card = rankCount (ds n) t :=
    List.toFinset_card_of_nodup (((ds_sorted n).imp (fun h => Nat.ne_of_lt h)).filter _)
  have sorted : rankEnv.Pairwise (· < ·) := (List.pairwise_lt_range' _ (by decide)).filter _
  have blen : b.card = rankCount rankEnv t :=
    List.toFinset_card_of_nodup ((sorted.imp (fun h => Nat.ne_of_lt h)).filter _)
  omega

end A251758Proof

namespace A251758Proof

theorem missing_bound {n : ℕ} (hn : 2 ≤ n) (hm : n < 35336848261)
    (hr : ∀ p ∈ [2,3,5,7], ¬ p ∣ n)
    (missing : ∃ p ∈ [11,13,17,19,23,29,31], ¬ p ∣ n) : recip (ds n) ≤ 1/9 := by
  have hn0 : 0 < n := by omega
  have hs : rankEnv.Pairwise (· < ·) := (List.pairwise_lt_range' _ (by decide)).filter _
  have hb (x : ℕ) (hx : x ∈ rankEnv) : 0 < x ∧ x < 3001 := by
    have := List.mem_range'_1.mp (List.mem_filter.mp hx).1
    omega
  have h1 : 1 ∈ rankEnv := List.mem_filter.mpr ⟨List.mem_range'_1.mpr (by decide), by decide⟩
  have hd := rank_divisor_bound hn0 (hr 2 (by decide)) (by decide : 0 < 3001) hs hb h1
    (fun t ht => (rankCount_ds hn0 t) ▸ rank_dominance hn hm hr missing t ht)
  exact hd.trans (envOKAt_sound 3000 rankEnv (fun x hx => (hb x hx).1) rank_cost)

end A251758Proof

namespace A251758Proof

private def sevenCover : List ℕ :=
  [1, 11, 13, 17, 19, 23, 29, 31, 121, 143, 169, 187, 209, 221, 247, 253, 289, 299, 319, 323,
   341, 361, 377, 391, 403, 437, 493, 527, 529, 551, 589, 667, 713, 841, 899, 961, 1573, 1859,
   2057, 2299, 2431, 2717, 2783, 2873, 3179, 3211, 3289, 3509, 3553, 3751, 3757, 3887, 3971,
   4147, 4199, 4301, 4433, 4693, 4807, 4901, 5083, 5239, 5423, 5491, 5681, 5797, 5819, 6061,
   6137, 6409, 6479, 6647, 6851, 6877]

private theorem seven_square {n : ℕ} (hn : n < 35336848261)
    (hr : ∀ p ∈ [2,3,5,7], ¬ p ∣ n) (hall : ∀ p ∈ [11,13,17,19,23,29,31], p ∣ n) :
    n ∣ 955049953^2 := by
  have hd : 955049953 ∣ n := Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd
    (Nat.lcm_dvd (Nat.lcm_dvd (hall 11 (by decide)) (hall 13 (by decide)))
    (hall 17 (by decide))) (hall 19 (by decide))) (hall 23 (by decide)))
    (hall 29 (by decide))) (hall 31 (by decide))
  obtain ⟨t,rfl⟩ := hd
  have ht : t < 37 := by omega
  have cert : ∀ s : Fin 37, ¬ 2 ∣ s.val → ¬ 3 ∣ s.val →
      ¬ 5 ∣ s.val → ¬ 7 ∣ s.val → s.val ∣ 955049953 := by decide
  have h (p : ℕ) (hp : p ∈ [2,3,5,7]) : ¬ p ∣ t :=
    fun h => hr p hp (dvd_mul_of_dvd_right h _)
  have hs := cert ⟨t,ht⟩ (h 2 (by decide)) (h 3 (by decide)) (h 5 (by decide)) (h 7 (by decide))
  simpa [pow_two] using Nat.mul_dvd_mul_left 955049953 hs

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem seven_incl : ∀ x : Fin 7001, x.val ∣ 955049953^2 → x.val ∈ sevenCover := by
  have blocks (i : Fin 70) : ∀ j : Fin 100,
      (100*i.val+j.val+1) ∣ 955049953^2 → (100*i.val+j.val+1) ∈ sevenCover := by
    fin_cases i <;> decide
  intro x hd
  have hx := x.isLt
  have hpos : 0 < x.val := Nat.pos_of_dvd_of_pos hd (by decide)
  let i : Fin 70 := ⟨(x.val-1)/100, by omega⟩
  let j : Fin 100 := ⟨(x.val-1)%100, Nat.mod_lt _ (by decide)⟩
  have he : 100*i.val+j.val+1 = x.val := by dsimp [i,j]; omega
  simpa only [he] using blocks i j (he ▸ hd)

theorem all_seven_bound {n : ℕ} (hn : 2 ≤ n) (hm : n < 35336848261)
    (hr : ∀ p ∈ [2,3,5,7], ¬ p ∣ n) (hall : ∀ p ∈ [11,13,17,19,23,29,31], p ∣ n) :
    recip (ds n) ≤ 1/9 := by
  have hd := seven_square hm hr hall
  have posBound : sevenCover.all (fun x => decide (0 < x ∧ x ≤ 7000)) = true := by decide
  have hs : sevenCover.Pairwise (· < ·) := by decide
  have hp : ∀ x ∈ sevenCover, 0 < x ∧ x ≤ 7000 := by simpa using List.all_eq_true.mp posBound
  have hi := envelope_bounds hn (hr 2 (by decide)) (by decide : 0 < 7000) hs hp
    (fun x _ hx h => seven_incl ⟨x, by omega⟩ (dvd_trans h hd))
  exact hi.trans (envOKAt_sound 7000 sevenCover (fun x hx => (hp x hx).1) (by decide))

end A251758Proof

open A251758Proof in
theorem OMA.solution : type_of% @OeisA251758.conjecture := by
  rw [A251758Candidate.primorial_value]
  refine ⟨⟨by decide, A251758Candidate.candidate_value⟩, ?_⟩
  intro n hn
  obtain ⟨hn, hval⟩ := hn
  by_contra! hlt
  have hr : ∀ p ∈ [2,3,5,7], ¬ p ∣ n := by
    intro p hp hd
    have hp' : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by simpa using hp
    exact small_excluded hn (by omega) (by omega) hd hval

  have bound : recip (ds n) ≤ 1/9 := by
    by_cases hall : ∀ p ∈ [11,13,17,19,23,29,31], p ∣ n
    · exact all_seven_bound hn hlt hr hall
    · push_neg at hall
      exact missing_bound hn hlt hr hall
  exact (not_lt_of_ge bound) (bounds_of_eight hn hval).1
