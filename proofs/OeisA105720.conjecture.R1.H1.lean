import OMAReductions.R_OeisA105720_conjecture_R1

-- Step OeisA105720.conjecture.R1.H1
-- Credit: @caa1982

open Nat Finset

private def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
   79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163,
   167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
   257, 263, 269, 271, 277, 281, 283]

private def checkDivs (n : ℕ) : List ℕ → Bool
  | [] => true
  | p :: ps =>
    if p * p > n then true
    else if n % p == 0 then false
    else checkDivs n ps

private def isPrimeFast (n : ℕ) : Bool :=
  if n < 2 then false else checkDivs n smallPrimes

private lemma smallPrimes_spec :
    smallPrimes.Pairwise (· ≤ ·) ∧
    (∀ p ∈ smallPrimes, p.Prime) ∧
    (∀ p : ℕ, p < 289 → p.Prime → p ∈ smallPrimes) := by
  decide +kernel

private lemma checkDivs_true_iff (n : ℕ) (ps : List ℕ) (hsort : ps.Pairwise (· ≤ ·)) :
    checkDivs n ps = true ↔ ∀ p ∈ ps, p * p ≤ n → ¬ p ∣ n := by
  induction ps with
  | nil => simp [checkDivs]
  | cons p ps ih =>
    have ⟨hp_le, hps_sort⟩ := List.pairwise_cons.mp hsort
    unfold checkDivs
    split_ifs with h1 h2
    · constructor
      · intro _ q hq hqle
        rcases List.mem_cons.mp hq with rfl | hq'
        · omega
        · have hpq : p ≤ q := hp_le q hq'
          have : p * p ≤ q * q := Nat.mul_le_mul hpq hpq
          omega
      · intro _; rfl
    · simp only [beq_iff_eq] at h2
      have hdvd : p ∣ n := Nat.dvd_of_mod_eq_zero h2
      constructor
      · intro h; exact h.elim
      · intro hall; exact (hall p (List.mem_cons_self ..) (by omega) hdvd).elim
    · simp only [beq_iff_eq] at h2
      have hndvd : ¬ p ∣ n := fun h => h2 (Nat.mod_eq_zero_of_dvd h)
      rw [ih hps_sort]
      constructor
      · intro hall q hq hqle
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact hndvd
        · exact hall q hq' hqle
      · intro hall q hq' hqle
        exact hall q (List.mem_cons_of_mem p hq') hqle

private lemma isPrimeFast_iff {n : ℕ} (hn : n < 83521) :
    isPrimeFast n = true ↔ n.Prime := by
  unfold isPrimeFast
  split_ifs with hlt
  · constructor
    · intro h; exact h.elim
    · intro hp; have := hp.two_le; omega
  · rw [checkDivs_true_iff n smallPrimes smallPrimes_spec.1]
    constructor
    · intro hall
      by_contra hnp
      set p := n.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpdvd : p ∣ n := Nat.minFac_dvd n
      have hpsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
      have hp_lt : p < 289 := by nlinarith
      have hpmem : p ∈ smallPrimes := smallPrimes_spec.2.2 p hp_lt hp
      exact hall p hpmem (by nlinarith) hpdvd
    · intro hp q hq hqle hdvd
      have hqp : q.Prime := smallPrimes_spec.2.1 q hq
      rcases hp.eq_one_or_self_of_dvd q hdvd with h1 | hself
      · exact hqp.ne_one h1
      · have := hqp.two_le; nlinarith

private def countRange (lo len : ℕ) : ℕ :=
  let rec go (k rem acc : ℕ) : ℕ :=
    match rem with
    | 0 => acc
    | r + 1 => go (k + 1) r (if isPrimeFast k then acc + 1 else acc)
  go lo len 0

private def sumRange (lo len : ℕ) : ℕ :=
  let rec go (k rem acc : ℕ) : ℕ :=
    match rem with
    | 0 => acc
    | r + 1 => go (k + 1) r (if isPrimeFast k then acc + k else acc)
  go lo len 0

private lemma countRange_go_eq (k rem acc : ℕ) :
    countRange.go k rem acc = acc + ((Finset.Ico k (k + rem)).filter (fun x => isPrimeFast x = true)).card := by
  induction rem generalizing k acc with
  | zero => simp [countRange.go]
  | succ r ih =>
    unfold countRange.go
    rw [ih (k + 1)]
    have hset : Finset.Ico k (k + (r + 1)) = insert k (Finset.Ico (k + 1) (k + 1 + r)) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hnot : k ∉ Finset.Ico (k + 1) (k + 1 + r) := by simp
    rw [hset, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (fun hm => hnot (Finset.mem_filter.mp hm).1)]
      omega
    · rfl

private lemma countRange_eq (lo hi : ℕ) (hle : lo ≤ hi) :
    countRange lo (hi - lo) = ((Finset.Ico lo hi).filter (fun x => isPrimeFast x = true)).card := by
  unfold countRange
  rw [countRange_go_eq, Nat.add_sub_cancel' hle, zero_add]

private lemma sumRange_go_eq (k rem acc : ℕ) :
    sumRange.go k rem acc = acc + ∑ x ∈ (Finset.Ico k (k + rem)).filter (fun x => isPrimeFast x = true), x := by
  induction rem generalizing k acc with
  | zero => simp [sumRange.go]
  | succ r ih =>
    unfold sumRange.go
    rw [ih (k + 1)]
    have hset : Finset.Ico k (k + (r + 1)) = insert k (Finset.Ico (k + 1) (k + 1 + r)) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hnot : k ∉ Finset.Ico (k + 1) (k + 1 + r) := by simp
    rw [hset, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.sum_insert (fun hm => hnot (Finset.mem_filter.mp hm).1)]
      omega
    · rfl

private lemma sumRange_eq (lo hi : ℕ) (hle : lo ≤ hi) :
    sumRange lo (hi - lo) = ∑ x ∈ (Finset.Ico lo hi).filter (fun x => isPrimeFast x = true), x := by
  unfold sumRange
  rw [sumRange_go_eq, Nat.add_sub_cancel' hle, zero_add]

private lemma count_Ico_add {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ((Finset.Ico a c).filter (fun x => isPrimeFast x = true)).card =
    ((Finset.Ico a b).filter (fun x => isPrimeFast x = true)).card +
    ((Finset.Ico b c).filter (fun x => isPrimeFast x = true)).card := by
  have hunion : Finset.Ico a b ∪ Finset.Ico b c = Finset.Ico a c := by
    ext x; simp only [Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.Ico a b) (Finset.Ico b c) := by
    rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
  rw [← hunion, Finset.filter_union, Finset.card_union_of_disjoint
    (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

private lemma sum_Ico_add {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ x ∈ (Finset.Ico a c).filter (fun x => isPrimeFast x = true), x =
    ∑ x ∈ (Finset.Ico a b).filter (fun x => isPrimeFast x = true), x +
    ∑ x ∈ (Finset.Ico b c).filter (fun x => isPrimeFast x = true), x := by
  have hunion : Finset.Ico a b ∪ Finset.Ico b c = Finset.Ico a c := by
    ext x; simp only [Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.Ico a b) (Finset.Ico b c) := by
    rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
  rw [← hunion, Finset.filter_union, Finset.sum_union
    (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

private lemma nat_count_eq_filter_card {B : ℕ} (hB : B ≤ 83521) :
    Nat.count Nat.Prime B = ((Finset.Ico 0 B).filter (fun x => isPrimeFast x = true)).card := by
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Nat.zero_le, true_and]
  constructor
  · rintro ⟨hx, hp⟩; exact ⟨hx, (isPrimeFast_iff (by omega)).mpr hp⟩
  · rintro ⟨hx, hf⟩; exact ⟨hx, (isPrimeFast_iff (by omega)).mp hf⟩

private lemma sum_nth_prime_eq {lo hi A B : ℕ} (hAB : A ≤ B) (hB : B ≤ 83521)
    (hA : Nat.count Nat.Prime A = lo) (hBc : Nat.count Nat.Prime B = hi) :
    ∑ i ∈ Finset.Ico lo hi, Nat.nth Nat.Prime i =
      ∑ p ∈ (Finset.Ico A B).filter (fun x => isPrimeFast x = true), p := by
  refine Finset.sum_bij (fun i _ => Nat.nth Nat.Prime i) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i hi_mem
    simp only [Finset.mem_Ico] at hi_mem
    have hp : (Nat.nth Nat.Prime i).Prime := Nat.prime_nth_prime i
    have hltB : Nat.nth Nat.Prime i < B := by
      rw [← hBc] at hi_mem
      exact Nat.nth_lt_of_lt_count hi_mem.2
    have hgeA : A ≤ Nat.nth Nat.Prime i := by
      by_contra hltA
      push Not at hltA
      have hc : Nat.count Nat.Prime (Nat.nth Nat.Prime i) < Nat.count Nat.Prime A :=
        Nat.count_strict_mono hp hltA
      rw [Nat.count_nth_of_infinite Nat.infinite_setOf_prime, hA] at hc
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hgeA, hltB⟩,
      (isPrimeFast_iff (by omega)).mpr hp⟩
  · intro i _ j _ heq
    exact Nat.nth_injective Nat.infinite_setOf_prime heq
  · intro p hp_mem
    have hp_ico := Finset.mem_Ico.mp (Finset.mem_filter.mp hp_mem).1
    have hp : p.Prime := (isPrimeFast_iff (by omega)).mp (Finset.mem_filter.mp hp_mem).2
    refine ⟨Nat.count Nat.Prime p, Finset.mem_Ico.mpr ⟨?_, ?_⟩, Nat.nth_count hp⟩
    · rw [← hA]; exact Nat.count_monotone Nat.Prime hp_ico.1
    · rw [← hBc]; exact Nat.count_strict_mono hp hp_ico.2

set_option maxHeartbeats 800000 in
private lemma c1 : countRange 0 13000 = 1547 := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma c2 : countRange 13000 13000 = 1313 := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma c3 : countRange 26000 12653 = 1211 := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma c4 : countRange 38653 11347 = 1062 := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma c5 : countRange 50000 12000 = 1099 := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma c6 : countRange 62000 11000 = 986 := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma c7 : countRange 73000 10424 = 926 := by decide +kernel

set_option maxHeartbeats 800000 in
private lemma s4 : sumRange 38653 11347 = 47031728 := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma s5 : sumRange 50000 12000 = 61510801 := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma s6 : sumRange 62000 11000 = 66595726 := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma s7 : sumRange 73000 10424 = 72451970 := by decide +kernel

private lemma count_38653 : Nat.count Nat.Prime 38653 = 4071 := by
  rw [nat_count_eq_filter_card (by omega),
    count_Ico_add (by omega : 0 ≤ 26000) (by omega : 26000 ≤ 38653),
    count_Ico_add (by omega : 0 ≤ 13000) (by omega : 13000 ≤ 26000)]
  have h1 := countRange_eq 0 13000 (by omega)
  have h2 := countRange_eq 13000 26000 (by omega)
  have h3 := countRange_eq 26000 38653 (by omega)
  rw [c1] at h1; rw [c2] at h2; rw [c3] at h3
  omega

private lemma count_83424 : Nat.count Nat.Prime 83424 = 8144 := by
  rw [nat_count_eq_filter_card (by omega),
    count_Ico_add (by omega : 0 ≤ 38653) (by omega : 38653 ≤ 83424),
    ← nat_count_eq_filter_card (by omega), count_38653,
    count_Ico_add (by omega : 38653 ≤ 73000) (by omega : 73000 ≤ 83424),
    count_Ico_add (by omega : 38653 ≤ 62000) (by omega : 62000 ≤ 73000),
    count_Ico_add (by omega : 38653 ≤ 50000) (by omega : 50000 ≤ 62000)]
  have h4 := countRange_eq 38653 50000 (by omega)
  have h5 := countRange_eq 50000 62000 (by omega)
  have h6 := countRange_eq 62000 73000 (by omega)
  have h7 := countRange_eq 73000 83424 (by omega)
  rw [c4] at h4; rw [c5] at h5; rw [c6] at h6; rw [c7] at h7
  omega

private lemma sum_38653_83424 :
    ∑ p ∈ (Finset.Ico 38653 83424).filter (fun x => isPrimeFast x = true), p = 247590225 := by
  rw [sum_Ico_add (by omega : 38653 ≤ 73000) (by omega : 73000 ≤ 83424),
    sum_Ico_add (by omega : 38653 ≤ 62000) (by omega : 62000 ≤ 73000),
    sum_Ico_add (by omega : 38653 ≤ 50000) (by omega : 50000 ≤ 62000)]
  have h4 := sumRange_eq 38653 50000 (by omega)
  have h5 := sumRange_eq 50000 62000 (by omega)
  have h6 := sumRange_eq 62000 73000 (by omega)
  have h7 := sumRange_eq 73000 83424 (by omega)
  rw [s4] at h4; rw [s5] at h5; rw [s6] at h6; rw [s7] at h7
  omega

theorem OMA.solution : OMA.R_OeisA105720_conjecture_R1.H1 := by
  intro n hn
  rcases hn with rfl | rfl | rfl
  · refine ⟨6, ?_⟩
    unfold OeisA105720.a
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
    have hsum : ∑ i ∈ Finset.Ico 2 6, Nat.nth Nat.Prime i =
        ∑ p ∈ (Finset.Ico 5 14).filter (fun x => isPrimeFast x = true), p :=
      sum_nth_prime_eq (by omega) (by omega) (by decide) (by decide)
    rw [show 3 - 1 = 2 by rfl, show 2 * 3 = 6 by rfl, hsum]
    decide +kernel
  · refine ⟨13, ?_⟩
    unfold OeisA105720.a
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
    have hsum : ∑ i ∈ Finset.Ico 5 12, Nat.nth Nat.Prime i =
        ∑ p ∈ (Finset.Ico 13 38).filter (fun x => isPrimeFast x = true), p :=
      sum_nth_prime_eq (by omega) (by omega) (by decide) (by decide)
    rw [show 6 - 1 = 5 by rfl, show 2 * 6 = 12 by rfl, hsum]
    decide +kernel
  · refine ⟨15735, ?_⟩
    unfold OeisA105720.a
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
    have hsum : ∑ i ∈ Finset.Ico 4071 8144, Nat.nth Nat.Prime i =
        ∑ p ∈ (Finset.Ico 38653 83424).filter (fun x => isPrimeFast x = true), p :=
      sum_nth_prime_eq (by omega) (by omega) count_38653 count_83424
    rw [show 4072 - 1 = 4071 by rfl, show 2 * 4072 = 8144 by rfl, hsum, sum_38653_83424]
