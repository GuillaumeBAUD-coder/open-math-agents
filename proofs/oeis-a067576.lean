import OMAStatements.S_oeis_a067576

/-!
Proof that in the array `entry i j` (the `j`-th smallest natural number with `i` set bits),
every column `j+1` satisfies `entry (i+1) (j+1) + 1 = 2 * (entry i (j+1) + 1)` for all
`i ≥ max(1, j)`, and `max(1, j)` is the least such row bound.

The identity `T(i+1, s) = 2*T(i, s) + 1` (with `s = j+1` the 1-based column rank and
`T(i, s) = entry i s`) holds exactly when no number with `i+1` set bits is `≤ T(i, s)`,
i.e. when `T(i, s) < 2^(i+1) - 1`; the latter holds whenever `s ≤ i + 1`, because there
are exactly `i+1` numbers below `2^(i+1)` with `i` set bits.
-/

namespace OMA.S_oeis_a067576

/-- The popcount predicate: `PC c n` iff `n` has exactly `c` set bits. -/
abbrev PC (c : ℕ) : ℕ → Prop := fun a => a.bitIndices.length = c

instance instPC (c : ℕ) : DecidablePred (PC c) :=
  fun a => inferInstanceAs (Decidable (a.bitIndices.length = c))

lemma two_pow_lt : ∀ a b : ℕ, a < b → 2 ^ a < 2 ^ b := by
  intro a b hab
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hab) with heq | hab'
    · rw [heq, Nat.pow_succ]
      have h3 : 0 < 2 ^ b := Nat.pow_pos (by omega)
      omega
    · have h1 := ih hab'
      rw [Nat.pow_succ]
      have h3 : 0 < 2 ^ b := Nat.pow_pos (by omega)
      omega

lemma two_pow_inj {a b : ℕ} (h : 2 ^ a = 2 ^ b) : a = b := by
  rcases lt_trichotomy a b with h' | h' | h'
  · exact absurd h (by have := two_pow_lt a b h'; omega)
  · exact h'
  · exact absurd h.symm (by have := two_pow_lt b a h'; omega)

lemma length_two_mul (n : ℕ) : (2 * n).bitIndices.length = n.bitIndices.length := by
  rw [Nat.bitIndices_two_mul, List.length_map]

lemma length_two_mul_add_one (n : ℕ) :
    (2 * n + 1).bitIndices.length = n.bitIndices.length + 1 := by
  rw [Nat.bitIndices_two_mul_add_one]
  simp [List.length_map]

lemma PC_two_mul {c n : ℕ} : PC c (2 * n) ↔ PC c n := by
  simp only [PC, length_two_mul]

lemma PC_two_mul_add_one {c n : ℕ} (hc : 0 < c) : PC c (2 * n + 1) ↔ PC (c - 1) n := by
  have h1 : (2 * n + 1).bitIndices.length = n.bitIndices.length + 1 := length_two_mul_add_one n
  constructor
  · intro h
    have h2 : (2 * n + 1).bitIndices.length = c := h
    rw [h1] at h2
    omega
  · intro h
    have h2 : n.bitIndices.length = c - 1 := h
    show (2 * n + 1).bitIndices.length = c
    rw [h1]
    omega

/-- `2 ^ c - 1` has exactly `c` set bits. -/
lemma PC_two_pow_sub_one (c : ℕ) : PC c (2 ^ c - 1) := by
  induction c with
  | zero => simp [Nat.bitIndices_zero]
  | succ k ih =>
    have h1 : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
      have h : 2 * (2 ^ k - 1) + 2 = 2 ^ (k + 1) := by
        have e1 : 2 * (2 ^ k - 1) + 2 = 2 * ((2 ^ k - 1) + 1) := by ring
        rw [e1]
        have h1' : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        rw [Nat.sub_add_cancel h1', Nat.pow_succ]
        ring
      omega
    have h2 : (2 ^ k - 1).bitIndices.length = k := ih
    show (2 ^ (k + 1) - 1).bitIndices.length = k + 1
    rw [h1, length_two_mul_add_one, h2]

/-- A number with `c` set bits is at least `2 ^ c - 1`. -/
lemma PC_ge : ∀ (n c : ℕ), PC c n → 2 ^ c - 1 ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro c h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : ([] : List ℕ).length = c := h
      simp only [List.length_nil] at h0
      subst h0
      simp
    · obtain hpar : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases hpar with hpar | hpar
      · have hdef : n = 2 * (n / 2) := by omega
        have h' : PC c (n / 2) := by
          have hpc : PC c (2 * (n / 2)) := by rw [← hdef]; exact h
          exact PC_two_mul.1 hpc
        have h2 := ih (n / 2) (by omega) c h'
        rw [hdef]
        omega
      · have hdef : n = 2 * (n / 2) + 1 := by omega
        have hc1 : 0 < c := by
          have hpc : PC c (2 * (n / 2) + 1) := by rw [← hdef]; exact h
          have hthis : (2 * (n / 2) + 1).bitIndices.length = c := hpc
          have hlen : (2 * (n / 2) + 1).bitIndices.length = (n / 2).bitIndices.length + 1 :=
            length_two_mul_add_one _
          omega
        have hpcm : PC (c - 1) (n / 2) := by
          refine (PC_two_mul_add_one hc1).1 ?_
          rw [← hdef]
          exact h
        have h2 := ih (n / 2) (by omega) (c - 1) hpcm
        have hpow : 2 ^ c = 2 * 2 ^ (c - 1) := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (show c ≠ 0 by omega)
          subst hk
          have e : k.succ - 1 = k := by simp
          rw [Nat.pow_succ, e]
          ring
        rw [hdef]
        omega

/-- The popcount-`c` numbers are infinite for `c ≥ 1`. -/
lemma infinite_PC (c : ℕ) (hc : 0 < c) : {n | PC c n}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 ^ (k + 1) * (2 ^ c - 1)) ?_ ?_
  · intro a b hab
    simp only at hab
    have hpos : 0 < 2 ^ c - 1 := by
      have h2 : 1 < 2 ^ c := two_pow_lt 0 c (by omega)
      omega
    have h1 : 2 ^ (a + 1) = 2 ^ (b + 1) := by
      refine Nat.eq_of_mul_eq_mul_left hpos ?_
      rw [mul_comm (2 ^ (a + 1)), mul_comm (2 ^ (b + 1))] at hab
      exact hab
    have := two_pow_inj h1
    omega
  · intro k
    have h1 : PC c (2 ^ c - 1) := PC_two_pow_sub_one c
    have h2 : (2 ^ c - 1).bitIndices.length = c := h1
    show (2 ^ (k + 1) * (2 ^ c - 1)).bitIndices.length = c
    rw [Nat.bitIndices_two_pow_mul, List.length_map]
    exact h2

/-- Splitting `range (2 * M)` into even and odd parts. -/
lemma fin_range_split_mul (M : ℕ) :
    Finset.range (2 * M) =
      (Finset.range M).image (fun m => 2 * m) ∪ (Finset.range M).image (fun m => 2 * m + 1) := by
  ext k
  simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
  constructor
  · intro hk
    obtain h1 : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases h1 with h1 | h1
    · exact Or.inl ⟨k / 2, by have := Nat.div_add_mod k 2; omega,
        by have := Nat.div_add_mod k 2; omega⟩
    · exact Or.inr ⟨k / 2, by have := Nat.div_add_mod k 2; omega,
        by have := Nat.div_add_mod k 2; omega⟩
  · rintro (⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
    · omega
    · omega

/-- Splitting `range (2 * M + 1)` into even and odd parts. -/
lemma fin_range_split_mul_add_one (M : ℕ) :
    Finset.range (2 * M + 1) =
      (Finset.range (M + 1)).image (fun m => 2 * m) ∪ (Finset.range M).image (fun m => 2 * m + 1) := by
  ext k
  simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
  constructor
  · intro hk
    obtain h1 : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases h1 with h1 | h1
    · exact Or.inl ⟨k / 2, by have := Nat.div_add_mod k 2; omega,
        by have := Nat.div_add_mod k 2; omega⟩
    · exact Or.inr ⟨k / 2, by have := Nat.div_add_mod k 2; omega,
        by have := Nat.div_add_mod k 2; omega⟩
  · rintro (⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
    · omega
    · omega

lemma card_image_filter {α β : Type} [DecidableEq β] {s : Finset α} {f : α → β}
    (hf : Function.Injective f) (p : β → Prop) [DecidablePred p] :
    ((s.image f).filter p).card = (s.filter fun a => p (f a)).card := by
  have heq : (s.image f).filter p = (s.filter fun a => p (f a)).image f := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_filter, Finset.mem_image] at hx
      obtain ⟨hm, hpx⟩ := hx
      obtain ⟨a, ha, hfx⟩ := hm
      have hpa : p (f a) := by rw [hfx]; exact hpx
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hpa⟩, hfx⟩
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨a, ha, hfx⟩ := hx
      rw [Finset.mem_filter] at ha
      obtain ⟨ha1, ha2⟩ := ha
      have hpx : p x := by rw [← hfx]; exact ha2
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨a, ha1, hfx⟩, hpx⟩
  rw [heq, Finset.card_image_of_injective _ hf]

/-- Two pointwise-equivalent predicates give equal filter cards. -/
lemma card_filter_congr {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] {s : Finset ℕ}
    (h : ∀ x ∈ s, p x ↔ q x) : (s.filter p).card = (s.filter q).card := by
  rw [Finset.filter_congr fun x hx => h x hx]

/-- Counting popcount-`c` numbers below an even bound. -/
lemma count_two_mul (c : ℕ) (hc : 0 < c) (M : ℕ) :
    Nat.count (PC c) (2 * M) = Nat.count (PC c) M + Nat.count (PC (c - 1)) M := by
  have hd : Disjoint (((Finset.range M).image (fun m : ℕ => 2 * m)).filter (PC c))
      (((Finset.range M).image (fun m : ℕ => 2 * m + 1)).filter (PC c)) := by
    rw [Finset.disjoint_left]
    intro a h1 h2
    simp only [Finset.mem_filter, Finset.mem_image] at h1 h2
    obtain ⟨a1, _, h1'⟩ := h1.1
    obtain ⟨a2, _, h2'⟩ := h2.1
    have b1 : (2 * a1 : ℕ) = a := h1'
    have b2 : (2 * a2 + 1 : ℕ) = a := h2'
    omega
  rw [Nat.count_eq_card_filter_range, fin_range_split_mul M, Finset.filter_union,
    Finset.card_union_of_disjoint hd]
  congr 1
  · rw [card_image_filter (fun a b h => Nat.eq_of_mul_eq_mul_left (by omega) h),
      card_filter_congr (fun x _ => PC_two_mul),
      ← Nat.count_eq_card_filter_range]
  · rw [card_image_filter (fun a b h => Nat.eq_of_mul_eq_mul_left (by omega) (Nat.succ.inj h)),
      card_filter_congr (fun x _ => PC_two_mul_add_one hc),
      ← Nat.count_eq_card_filter_range]

/-- Counting popcount-`c` numbers below an odd bound. -/
lemma count_two_mul_add_one (c : ℕ) (hc : 0 < c) (M : ℕ) :
    Nat.count (PC c) (2 * M + 1) = Nat.count (PC c) (M + 1) + Nat.count (PC (c - 1)) M := by
  have hd : Disjoint (((Finset.range (M + 1)).image (fun m : ℕ => 2 * m)).filter (PC c))
      (((Finset.range M).image (fun m : ℕ => 2 * m + 1)).filter (PC c)) := by
    rw [Finset.disjoint_left]
    intro a h1 h2
    simp only [Finset.mem_filter, Finset.mem_image] at h1 h2
    obtain ⟨a1, _, h1'⟩ := h1.1
    obtain ⟨a2, _, h2'⟩ := h2.1
    have b1 : (2 * a1 : ℕ) = a := h1'
    have b2 : (2 * a2 + 1 : ℕ) = a := h2'
    omega
  rw [Nat.count_eq_card_filter_range, fin_range_split_mul_add_one M, Finset.filter_union,
    Finset.card_union_of_disjoint hd]
  congr 1
  · rw [card_image_filter (fun a b h => Nat.eq_of_mul_eq_mul_left (by omega) h),
      card_filter_congr (fun x _ => PC_two_mul),
      ← Nat.count_eq_card_filter_range]
  · rw [card_image_filter (fun a b h => Nat.eq_of_mul_eq_mul_left (by omega) (Nat.succ.inj h)),
      card_filter_congr (fun x _ => PC_two_mul_add_one hc),
      ← Nat.count_eq_card_filter_range]

/-- No popcount-`c` number is strictly below `2 ^ c - 1`. -/
lemma count_PC_two_pow_sub_one (c : ℕ) : Nat.count (PC c) (2 ^ c - 1) = 0 := by
  rw [Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk hpc
  have hk2 : k < 2 ^ c - 1 := Finset.mem_range.mp hk
  have := PC_ge k c hpc
  omega

/-- Exactly one popcount-`i` number lies strictly below `2 ^ i`, namely `2 ^ i - 1`. -/
lemma count_PC_two_pow (i : ℕ) : Nat.count (PC i) (2 ^ i) = 1 := by
  have hp : 0 < 2 ^ i := Nat.pow_pos (by omega)
  have h1 : 2 ^ i = (2 ^ i - 1) + 1 := by omega
  have h2 : PC i (2 ^ i - 1) := PC_two_pow_sub_one i
  have h3 : Nat.count (PC i) (2 ^ i - 1) = 0 := count_PC_two_pow_sub_one i
  rw [h1, Nat.count_succ, if_pos h2, h3]

/-- The number of popcount-`i` values strictly below `2 ^ (i+1)` is `i + 1`. -/
lemma count_PC_two_pow_succ (i : ℕ) : Nat.count (PC i) (2 ^ (i + 1)) = i + 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : 2 ^ (i + 1 + 1) = 2 * 2 ^ (i + 1) := by rw [Nat.pow_succ]; ring
    rw [h1, count_two_mul (i + 1) (by omega) (2 ^ (i + 1))]
    have h2 : Nat.count (PC (i + 1)) (2 ^ (i + 1)) = 1 := count_PC_two_pow (i + 1)
    have h4 : Nat.count (PC ((i + 1) - 1)) (2 ^ (i + 1)) = i + 1 := ih
    rw [h2, h4]
    ring

/-- `entry i (j+1)` is the `j`-th (0-indexed) number with `i` set bits. -/
lemma entry_eq (i j : ℕ) : entry i (j + 1) = Nat.nth (PC i) j := by
  show Nat.nth (fun a => a.bitIndices.length = i) (j + 1 - 1) = _
  rw [Nat.add_sub_cancel]

/-- The doubling identity for row `i ≥ max(1, j)`. -/
lemma entry_succ (j i : ℕ) (hij : max 1 j ≤ i) :
    entry (i + 1) (j + 1) + 1 = 2 * (entry i (j + 1) + 1) := by
  have hi1 : 0 < i := by omega
  have hinj : {n | PC i n}.Infinite := infinite_PC i hi1
  have hinj1 : {n | PC (i + 1) n}.Infinite := infinite_PC (i + 1) (by omega)
  set T := Nat.nth (PC i) j with hT
  have hTdef : entry i (j + 1) = T := entry_eq i j
  have hmem : PC i T := Nat.nth_mem_of_infinite hinj j
  have hcount : Nat.count (PC i) T = j := Nat.count_nth_of_infinite hinj j
  have hlt : T < 2 ^ (i + 1) := by
    refine Nat.nth_lt_of_lt_count (p := PC i) (n := 2 ^ (i + 1)) (k := j) ?_
    have hcs : Nat.count (PC i) (2 ^ (i + 1)) = i + 1 := count_PC_two_pow_succ i
    omega
  have hne : T ≠ 2 ^ (i + 1) - 1 := by
    intro hcon
    have h1 : PC (i + 1) T := by rw [hcon]; exact PC_two_pow_sub_one (i + 1)
    have e1 : T.bitIndices.length = i + 1 := h1
    have e2 : T.bitIndices.length = i := hmem
    omega
  have hT2 : T + 1 ≤ 2 ^ (i + 1) - 1 := by omega
  have h0 : Nat.count (PC (i + 1)) (T + 1) = 0 := by
    refine Nat.le_antisymm ?_ (Nat.zero_le _)
    have h1 : Nat.count (PC (i + 1)) (2 ^ (i + 1) - 1) = 0 := count_PC_two_pow_sub_one (i + 1)
    have h2 := Nat.count_monotone (PC (i + 1)) hT2
    omega
  have hmem2 : PC (i + 1) (2 * T + 1) := by
    show (2 * T + 1).bitIndices.length = i + 1
    have hthis : T.bitIndices.length = i := hmem
    rw [length_two_mul_add_one]
    omega
  have hc2 : Nat.count (PC (i + 1)) (2 * T + 1) = j := by
    have h3 := count_two_mul_add_one (i + 1) (by omega) T
    have h4 : Nat.count (PC ((i + 1) - 1)) T = j := hcount
    omega
  have hnth : Nat.nth (PC (i + 1)) j = 2 * T + 1 := by
    rw [← hc2]
    exact Nat.nth_count hmem2
  rw [entry_eq, hnth, hTdef]
  ring

end OMA.S_oeis_a067576

open OMA.S_oeis_a067576 in
theorem OMA.solution : type_of% @OMA.S_oeis_a067576.main := by
  intro j
  refine ⟨⟨by omega, fun i hi => entry_succ j i hi⟩, ?_⟩
  intro r hr
  obtain ⟨hr1, hr2⟩ := hr
  by_contra hcon
  by_cases hj : j ≤ 1
  · have hmax : max 1 j = 1 := by omega
    omega
  · have hj2 : 2 ≤ j := by omega
    have hmax : max 1 j = j := by omega
    have hrj : r < j := by omega
    have hfail := hr2 (j - 1) (by omega)
    have hinj1 : {n | PC j n}.Infinite := infinite_PC j (by omega)
    set T := Nat.nth (PC (j - 1)) j with hT
    have hmem : PC (j - 1) T := Nat.nth_mem_of_infinite (infinite_PC (j - 1) (by omega)) j
    have hcount : Nat.count (PC (j - 1)) T = j :=
      Nat.count_nth_of_infinite (infinite_PC (j - 1) (by omega)) j
    have hTge : ¬ (T < 2 ^ j) := by
      intro hlt
      have hT1 : Nat.count (PC (j - 1)) (T + 1) = j + 1 :=
        Nat.count_nth_succ_of_infinite (infinite_PC (j - 1) (by omega)) j
      have h2 := count_PC_two_pow_succ (j - 1)
      have h3 : Nat.count (PC (j - 1)) (2 ^ j) = j := by
        have h4 : 2 ^ j = 2 ^ ((j - 1) + 1) := by
          rw [Nat.sub_add_cancel (show 1 ≤ j by omega)]
        have h5 : Nat.count (PC (j - 1)) (2 ^ ((j - 1) + 1)) = (j - 1) + 1 := h2
        rw [← h4] at h5
        omega
      have h6 := Nat.count_monotone (PC (j - 1)) (show T + 1 ≤ 2 ^ j by omega)
      omega
    have h1 : 1 ≤ Nat.count (PC j) (T + 1) := by
      have h2 : 1 ≤ Nat.count (PC j) (2 ^ j) := by
        have h3 := Nat.count_lt_count_succ_iff (p := PC j) (n := 2 ^ j - 1)
          |>.2 (PC_two_pow_sub_one j)
        have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        have h4 : 2 ^ j = (2 ^ j - 1) + 1 := by omega
        rw [h4]
        omega
      have h5 := Nat.count_monotone (PC j) (show 2 ^ j ≤ T + 1 by omega)
      omega
    have hc2 : Nat.count (PC j) (2 * T + 1) = Nat.count (PC j) (T + 1) + Nat.count (PC (j - 1)) T :=
      count_two_mul_add_one j (by omega) T
    have he1 : entry ((j - 1) + 1) (j + 1) = Nat.nth (PC j) j := by
      rw [Nat.sub_add_cancel (show 1 ≤ j by omega)]
      exact entry_eq j j
    have he2 : entry (j - 1) (j + 1) = T := entry_eq (j - 1) j
    have hnth : Nat.nth (PC j) j = 2 * T + 1 := by
      have hid : entry ((j - 1) + 1) (j + 1) + 1 = 2 * (entry (j - 1) (j + 1) + 1) := hfail
      rw [he1, he2] at hid
      omega
    have hc3 : Nat.count (PC j) (2 * T + 1) = j := by
      rw [← hnth]
      exact Nat.count_nth_of_infinite hinj1 j
    omega
