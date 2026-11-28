import OMAStatements.S_oeis_a257948

namespace OMA.S_oeis_a257948



/-! ### The recursion and the bounds -/

theorem s2_rec (n : ℕ) : s2 n = (n % 100) ^ 2 + s2 (n / 100) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [s2]
  · unfold s2
    rw [Nat.digits_def' (by norm_num) hn]
    simp

theorem s2_zero : s2 0 = 0 := by simp [s2]

/-- The fast form used by the kernel, valid below `10^6`. -/
def s2f (n : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.mul (Nat.mod n 100) (Nat.mod n 100))
    (Nat.mul (Nat.mod (Nat.div n 100) 100) (Nat.mod (Nat.div n 100) 100)))
    (Nat.mul (Nat.mod (Nat.div n 10000) 100) (Nat.mod (Nat.div n 10000) 100))

theorem s2_eq_s2f {n : ℕ} (hn : n < 1000000) : s2 n = s2f n := by
  rw [s2_rec n, s2_rec (n / 100), s2_rec (n / 100 / 100)]
  have h : n / 100 / 100 / 100 = 0 := by omega
  rw [h, s2_zero, Nat.div_div_eq_div_mul]
  show _ = (n % 100) * (n % 100) + (n / 100 % 100) * (n / 100 % 100) +
    (n / 10000 % 100) * (n / 10000 % 100)
  ring

theorem s2_le_small {n : ℕ} (hn : n < 1000000) : s2 n ≤ 29403 := by
  rw [s2_eq_s2f hn]
  show (n % 100) * (n % 100) + (n / 100 % 100) * (n / 100 % 100) +
    (n / 10000 % 100) * (n / 10000 % 100) ≤ 29403
  have h1 : n % 100 < 100 := Nat.mod_lt _ (by norm_num)
  have h2 : n / 100 % 100 < 100 := Nat.mod_lt _ (by norm_num)
  have h3 : n / 10000 % 100 < 100 := Nat.mod_lt _ (by norm_num)
  have e1 : (n % 100) * (n % 100) ≤ 99 * 99 := Nat.mul_le_mul (by omega) (by omega)
  have e2 : (n / 100 % 100) * (n / 100 % 100) ≤ 99 * 99 := Nat.mul_le_mul (by omega) (by omega)
  have e3 : (n / 10000 % 100) * (n / 10000 % 100) ≤ 99 * 99 := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem s2_lt_large : ∀ n, 29404 ≤ n → s2 n < n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 1000000 with h | h
    · have := s2_le_small h
      omega
    · rw [s2_rec]
      have hsq : (n % 100) ^ 2 ≤ 9801 := by
        have : n % 100 ≤ 99 := by have := Nat.mod_lt n (show 100 > 0 by norm_num); omega
        calc (n % 100) ^ 2 ≤ 99 ^ 2 := Nat.pow_le_pow_left this 2
          _ = 9801 := by norm_num
      rcases Nat.lt_or_ge (n / 100) 1000000 with h' | h'
      · have := s2_le_small h'
        omega
      · have := ih (n / 100) (by omega) (by omega)
        omega

theorem s2_le_max (x : ℕ) : s2 x ≤ max 29403 (x - 1) := by
  rcases Nat.lt_or_ge x 29404 with h | h
  · have := s2_le_small (show x < 1000000 by omega)
    omega
  · have := s2_lt_large x h
    omega

/-- Orbits are bounded by `max n 29403`. -/
theorem iter_le (n : ℕ) : ∀ i, s2^[i] n ≤ max n 29403 := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have := s2_le_max (s2^[i] n)
    omega

/-- Periodic points are at most 29403. -/
theorem periodic_le {n m : ℕ} (hm : 0 < m) (h : s2^[m] n = n) : n ≤ 29403 := by
  by_contra hn
  push Not at hn
  have key : ∀ i, 0 < i → s2^[i] n ≤ n - 1 := by
    intro i hi
    induction i with
    | zero => omega
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      rcases Nat.eq_zero_or_pos i with rfl | hi'
      · simpa using (show s2 n ≤ n - 1 by have := s2_le_max n; omega)
      · have h1 := ih hi'
        have := s2_le_max (s2^[i] n)
        omega
  have := key m hm
  omega

/-! ### The cycles -/

/-- The ten cycles of length > 1, in the entry's order. -/
def cycles : List (List ℕ) :=
  [[5965, 7706],
    [3869, 6205],
    [3460, 4756, 5345, 4834],
    [1781, 6850, 7124, 5617, 3425],
    [3770, 6269, 8605, 7421, 5917],
    [4973, 7730, 6829, 5465, 7141, 6722],
    [1268, 4768, 6833, 5713, 3418, 1480, 6596, 13441, 2838, 2228],
    [1946, 2477, 6505, 4250, 4264, 5860, 6964, 8857, 10993, 8731, 8530, 8125, 7186, 12437],
    [37, 1369, 4930, 3301, 1090, 8200, 6724, 5065, 6725, 5114, 2797, 10138, 1446, 2312, 673, 5365,
      7034, 6056, 6736, 5785, 10474, 5493, 11565, 4451, 4537, 3394, 9925, 10426, 693, 8685, 14621,
      2558, 3989, 9442, 10600],
    [41, 1681, 6817, 4913, 2570, 5525, 3650, 3796, 10585, 7251, 7785, 13154, 3878, 7528, 6409, 4177,
      7610, 5876, 9140, 9881, 16165, 7947, 8450, 9556, 12161, 4163, 5650, 5636, 4432, 2960, 4441,
      3617, 1585, 7450, 7976, 12017, 690, 8136, 7857, 9333, 9738, 10853, 2874, 6260, 7444, 7412, 5620,
      3536, 2521, 1066, 4456, 5072, 7684, 12832, 1809, 405]]

/-- The fixed points. -/
def fixedPts : List ℕ := [0, 1, 1233, 8833]

/-- All periodic points below 29404. -/
def P : List ℕ := cycles.flatten ++ fixedPts

def memB (x : ℕ) : List ℕ → Bool :=
  List.rec false (fun y _ ih => Nat.beq x y || ih)

theorem memB_iff (x : ℕ) : ∀ l : List ℕ, memB x l = true ↔ x ∈ l := by
  intro l
  induction l with
  | nil => simp [memB]
  | cons y l ih =>
    show (Nat.beq x y || memB x l) = true ↔ x ∈ y :: l
    rw [Bool.or_eq_true, ih, List.mem_cons, Nat.beq_eq]

/-- `s2f^[k] n` by a kernel-friendly recursion. -/
def iterF (k n : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) n (fun _ ih => s2f ih) k

theorem iterF_succ (k n : ℕ) : iterF (k + 1) n = s2f (iterF k n) := rfl

/-- Orbits of points at most 29403 stay at most 29403, where `s2 = s2f`. -/
theorem iter_eq_iterF {n : ℕ} (hn : n ≤ 29403) : ∀ k, s2^[k] n = iterF k n ∧ s2^[k] n ≤ 29403 := by
  intro k
  induction k with
  | zero => exact ⟨rfl, hn⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Function.iterate_succ_apply', iterF_succ, ← h1]
    have hlt : s2^[k] n < 1000000 := by omega
    exact ⟨s2_eq_s2f hlt, s2_le_small hlt⟩

/-- The bitmask of `P`: bit `x` is set iff `x ∈ P` (checked below for `x < 16384`). -/
def M : ℕ := 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000010002000000000000000000000000000400000000000400000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000002000000000020000000000000000000000000000000000040000000000000000000000000000000000000000000010000000000000000000000000000400000000000000000000000000200000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000002000002000000000000000000000000080000000000200000000000000000002000000000000000000400000000000000000004000000000000000000000000000000000000000000000000000000000000010000000000000001002000000000000000000000000000000000000100000008000000000000000000000200000000000000000200000000000004000004000010000000000000000004000000000000000000010000000000000000000410000020100000000000000000000000000000000000000008000000000000000400000000002000100000000000000000000004000000000000000010000000000000000000000000000400022002000000000000000000010034000000000000000000000000000000100000000000000000000002000000000000000000000002000000000000000000000000000000000020100000000000002000000000000000000000000000000000000100000000000000000000002000000000002000000000100010000000000000000002000000000000000002000000000000000400100012000000000000000000000020000000200000020000000000000000000000002000020000000000000000000000000000000000000000000000000000000004000000000102000000000000000000000020000000000400020000000000000000000400000000000000010010000000000000000000000000000000000000000000000000000002000000000000000000010802010000000000000000000000000000000000000000010004000000000000000002000800000000000000000000000000000000000000000020000000000000000000000000004020000000000000000010000004000000000000000000000000000004000000020000000000000000000100000000000000000010000000020400000400000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000040000000040000000002000000000000000000000000000000000000000000000000000000004004000000002000000000020000000000000000000000000000000000000000100000000000000000000100000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000200000020000000000000000000000002000000000000000000000002000000000000000000000000010000000040000000000000000002000000000000000000000000100000000200000000000000000000000000000000000400000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000240002000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000022000000003

/-- Fast membership test for `P` (raw operations, no type classes, for the kernel). -/
def inP (x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight M x) 1) 1

theorem M_shift_large {x : ℕ} (hx : 16384 ≤ x) : Nat.shiftRight M x = 0 := by
  have hM : M < 2 ^ 16384 := by decide +kernel
  show M >>> x = 0
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by norm_num) hx))

/-- `tableOK L`: every `x < L` with `inP x` lies in `P`. -/
def tableOK (L : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun x ih => (!inP x || memB x P) && ih) L

theorem tableOK_spec : ∀ L, tableOK L = true → ∀ x < L, inP x = true → x ∈ P := by
  intro L
  induction L with
  | zero => intro _ x hx; omega
  | succ L ih =>
    intro h x hx hin
    have h' : ((!inP L || memB L P) && tableOK L) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_or_ge x L with hxL | hxL
    · exact ih h'.2 x hxL hin
    · have : x = L := by omega
      subst this
      have := h'.1
      rw [hin, Bool.not_true, Bool.false_or] at this
      exact (memB_iff _ _).mp this

theorem table : tableOK 16384 = true := by decide +kernel

theorem mem_of_inP {x : ℕ} (h : inP x = true) : x ∈ P := by
  rcases Nat.lt_or_ge x 16384 with hx | hx
  · exact tableOK_spec 16384 table x hx h
  · exfalso
    unfold inP at h
    rw [M_shift_large hx] at h
    exact absurd h (by decide)

/-- `reachB f x`: some `s2f^[j] x` with `j ≤ f` lies in `P` (early exit, loop-shaped for the kernel). -/
def reachB (fuel : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun x => inP x)
    (fun _ ih x => inP x || ih (s2f x)) fuel

theorem reachB_spec : ∀ fuel x, x ≤ 29403 → reachB fuel x = true → ∃ j ≤ fuel, s2^[j] x ∈ P := by
  intro fuel
  induction fuel with
  | zero =>
    intro x _ h
    exact ⟨0, le_refl 0, mem_of_inP h⟩
  | succ f ih =>
    intro x hx h
    have h' : (inP x || reachB f (s2f x)) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with h1 | h1
    · exact ⟨0, Nat.zero_le _, mem_of_inP h1⟩
    · have hlt : x < 1000000 := by omega
      rw [← s2_eq_s2f hlt] at h1
      obtain ⟨j, hj, hjP⟩ := ih (s2 x) (s2_le_small hlt) h1
      exact ⟨j + 1, by omega, by rw [Function.iterate_succ_apply]; exact hjP⟩

/-- `blockOK s L`: every `n ∈ [s, s + L)` reaches `P` within 100 steps. -/
def blockOK (s L : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => reachB 100 (Nat.add s i) && ih) L

theorem blockOK_spec (s : ℕ) : ∀ L, blockOK s L = true → ∀ i < L, reachB 100 (s + i) = true := by
  intro L
  induction L with
  | zero => intro _ i hi; omega
  | succ L ih =>
    intro h i hi
    have h' : (reachB 100 (Nat.add s L) && blockOK s L) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_or_ge i L with hiL | hiL
    · exact ih h'.2 i hiL
    · have : i = L := by omega
      subst this
      exact h'.1

/-! Blocks of 3000 starting points, each a separate declaration (the kernel frees its cache between
declarations, which keeps the peak memory low). -/

theorem b0 : blockOK 0 3000 = true := by decide +kernel
theorem b1 : blockOK 3000 3000 = true := by decide +kernel
theorem b2 : blockOK 6000 3000 = true := by decide +kernel
theorem b3 : blockOK 9000 3000 = true := by decide +kernel
theorem b4 : blockOK 12000 3000 = true := by decide +kernel
theorem b5 : blockOK 15000 3000 = true := by decide +kernel
theorem b6 : blockOK 18000 3000 = true := by decide +kernel
theorem b7 : blockOK 21000 3000 = true := by decide +kernel
theorem b8 : blockOK 24000 3000 = true := by decide +kernel
theorem b9 : blockOK 27000 2404 = true := by decide +kernel

theorem pass {n : ℕ} (hn : n ≤ 29403) : reachB 100 n = true := by
  have key : ∀ s L, blockOK s L = true → s ≤ n → n < s + L → reachB 100 n = true := by
    intro s L hb h1 h2
    have := blockOK_spec s L hb (n - s) (by omega)
    rwa [show s + (n - s) = n by omega] at this
  have hk : n / 3000 < 10 := by omega
  interval_cases h : n / 3000
  · exact key 0 3000 b0 (by omega) (by omega)
  · exact key 3000 3000 b1 (by omega) (by omega)
  · exact key 6000 3000 b2 (by omega) (by omega)
  · exact key 9000 3000 b3 (by omega) (by omega)
  · exact key 12000 3000 b4 (by omega) (by omega)
  · exact key 15000 3000 b5 (by omega) (by omega)
  · exact key 18000 3000 b6 (by omega) (by omega)
  · exact key 21000 3000 b7 (by omega) (by omega)
  · exact key 24000 3000 b8 (by omega) (by omega)
  · exact key 27000 2404 b9 (by omega) (by omega)

theorem enter_P {n : ℕ} (hn : n ≤ 29403) : ∃ j ≤ 100, s2^[j] n ∈ P :=
  reachB_spec 100 n hn (pass hn)

theorem P_closed : ∀ y ∈ P, s2 y ∈ P := by
  have hall : P.all (fun y => memB (s2f y) P) = true := by decide +kernel
  have hsmall : P.all (fun y => Nat.blt y 1000000) = true := by decide +kernel
  intro y hy
  rw [List.all_eq_true] at hall hsmall
  have h1 := hall y hy
  have h2 := hsmall y hy
  rw [Nat.blt_eq] at h2
  rw [s2_eq_s2f h2]
  exact (memB_iff _ _).mp h1

theorem fixed_of_mem {y : ℕ} (hy : y ∈ fixedPts) : s2 y = y := by
  simp only [fixedPts, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl <;> rw [s2_eq_s2f (by norm_num)] <;> decide

/-- A periodic point that is not fixed lies in one of the ten cycles. -/
theorem periodic_mem {n m : ℕ} (hm : 0 < m) (h : s2^[m] n = n) (hfix : s2 n ≠ n) :
    n ∈ cycles.flatten := by
  have hn := periodic_le hm h
  -- n is in the forward orbit of y = s2^[100] n
  have hper : ∀ t, s2^[m * t] n = n := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, Function.iterate_add_apply, h, ih]
  obtain ⟨j0, hj0, hy⟩ := enter_P hn
  have horbit : ∀ j, s2^[j] (s2^[j0] n) ∈ P := by
    intro j
    induction j with
    | zero => simpa using hy
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact P_closed _ ih
  have hmt : j0 ≤ m * j0 := Nat.le_mul_of_pos_left j0 hm
  have hnP : n ∈ P := by
    have e : n = s2^[m * j0 - j0] (s2^[j0] n) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hmt, hper]
    rw [e]
    exact horbit _
  rw [P, List.mem_append] at hnP
  rcases hnP with h1 | h1
  · exact h1
  · exact absurd (fixed_of_mem h1) hfix

/-- Every orbit is eventually periodic (it stays below `max n 29403`). -/
theorem eventually_periodic (n : ℕ) : ∃ k m, 0 < m ∧ s2^[k + m] n = s2^[k] n := by
  set B := max n 29403
  have hmaps : ∀ i ∈ Finset.range (B + 2), s2^[i] n ∈ Finset.range (B + 1) := by
    intro i _
    rw [Finset.mem_range]
    have := iter_le n i
    omega
  obtain ⟨i, hi, j, hj, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simp) hmaps
  rcases Nat.lt_or_gt_of_ne hne with hij | hij
  · exact ⟨i, j - i, by omega, by rw [Nat.add_sub_cancel' hij.le]; exact heq.symm⟩
  · exact ⟨j, i - j, by omega, by rw [Nat.add_sub_cancel' hij.le]; exact heq⟩

theorem cycles_ok : ∀ c ∈ cycles, IsCycle c := by
  intro c hc
  have hsmall : cycles.all (fun c => c.all (fun y => Nat.blt y 1000000)) = true := by decide +kernel
  have hmap : cycles.all (fun c => decide (c ≠ [] ∧ c.Nodup ∧ c.map s2f = c.rotate 1)) = true := by
    decide +kernel
  rw [List.all_eq_true] at hsmall hmap
  have h1 := hsmall c hc
  have h2 := of_decide_eq_true (hmap c hc)
  rw [List.all_eq_true] at h1
  refine ⟨h2.1, h2.2.1, ?_⟩
  rw [← h2.2.2]
  apply List.map_congr_left
  intro y hy
  have := h1 y hy
  rw [Nat.blt_eq] at this
  exact s2_eq_s2f this

theorem solution :
    (∀ n, ∃ k m, 0 < m ∧ s2^[k + m] n = s2^[k] n) ∧
    ∃ cs : List (List ℕ), cs.map List.length = [2, 2, 4, 5, 5, 6, 10, 14, 35, 56] ∧
      (∀ c ∈ cs, IsCycle c) ∧ cs.flatten.Nodup ∧
      ∀ n, (∃ m, 0 < m ∧ s2^[m] n = n) → s2 n ≠ n → n ∈ cs.flatten := by
  refine ⟨eventually_periodic, cycles, by decide, cycles_ok, by decide +kernel, ?_⟩
  rintro n ⟨m, hm, h⟩ hfix
  exact periodic_mem hm h hfix

end OMA.S_oeis_a257948

theorem OMA.solution : type_of% @OMA.S_oeis_a257948.main :=
  OMA.S_oeis_a257948.solution
