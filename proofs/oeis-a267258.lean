import OMAStatements.S_oeis_a267258

namespace Ours

def update (l c r : Bool) : Bool :=
  (111 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)
def sweep (l c : Bool) : List Bool → List Bool
  | [] => []
  | r :: tail => update l c r :: sweep c r tail
def row : ℕ → Bool × List Bool
  | 0 => (false, [true])
  | n + 1 =>
    let (b, w) := row n
    (update b b b, sweep b b (w ++ [b, b]))
def centre (n : ℕ) : ℕ := ((row n).2[n]!).toNat
def a : ℕ → ℕ
  | 0 => centre 0
  | n + 1 => 2 * a n + centre (n + 1)



namespace RowProof

def advance (s : Bool × List Bool) : Bool × List Bool :=
  (update s.1 s.1 s.1, sweep s.1 s.1 (s.2 ++ [s.1, s.1]))

lemma row_next (n : ℕ) : row (n + 1) = advance (row n) := rfl

def blocks (w : List Bool) : ℕ → List Bool → List Bool
  | 0, t => t
  | k + 1, t => w ++ blocks w k t

lemma blocks_append (w : List Bool) (k : ℕ) (t s : List Bool) :
    blocks w k t ++ s = blocks w k (t ++ s) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [blocks, List.append_assoc, ih]

lemma sweep_blocks (u v : List Bool) (l c : Bool)
    (h : ∀ t, sweep l c (u ++ t) = v ++ sweep l c t) (k : ℕ) (t : List Bool) :
    sweep l c (blocks u k t) = blocks v k (sweep l c t) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [blocks, h, ih]

lemma blocks_rotate (b : Bool) (w : List Bool) (k : ℕ) (t : List Bool) :
    blocks (b :: w) k (b :: t) = b :: blocks (w ++ [b]) k t := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [blocks, ih, List.cons_append, List.append_assoc, List.nil_append]

lemma sweepBlock0 (k : ℕ) (t : List Bool) :
    sweep false false (blocks [false, false] k t) =
      blocks [true, true] k (sweep false false t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock1 (k : ℕ) (t : List Bool) :
    sweep true true (blocks [true, true] k t) =
      blocks [false, false] k (sweep true true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma rotateBlock0 (k : ℕ) (t : List Bool) :
    blocks [false, false] k (false :: t) =
      false :: blocks [false, false] k t :=
  blocks_rotate _ [false] k t

lemma rotateBlock1 (k : ℕ) (t : List Bool) :
    blocks [true, true] k (true :: t) =
      true :: blocks [true, true] k t :=
  blocks_rotate _ [true] k t

lemma update000 : update false false false = true := by decide
lemma update001 : update false false true = true := by decide
lemma update010 : update false true false = true := by decide
lemma update011 : update false true true = true := by decide
lemma update100 : update true false false = false := by decide
lemma update101 : update true false true = true := by decide
lemma update110 : update true true false = true := by decide
lemma update111 : update true true true = false := by decide

def phase0 (k : ℕ) : Bool × List Bool :=
  (true, true :: true :: true :: true :: true :: true :: true :: (blocks [true, true] k (true :: true :: true :: (blocks [true, true] k (false :: false :: false :: true :: false :: [])))))

def phase1 (k : ℕ) : Bool × List Bool :=
  (false, false :: false :: false :: false :: false :: false :: false :: (blocks [false, false] k (false :: false :: false :: (blocks [false, false] k (true :: false :: true :: true :: true :: true :: true :: [])))))

lemma advance0 (k : ℕ) : advance (phase0 k) = phase1 k := by
  simp only [advance, phase0, phase1, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1]

lemma advance1 (k : ℕ) : advance (phase1 k) = phase0 (k + 1) := by
  simp only [advance, phase1, phase0, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1]

lemma row_phases (k : ℕ) :
    row (2 * k + 7) = phase0 k ∧
    row (2 * k + 8) = phase1 k := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨_, old⟩ := ih
    have step0 : row (2 * (k + 1) + 7) = phase0 (k + 1) := by
      rw [show (2 * (k + 1) + 7) = (2 * k + 8) + 1 by omega, row_next (2 * k + 8), old, advance1]
    have step1 : row (2 * (k + 1) + 8) = phase1 (k + 1) := by
      rw [show (2 * (k + 1) + 8) = (2 * (k + 1) + 7) + 1 by omega, row_next (2 * (k + 1) + 7), step0, advance0]
    exact ⟨step0, step1⟩

lemma blocks_length (w : List Bool) (k : ℕ) (s : List Bool) :
    (blocks w k s).length = k * w.length + s.length := by
  induction k with
  | zero => simp [blocks]
  | succ k ih => simp [blocks, ih, Nat.succ_mul]; omega

lemma pick_append (u v : List Bool) (i : ℕ) :
    (u ++ v)[u.length + i]! = v[i]! := by
  induction u with
  | nil => simp
  | cons b u ih => simpa only [List.cons_append, List.length_cons, Nat.succ_add,
      List.getElem!_cons_succ] using ih

lemma rowValue0 (k : ℕ) : (centre (2 * k + 7) : ℚ) = 1 := by
  let pre : List Bool := true :: true :: true :: true :: true :: true :: true :: (blocks [true, true] k ([]))
  have splitRow : (phase0 k).2 = pre ++ (true :: true :: true :: (blocks [true, true] k (false :: false :: false :: true :: false :: []))) := by
    simp only [pre, phase0, List.cons_append, blocks_append, List.nil_append]
  have middle : 2 * k + 7 = pre.length + 0 := by
    simp [pre, blocks_length] <;> omega
  rw [centre, (row_phases k).1, splitRow, middle, pick_append, List.getElem!_cons_zero]
  rfl

lemma rowValue1 (k : ℕ) : (centre (2 * k + 8) : ℚ) = 0 := by
  let pre : List Bool := false :: false :: false :: false :: false :: false :: false :: (blocks [false, false] k (false :: []))
  have splitRow : (phase1 k).2 = pre ++ (false :: false :: (blocks [false, false] k (true :: false :: true :: true :: true :: true :: true :: []))) := by
    simp only [pre, phase1, List.cons_append, blocks_append, List.nil_append]
  have middle : 2 * k + 8 = pre.length + 0 := by
    simp [pre, blocks_length] <;> omega
  rw [centre, (row_phases k).2, splitRow, middle, pick_append, List.getElem!_cons_zero]
  rfl

lemma total_phases (k : ℕ) :
    (a (2 * k + 7) : ℚ) = (-1 / 3 : ℚ) + (766 / 3 : ℚ) * ((2 : ℚ) ^ k) ^ 2 ∧
    (a (2 * k + 8) : ℚ) = (-2 / 3 : ℚ) + (1532 / 3 : ℚ) * ((2 : ℚ) ^ k) ^ 2 := by
  induction k with
  | zero =>
    norm_num [show a 7 = 255 by rfl, show a 8 = 510 by rfl]
  | succ k ih =>
    obtain ⟨_, old⟩ := ih
    have step0 : (a (2 * (k + 1) + 7) : ℚ) = (-1 / 3 : ℚ) + (766 / 3 : ℚ) * ((2 : ℚ) ^ (k + 1)) ^ 2 := by
      have addRow : a (2 * (k + 1) + 7) = 2 * a (2 * k + 8) + centre (2 * (k + 1) + 7) := by
        rw [show (2 * (k + 1) + 7) = (2 * k + 8) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, old, rowValue0]
      push_cast
      try simp only [pow_succ]
      ring
    have step1 : (a (2 * (k + 1) + 8) : ℚ) = (-2 / 3 : ℚ) + (1532 / 3 : ℚ) * ((2 : ℚ) ^ (k + 1)) ^ 2 := by
      have addRow : a (2 * (k + 1) + 8) = 2 * a (2 * (k + 1) + 7) + centre (2 * (k + 1) + 8) := by
        rw [show (2 * (k + 1) + 8) = (2 * (k + 1) + 7) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, step0, rowValue1]
      push_cast
      try simp only [pow_succ]
      ring
    exact ⟨step0, step1⟩

lemma claim0 : ∀ n : ℕ, 5 < n → (a n : ℚ) = (383 * (2 : ℚ) ^ n - 32 * ((-1 : ℚ) ^ n + 3)) / 192 := by
  intro n hn
  by_cases small : n < 7
  · interval_cases n <;> norm_num [show a 0 = 1 by rfl, show a 1 = 3 by rfl, show a 2 = 7 by rfl, show a 3 = 15 by rfl, show a 4 = 31 by rfl, show a 5 = 63 by rfl, show a 6 = 127 by rfl] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 2 + 7 ∨ n = k * 2 + 8 := ⟨(n - 7) / 2, by omega⟩
  rcases hk with rfl | rfl
  · have val0 : (a (k * 2 + 7) : ℚ) = (-1 / 3 : ℚ) + (766 / 3 : ℚ) * ((2 : ℚ) ^ k) ^ 2 := by
      rw [show k * 2 + 7 = (2 * k + 7) by omega]
      exact (total_phases k).1
    have powers0 (j : ℕ) : (2 : ℚ) ^ (j * 2 + 7) = 128 * ((2 : ℚ) ^ j) ^ 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 7 = (j * 2 + 7) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp0 : (2 : ℚ) ^ ((k * 2 + 7) : ℕ) = 128 * ((2 : ℚ) ^ k) ^ 2 := by
      rw [show ((k * 2 + 7) : ℕ) = (k * 2 + 7) by omega]
      exact powers0 k
    have powers1 (j : ℕ) : (-1 : ℚ) ^ (j * 2 + 7) = (-1) := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 7 = (j * 2 + 7) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp1 : (-1 : ℚ) ^ ((k * 2 + 7) : ℕ) = (-1) := by
      rw [show ((k * 2 + 7) : ℕ) = (k * 2 + 7) by omega]
      exact powers1 k
    simp only [val0, exp0, exp1]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 2 + 8) : ℚ) = (-2 / 3 : ℚ) + (1532 / 3 : ℚ) * ((2 : ℚ) ^ k) ^ 2 := by
      rw [show k * 2 + 8 = (2 * k + 8) by omega]
      exact (total_phases k).2
    have powers0 (j : ℕ) : (2 : ℚ) ^ (j * 2 + 8) = 256 * ((2 : ℚ) ^ j) ^ 2 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 8 = (j * 2 + 8) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp0 : (2 : ℚ) ^ ((k * 2 + 8) : ℕ) = 256 * ((2 : ℚ) ^ k) ^ 2 := by
      rw [show ((k * 2 + 8) : ℕ) = (k * 2 + 8) by omega]
      exact powers0 k
    have powers1 (j : ℕ) : (-1 : ℚ) ^ (j * 2 + 8) = 1 := by
      induction j with
      | zero => norm_num
      | succ j ih =>
        rw [show (j + 1) * 2 + 8 = (j * 2 + 8) + 2 by omega, pow_add, ih]
        simp only [pow_succ] <;> norm_num <;> ring
    have exp1 : (-1 : ℚ) ^ ((k * 2 + 8) : ℕ) = 1 := by
      rw [show ((k * 2 + 8) : ℕ) = (k * 2 + 8) by omega]
      exact powers1 k
    simp only [val0, exp0, exp1]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring

lemma convolution : ∀ n : ℕ, (1) * (if 0 ≤ n then (a (n - 0) : ℚ) else 0) + (-2) * (if 1 ≤ n then (a (n - 1) : ℚ) else 0) + (-1) * (if 2 ≤ n then (a (n - 2) : ℚ) else 0) + (2) * (if 3 ≤ n then (a (n - 3) : ℚ) else 0) =
      (1) * (if n = 0 then (1 : ℚ) else 0) + (1) * (if n = 1 then (1 : ℚ) else 0) + (-1) * (if n = 8 then (1 : ℚ) else 0) := by
  intro n
  by_cases small : n < 10
  · interval_cases n <;> norm_num [show a 0 = 1 by rfl, show a 1 = 3 by rfl, show a 2 = 7 by rfl, show a 3 = 15 by rfl, show a 4 = 31 by rfl, show a 5 = 63 by rfl, show a 6 = 127 by rfl, show a 7 = 255 by rfl, show a 8 = 510 by rfl, show a 9 = 1021 by rfl] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 2 + 10 ∨ n = k * 2 + 11 := ⟨(n - 10) / 2, by omega⟩
  rcases hk with rfl | rfl
  · have val0 : (a (k * 2 + 10) : ℚ) = (-2 / 3 : ℚ) + (1532 / 3 : ℚ) * ((2 : ℚ) ^ (k + 1)) ^ 2 := by
      rw [show k * 2 + 10 = (2 * (k + 1) + 8) by omega]
      exact (total_phases (k + 1)).2
    have val1 : (a (k * 2 + 10 - 1) : ℚ) = (-1 / 3 : ℚ) + (766 / 3 : ℚ) * ((2 : ℚ) ^ (k + 1)) ^ 2 := by
      rw [show k * 2 + 10 - 1 = (2 * (k + 1) + 7) by omega]
      exact (total_phases (k + 1)).1
    have val2 : (a (k * 2 + 10 - 2) : ℚ) = (-2 / 3 : ℚ) + (1532 / 3 : ℚ) * ((2 : ℚ) ^ k) ^ 2 := by
      rw [show k * 2 + 10 - 2 = (2 * k + 8) by omega]
      exact (total_phases k).2
    have val3 : (a (k * 2 + 10 - 3) : ℚ) = (-1 / 3 : ℚ) + (766 / 3 : ℚ) * ((2 : ℚ) ^ k) ^ 2 := by
      rw [show k * 2 + 10 - 3 = (2 * k + 7) by omega]
      exact (total_phases k).1
    simp only [val0, val1, val2, val3, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 2 + 11) : ℚ) = (-1 / 3 : ℚ) + (766 / 3 : ℚ) * ((2 : ℚ) ^ (k + 2)) ^ 2 := by
      rw [show k * 2 + 11 = (2 * (k + 2) + 7) by omega]
      exact (total_phases (k + 2)).1
    have val1 : (a (k * 2 + 11 - 1) : ℚ) = (-2 / 3 : ℚ) + (1532 / 3 : ℚ) * ((2 : ℚ) ^ (k + 1)) ^ 2 := by
      rw [show k * 2 + 11 - 1 = (2 * (k + 1) + 8) by omega]
      exact (total_phases (k + 1)).2
    have val2 : (a (k * 2 + 11 - 2) : ℚ) = (-1 / 3 : ℚ) + (766 / 3 : ℚ) * ((2 : ℚ) ^ (k + 1)) ^ 2 := by
      rw [show k * 2 + 11 - 2 = (2 * (k + 1) + 7) by omega]
      exact (total_phases (k + 1)).1
    have val3 : (a (k * 2 + 11 - 3) : ℚ) = (-2 / 3 : ℚ) + (1532 / 3 : ℚ) * ((2 : ℚ) ^ k) ^ 2 := by
      rw [show k * 2 + 11 - 3 = (2 * k + 8) by omega]
      exact (total_phases k).2
    simp only [val0, val1, val2, val3, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring

open PowerSeries

lemma generating_function : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 2 * X)) =
      1 + X - X ^ 8 := by
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  calc
    _ = C (1 : ℚ) * (s * X ^ 0) + C (-2 : ℚ) * (s * X ^ 1) + C (-1 : ℚ) * (s * X ^ 2) + C (2 : ℚ) * (s * X ^ 3) := by simp only [map_neg, map_one, map_ofNat] <;> ring
    _ = C (1 : ℚ) * (X ^ 0) + C (1 : ℚ) * (X ^ 1) + C (-1 : ℚ) * (X ^ 8) := by
      apply PowerSeries.ext
      intro n
      simp only [map_add, coeff_C_mul]
      simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
      exact convolution n
    _ = _ := by simp only [map_neg, map_one, map_ofNat] <;> ring

end RowProof

open RowProof


end Ours

section Helpers

open PowerSeries

lemma ps_eq_mul_inv {F N D : PowerSeries ℚ} (h : F * D = N) (hc : constantCoeff D ≠ 0) :
    F = N * D⁻¹ := by
  rw [← h, mul_assoc, PowerSeries.mul_inv_cancel D hc, mul_one]

lemma ps_int_of_rat {L R : PowerSeries ℤ}
    (h : PowerSeries.map (Int.castRingHom ℚ) L = PowerSeries.map (Int.castRingHom ℚ) R) :
    L = R := by
  ext n
  apply Int.cast_injective (α := ℚ)
  have hn := congr_arg (PowerSeries.coeff n) h
  simpa only [PowerSeries.coeff_map, Int.coe_castRingHom] using hn

lemma nat_div_of_floor {a X Y : ℕ} (hY : 0 < Y)
    (h : (a : ℤ) = ⌊(X : ℚ) / (Y : ℚ)⌋) : a = X / Y := by
  have hYq : (0 : ℚ) < (Y : ℚ) := by exact_mod_cast hY
  have hf := Int.floor_eq_iff.mp h.symm
  have h1 : (a : ℚ) * (Y : ℚ) ≤ (X : ℚ) := (le_div_iff₀ hYq).mp hf.1
  have h2 : (X : ℚ) < ((a : ℚ) + 1) * (Y : ℚ) := (div_lt_iff₀ hYq).mp hf.2
  have h1n : a * Y ≤ X := by exact_mod_cast h1
  have h2n : X < (a + 1) * Y := by exact_mod_cast h2
  have hle : a ≤ X / Y := (Nat.le_div_iff_mul_le hY).mpr h1n
  have hlt : X / Y < a + 1 := (Nat.div_lt_iff_lt_mul hY).mpr h2n
  omega

def seg (a : ℤ) : ℕ → (ℤ → Bool) → List Bool
  | 0, _ => []
  | m + 1, g => g a :: seg (a + 1) m g

lemma seg_snoc (a : ℤ) (m : ℕ) (g : ℤ → Bool) :
    seg a (m + 1) g = seg a m g ++ [g (a + m)] := by
  induction m generalizing a with
  | zero => simp [seg]
  | succ m ih =>
    rw [seg, ih (a + 1), seg, List.cons_append]
    congr 2
    push_cast
    ring

lemma seg_append_two (a : ℤ) (m : ℕ) (g : ℤ → Bool) (b : Bool)
    (h1 : g (a + m) = b) (h2 : g (a + m + 1) = b) :
    seg a m g ++ [b, b] = seg a (m + 2) g := by
  rw [seg_snoc a (m + 1) g, seg_snoc a m g, List.append_assoc]
  simp only [List.singleton_append, Nat.cast_add, Nat.cast_one, ← add_assoc, h1, h2]

lemma seg_getElem? (a : ℤ) (m : ℕ) (g : ℤ → Bool) (k : ℕ) (hk : k < m) :
    (seg a m g)[k]? = some (g (a + k)) := by
  induction m generalizing a k with
  | zero => omega
  | succ m ih =>
    cases k with
    | zero => simp [seg]
    | succ k =>
      simp only [seg, List.getElem?_cons_succ]
      rw [ih (a + 1) k (by omega)]
      congr 1
      push_cast
      ring

lemma seg_count (c : Bool) (a : ℤ) (m : ℕ) (g : ℤ → Bool) :
    (seg a m g).count c = ∑ k ∈ Finset.range m, if g (a + k) = c then 1 else 0 := by
  induction m generalizing a with
  | zero => simp [seg]
  | succ m ih =>
    rw [seg_snoc, List.count_append, ih a, Finset.sum_range_succ]
    simp [List.count_cons, beq_iff_eq]

lemma seg_count_icc (n : ℕ) (g : ℤ → Bool) :
    (seg (-(n : ℤ)) (2 * n + 1) g).count true =
      ((Finset.Icc (-(n : ℤ)) n).filter (fun i => g i)).card := by
  rw [seg_count, Finset.card_filter]
  refine Finset.sum_nbij (fun k : ℕ => (k : ℤ) - n) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro k₁ _ k₂ _ h
    dsimp only at h
    omega
  · intro i hi
    have hi' := Finset.mem_Icc.mp hi
    refine ⟨(i + n).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    dsimp only
    omega
  · intro k _
    have h1 : -(n : ℤ) + (k : ℤ) = (k : ℤ) - n := by ring
    rw [h1]

lemma seg_ofDigits (B : ℕ) (a : ℤ) (m : ℕ) (g : ℤ → Bool) :
    Nat.ofDigits B (((seg a m g).map Bool.toNat).reverse) =
      ∑ k ∈ Finset.range m, if g (a + k) then B ^ (m - 1 - k) else 0 := by
  induction m generalizing a with
  | zero => simp [seg]
  | succ m ih =>
    rw [seg_snoc, List.map_append, List.reverse_append, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      Nat.ofDigits_cons, ih a, Finset.sum_range_succ, Finset.mul_sum]
    simp only [Nat.add_sub_cancel]
    have hsum :
        (∑ x ∈ Finset.range m, B * (if g (a + x) then B ^ (m - 1 - x) else 0)) =
          ∑ x ∈ Finset.range m, if g (a + x) then B ^ (m - x) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx' := Finset.mem_range.mp hx
      split_ifs
      · rw [show m - x = (m - 1 - x) + 1 by omega, pow_succ']
      · simp
    rw [hsum]
    cases g (a + m) <;> simp [Nat.add_comm]

lemma seg_ofDigits_rev (B : ℕ) (n : ℕ) (g : ℤ → Bool) :
    Nat.ofDigits B (((seg (-(n : ℤ)) (2 * n + 1) g).map Bool.toNat).reverse) =
      ∑ i ∈ Finset.range (2 * n + 1), (g ((n : ℤ) - i)).toNat * B ^ i := by
  rw [seg_ofDigits, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hidx : -(n : ℤ) + ((2 * n + 1 - 1 - i : ℕ) : ℤ) = (n : ℤ) - i := by omega
  have hexp : 2 * n + 1 - 1 - (2 * n + 1 - 1 - i) = i := by omega
  rw [hidx, hexp]
  cases g ((n : ℤ) - i) <;> simp

end Helpers


section Extras

lemma seg_getElem! (a : ℤ) (m : ℕ) (g : ℤ → Bool) (k : ℕ) (hk : k < m) :
    (seg a m g)[k]! = g (a + k) := by
  induction m generalizing a k with
  | zero => omega
  | succ m ih =>
    cases k with
    | zero => simp [seg]
    | succ k =>
      simp only [seg, List.getElem!_cons_succ]
      rw [ih (a + 1) k (by omega)]
      congr 1
      push_cast
      ring

end Extras

namespace BridgeProof

lemma sweep_seg_ours (a : ℤ) (m : ℕ) (g : ℤ → Bool) :
    Ours.sweep (g (a - 2)) (g (a - 1)) (seg a m g) =
      seg (a - 1) m (fun i => Ours.update (g (i - 1)) (g i) (g (i + 1))) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    simp only [seg, Ours.sweep]
    refine congrArg₂ List.cons ?_ ?_
    · congr 1 <;> ring
    · calc
        Ours.sweep (g (a - 1)) (g a) (seg (a + 1) m g)
          = Ours.sweep (g ((a + 1) - 2)) (g ((a + 1) - 1)) (seg (a + 1) m g) := by
              congr 1 <;> ring
        _ = seg ((a + 1) - 1) m (fun i => Ours.update (g (i - 1)) (g i) (g (i + 1))) := ih (a + 1)
        _ = seg ((a - 1) + 1) m (fun i => Ours.update (g (i - 1)) (g i) (g (i + 1))) := by
              congr 1; ring

lemma st_step (n : ℕ) (i : ℤ) :
    (OMA.S_oeis_a267258.state 111) (n + 1) i = Ours.update ((OMA.S_oeis_a267258.state 111) n (i - 1)) ((OMA.S_oeis_a267258.state 111) n i) ((OMA.S_oeis_a267258.state 111) n (i + 1)) := by
  rfl

lemma st_outside (n : ℕ) (i : ℤ) (hi : i < -(n : ℤ) ∨ (n : ℤ) < i) :
    (OMA.S_oeis_a267258.state 111) n i = (Ours.row n).1 := by
  induction n generalizing i with
  | zero =>
    have hne : i ≠ 0 := by omega
    simp [OMA.S_oeis_a267258.state, Ours.row, hne]
  | succ n ih =>
    rw [st_step, Ours.RowProof.row_next, Ours.RowProof.advance]
    have h1 : (OMA.S_oeis_a267258.state 111) n (i - 1) = (Ours.row n).1 := ih (i - 1) (by omega)
    have h2 : (OMA.S_oeis_a267258.state 111) n i = (Ours.row n).1 := ih i (by omega)
    have h3 : (OMA.S_oeis_a267258.state 111) n (i + 1) = (Ours.row n).1 := ih (i + 1) (by omega)
    rw [h1, h2, h3]

lemma row_eq_seg (n : ℕ) :
    (Ours.row n).2 = seg (-(n : ℤ)) (2 * n + 1) ((OMA.S_oeis_a267258.state 111) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Ours.RowProof.row_next, Ours.RowProof.advance, ih]
    dsimp only
    have hr1 : (OMA.S_oeis_a267258.state 111) n (-(n : ℤ) + (2 * n + 1 : ℕ)) = (Ours.row n).1 :=
      st_outside n _ (by omega)
    have hr2 : (OMA.S_oeis_a267258.state 111) n (-(n : ℤ) + (2 * n + 1 : ℕ) + 1) = (Ours.row n).1 :=
      st_outside n _ (by omega)
    rw [seg_append_two (-(n : ℤ)) (2 * n + 1) ((OMA.S_oeis_a267258.state 111) n) (Ours.row n).1 hr1 hr2]
    have hl1 : (Ours.row n).1 = (OMA.S_oeis_a267258.state 111) n (-(n : ℤ) - 2) :=
      (st_outside n _ (by omega)).symm
    have hl2 : (Ours.row n).1 = (OMA.S_oeis_a267258.state 111) n (-(n : ℤ) - 1) :=
      (st_outside n _ (by omega)).symm
    conv_lhs =>
      arg 1; rw [hl1]
    conv_lhs =>
      arg 2; rw [hl2]
    rw [sweep_seg_ours]
    have ha : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
    have hm : 2 * n + 1 + 2 = 2 * (n + 1) + 1 := by omega
    have hf : (fun i => Ours.update ((OMA.S_oeis_a267258.state 111) n (i - 1)) ((OMA.S_oeis_a267258.state 111) n i) ((OMA.S_oeis_a267258.state 111) n (i + 1))) =
        (OMA.S_oeis_a267258.state 111) (n + 1) := by
      funext i
      exact (st_step n i).symm
    rw [ha, hm, hf]


lemma c_eq (n : ℕ) : OMA.S_oeis_a267258.c n = Ours.centre n := by
  rw [Ours.centre, row_eq_seg, seg_getElem! (-(n : ℤ)) (2 * n + 1) (OMA.S_oeis_a267258.state 111 n) n (by omega)]
  have h0 : -(n : ℤ) + (n : ℤ) = 0 := by ring
  rw [h0]
  rfl

lemma a_eq (n : ℕ) : OMA.S_oeis_a267258.a n = Ours.a n := by
  induction n with
  | zero => simp [OMA.S_oeis_a267258.a, Ours.a, c_eq]
  | succ n ih =>
    rw [OMA.S_oeis_a267258.a, Finset.sum_range_succ, Ours.a, ← ih, OMA.S_oeis_a267258.a, Finset.mul_sum, c_eq]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
      ring
    · simp

lemma main_proof : type_of% @OMA.S_oeis_a267258.main := by
  have ha : OMA.S_oeis_a267258.a = Ours.a := funext a_eq
  dsimp only [OMA.S_oeis_a267258.A]
  rw [ha]
  exact ⟨Ours.RowProof.claim0, ps_eq_mul_inv Ours.RowProof.generating_function (by simp)⟩

end BridgeProof

theorem OMA.solution : type_of% @OMA.S_oeis_a267258.main := BridgeProof.main_proof
