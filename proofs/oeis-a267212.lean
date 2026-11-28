import OMAStatements.S_oeis_a267212

namespace Ours_oeis_a267212

def update (l c r : Bool) : Bool :=
  (109 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

def sweep (l c : Bool) : List Bool → List Bool
  | [] => []
  | r :: tail => update l c r :: sweep c r tail


def row : ℕ → Bool × List Bool
  | 0 => (false, [true])
  | n + 1 =>
    let (b, w) := row n
    (update b b b, sweep b b (w ++ [b, b]))

def countRow (n : ℕ) : ℕ := (row n).2.count true

def a : ℕ → ℕ
  | 0 => countRow 0
  | n + 1 => a n + countRow (n + 1)

end Ours_oeis_a267212

open Ours_oeis_a267212

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

lemma seed0 : row 0 = (false, [true]) := rfl

lemma seed1 : row 1 = (true, [false, true, false]) :=
  (row_next 0).trans (by rw [seed0]; rfl)

lemma seed2 : row 2 = (false, [true, true, true, true, true]) :=
  (row_next 1).trans (by rw [seed1]; rfl)

lemma seed3 : row 3 = (true, [false, true, false, false, false, true, false]) :=
  (row_next 2).trans (by rw [seed2]; rfl)

lemma seed4 : row 4 = (false, [true, true, true, false, true, false, true, true, true]) :=
  (row_next 3).trans (by rw [seed3]; rfl)

lemma seed5 : row 5 = (true, [false, true, false, true, true, true, true, true, false, true, false]) :=
  (row_next 4).trans (by rw [seed4]; rfl)

lemma seed6 : row 6 = (false, [true, true, true, true, true, false, false, false, true, true, true, true, true]) :=
  (row_next 5).trans (by rw [seed5]; rfl)

lemma seed7 : row 7 = (true, [false, true, false, false, false, true, false, true, false, true, false, false, false, true, false]) :=
  (row_next 6).trans (by rw [seed6]; rfl)

lemma seed8 : row 8 = (false, [true, true, true, false, true, false, true, true, true, true, true, false, true, false, true, true, true]) :=
  (row_next 7).trans (by rw [seed7]; rfl)

lemma seed9 : row 9 = (true, [false, true, false, true, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false]) :=
  (row_next 8).trans (by rw [seed8]; rfl)

lemma seed10 : row 10 = (false, [true, true, true, true, true, false, false, false, true, false, true, false, true, false, false, false, true, true, true, true, true]) :=
  (row_next 9).trans (by rw [seed9]; rfl)

lemma seed11 : row 11 = (true, [false, true, false, false, false, true, false, true, false, true, true, true, true, true, false, true, false, true, false, false, false, true, false]) :=
  (row_next 10).trans (by rw [seed10]; rfl)

lemma seed12 : row 12 = (false, [true, true, true, false, true, false, true, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true]) :=
  (row_next 11).trans (by rw [seed11]; rfl)

lemma seed13 : row 13 = (true, [false, true, false, true, true, true, true, true, false, false, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, true, false]) :=
  (row_next 12).trans (by rw [seed12]; rfl)

lemma seed14 : row 14 = (false, [true, true, true, true, true, false, false, false, true, false, true, false, true, true, true, true, true, false, true, false, true, false, false, false, true, true, true, true, true]) :=
  (row_next 13).trans (by rw [seed13]; rfl)

lemma seed15 : row 15 = (true, [false, true, false, false, false, true, false, true, false, true, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, false, true, false]) :=
  (row_next 14).trans (by rw [seed14]; rfl)

lemma seed16 : row 16 = (false, [true, true, true, false, true, false, true, true, true, true, true, false, false, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true]) :=
  (row_next 15).trans (by rw [seed15]; rfl)

lemma seed17 : row 17 = (true, [false, true, false, true, true, true, true, true, false, false, false, true, false, true, false, true, true, true, true, true, false, true, false, true, false, false, false, true, true, true, true, true, false, true, false]) :=
  (row_next 16).trans (by rw [seed16]; rfl)

lemma seed18 : row 18 = (false, [true, true, true, true, true, false, false, false, true, false, true, false, true, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, false, true, true, true, true, true]) :=
  (row_next 17).trans (by rw [seed17]; rfl)

lemma seed19 : row 19 = (true, [false, true, false, false, false, true, false, true, false, true, true, true, true, true, false, false, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, false, true, false]) :=
  (row_next 18).trans (by rw [seed18]; rfl)

lemma seed20 : row 20 = (false, [true, true, true, false, true, false, true, true, true, true, true, false, false, false, true, false, true, false, true, true, true, true, true, false, true, false, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true]) :=
  (row_next 19).trans (by rw [seed19]; rfl)

lemma sweepBlock0 (k : ℕ) (t : List Bool) :
    sweep false false (blocks [false, true, true, true, true, true, false, true, false, true, false, false] k t) =
      blocks [true, false, true, false, false, false, true, true, true, true, true, false] k (sweep false false t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock1 (k : ℕ) (t : List Bool) :
    sweep false false (blocks [true, true, true, true, true, false, true, false, true, false, false, false] k t) =
      blocks [false, true, false, false, false, true, true, true, true, true, false, true] k (sweep false false t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock2 (k : ℕ) (t : List Bool) :
    sweep false true (blocks [false, false, false, true, true, true, true, true, false, true, false, true] k t) =
      blocks [true, false, true, false, true, false, false, false, true, true, true, true] k (sweep false true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock3 (k : ℕ) (t : List Bool) :
    sweep false true (blocks [false, true, false, false, false, true, true, true, true, true, false, true] k t) =
      blocks [true, true, true, false, true, false, true, false, false, false, true, true] k (sweep false true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock4 (k : ℕ) (t : List Bool) :
    sweep false true (blocks [false, true, false, true, true, true, true, true, false, false, false, true] k t) =
      blocks [true, true, true, true, true, false, false, false, true, false, true, false] k (sweep false true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock5 (k : ℕ) (t : List Bool) :
    sweep false true (blocks [true, true, true, true, false, true, false, true, false, false, false, true] k t) =
      blocks [true, false, false, false, true, true, true, true, true, false, true, false] k (sweep false true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock6 (k : ℕ) (t : List Bool) :
    sweep true false (blocks [false, false, true, false, true, false, true, true, true, true, true, false] k t) =
      blocks [false, true, false, true, true, true, true, true, false, false, false, true] k (sweep true false t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock7 (k : ℕ) (t : List Bool) :
    sweep true false (blocks [false, false, true, true, true, true, true, false, true, false, true, false] k t) =
      blocks [false, true, false, true, false, false, false, true, true, true, true, true] k (sweep true false t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock8 (k : ℕ) (t : List Bool) :
    sweep true false (blocks [true, false, false, false, true, true, true, true, true, false, true, false] k t) =
      blocks [true, true, false, true, false, true, false, false, false, true, true, true] k (sweep true false t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock9 (k : ℕ) (t : List Bool) :
    sweep true false (blocks [true, false, true, false, false, false, true, true, true, true, true, false] k t) =
      blocks [true, true, true, true, false, true, false, true, false, false, false, true] k (sweep true false t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock10 (k : ℕ) (t : List Bool) :
    sweep true false (blocks [true, true, true, true, true, false, false, false, true, false, true, false] k t) =
      blocks [true, true, false, false, false, true, false, true, false, true, true, true] k (sweep true false t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock11 (k : ℕ) (t : List Bool) :
    sweep true true (blocks [false, true, false, true, false, false, false, true, true, true, true, true] k t) =
      blocks [true, true, true, true, true, false, true, false, true, false, false, false] k (sweep true true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock12 (k : ℕ) (t : List Bool) :
    sweep true true (blocks [true, false, true, false, true, false, false, false, true, true, true, true] k t) =
      blocks [false, true, true, true, true, true, false, true, false, true, false, false] k (sweep true true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock13 (k : ℕ) (t : List Bool) :
    sweep true true (blocks [true, true, false, false, false, true, false, true, false, true, true, true] k t) =
      blocks [false, false, true, false, true, false, true, true, true, true, true, false] k (sweep true true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock14 (k : ℕ) (t : List Bool) :
    sweep true true (blocks [true, true, false, true, false, true, false, false, false, true, true, true] k t) =
      blocks [false, false, true, true, true, true, true, false, true, false, true, false] k (sweep true true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma sweepBlock15 (k : ℕ) (t : List Bool) :
    sweep true true (blocks [true, true, true, false, true, false, true, false, false, false, true, true] k t) =
      blocks [false, false, false, true, true, true, true, true, false, true, false, true] k (sweep true true t) :=
  sweep_blocks _ _ _ _ (fun _ => rfl) k t

lemma rotateBlock0 (k : ℕ) (t : List Bool) :
    blocks [false, false, false, true, false, true, false, true, true, true, true, true] k (false :: t) =
      false :: blocks [false, false, true, false, true, false, true, true, true, true, true, false] k t :=
  blocks_rotate _ [false, false, true, false, true, false, true, true, true, true, true] k t

lemma rotateBlock1 (k : ℕ) (t : List Bool) :
    blocks [false, false, false, true, true, true, true, true, false, true, false, true] k (false :: t) =
      false :: blocks [false, false, true, true, true, true, true, false, true, false, true, false] k t :=
  blocks_rotate _ [false, false, true, true, true, true, true, false, true, false, true] k t

lemma rotateBlock2 (k : ℕ) (t : List Bool) :
    blocks [false, false, true, false, true, false, true, true, true, true, true, false] k (false :: t) =
      false :: blocks [false, true, false, true, false, true, true, true, true, true, false, false] k t :=
  blocks_rotate _ [false, true, false, true, false, true, true, true, true, true, false] k t

lemma rotateBlock3 (k : ℕ) (t : List Bool) :
    blocks [false, false, true, true, true, true, true, false, true, false, true, false] k (false :: t) =
      false :: blocks [false, true, true, true, true, true, false, true, false, true, false, false] k t :=
  blocks_rotate _ [false, true, true, true, true, true, false, true, false, true, false] k t

lemma rotateBlock4 (k : ℕ) (t : List Bool) :
    blocks [false, true, false, false, false, true, true, true, true, true, false, true] k (false :: t) =
      false :: blocks [true, false, false, false, true, true, true, true, true, false, true, false] k t :=
  blocks_rotate _ [true, false, false, false, true, true, true, true, true, false, true] k t

lemma rotateBlock5 (k : ℕ) (t : List Bool) :
    blocks [false, true, false, true, false, false, false, true, true, true, true, true] k (false :: t) =
      false :: blocks [true, false, true, false, false, false, true, true, true, true, true, false] k t :=
  blocks_rotate _ [true, false, true, false, false, false, true, true, true, true, true] k t

lemma rotateBlock6 (k : ℕ) (t : List Bool) :
    blocks [false, true, false, true, false, true, true, true, true, true, false, false] k (false :: t) =
      false :: blocks [true, false, true, false, true, true, true, true, true, false, false, false] k t :=
  blocks_rotate _ [true, false, true, false, true, true, true, true, true, false, false] k t

lemma rotateBlock7 (k : ℕ) (t : List Bool) :
    blocks [false, true, false, true, true, true, true, true, false, false, false, true] k (false :: t) =
      false :: blocks [true, false, true, true, true, true, true, false, false, false, true, false] k t :=
  blocks_rotate _ [true, false, true, true, true, true, true, false, false, false, true] k t

lemma rotateBlock8 (k : ℕ) (t : List Bool) :
    blocks [false, true, true, true, true, true, false, false, false, true, false, true] k (false :: t) =
      false :: blocks [true, true, true, true, true, false, false, false, true, false, true, false] k t :=
  blocks_rotate _ [true, true, true, true, true, false, false, false, true, false, true] k t

lemma rotateBlock9 (k : ℕ) (t : List Bool) :
    blocks [false, true, true, true, true, true, false, true, false, true, false, false] k (false :: t) =
      false :: blocks [true, true, true, true, true, false, true, false, true, false, false, false] k t :=
  blocks_rotate _ [true, true, true, true, true, false, true, false, true, false, false] k t

lemma rotateBlock10 (k : ℕ) (t : List Bool) :
    blocks [true, false, false, false, true, false, true, false, true, true, true, true] k (true :: t) =
      true :: blocks [false, false, false, true, false, true, false, true, true, true, true, true] k t :=
  blocks_rotate _ [false, false, false, true, false, true, false, true, true, true, true] k t

lemma rotateBlock11 (k : ℕ) (t : List Bool) :
    blocks [true, false, false, false, true, true, true, true, true, false, true, false] k (true :: t) =
      true :: blocks [false, false, false, true, true, true, true, true, false, true, false, true] k t :=
  blocks_rotate _ [false, false, false, true, true, true, true, true, false, true, false] k t

lemma rotateBlock12 (k : ℕ) (t : List Bool) :
    blocks [true, false, true, false, false, false, true, true, true, true, true, false] k (true :: t) =
      true :: blocks [false, true, false, false, false, true, true, true, true, true, false, true] k t :=
  blocks_rotate _ [false, true, false, false, false, true, true, true, true, true, false] k t

lemma rotateBlock13 (k : ℕ) (t : List Bool) :
    blocks [true, false, true, false, true, false, false, false, true, true, true, true] k (true :: t) =
      true :: blocks [false, true, false, true, false, false, false, true, true, true, true, true] k t :=
  blocks_rotate _ [false, true, false, true, false, false, false, true, true, true, true] k t

lemma rotateBlock14 (k : ℕ) (t : List Bool) :
    blocks [true, false, true, false, true, true, true, true, true, false, false, false] k (true :: t) =
      true :: blocks [false, true, false, true, true, true, true, true, false, false, false, true] k t :=
  blocks_rotate _ [false, true, false, true, true, true, true, true, false, false, false] k t

lemma rotateBlock15 (k : ℕ) (t : List Bool) :
    blocks [true, false, true, true, true, true, true, false, false, false, true, false] k (true :: t) =
      true :: blocks [false, true, true, true, true, true, false, false, false, true, false, true] k t :=
  blocks_rotate _ [false, true, true, true, true, true, false, false, false, true, false] k t

lemma rotateBlock16 (k : ℕ) (t : List Bool) :
    blocks [true, true, false, false, false, true, false, true, false, true, true, true] k (true :: t) =
      true :: blocks [true, false, false, false, true, false, true, false, true, true, true, true] k t :=
  blocks_rotate _ [true, false, false, false, true, false, true, false, true, true, true] k t

lemma rotateBlock17 (k : ℕ) (t : List Bool) :
    blocks [true, true, false, true, false, true, false, false, false, true, true, true] k (true :: t) =
      true :: blocks [true, false, true, false, true, false, false, false, true, true, true, true] k t :=
  blocks_rotate _ [true, false, true, false, true, false, false, false, true, true, true] k t

lemma rotateBlock18 (k : ℕ) (t : List Bool) :
    blocks [true, true, true, false, false, false, true, false, true, false, true, true] k (true :: t) =
      true :: blocks [true, true, false, false, false, true, false, true, false, true, true, true] k t :=
  blocks_rotate _ [true, true, false, false, false, true, false, true, false, true, true] k t

lemma rotateBlock19 (k : ℕ) (t : List Bool) :
    blocks [true, true, true, false, true, false, true, false, false, false, true, true] k (true :: t) =
      true :: blocks [true, true, false, true, false, true, false, false, false, true, true, true] k t :=
  blocks_rotate _ [true, true, false, true, false, true, false, false, false, true, true] k t

lemma rotateBlock20 (k : ℕ) (t : List Bool) :
    blocks [true, true, true, true, false, false, false, true, false, true, false, true] k (true :: t) =
      true :: blocks [true, true, true, false, false, false, true, false, true, false, true, true] k t :=
  blocks_rotate _ [true, true, true, false, false, false, true, false, true, false, true] k t

lemma rotateBlock21 (k : ℕ) (t : List Bool) :
    blocks [true, true, true, true, false, true, false, true, false, false, false, true] k (true :: t) =
      true :: blocks [true, true, true, false, true, false, true, false, false, false, true, true] k t :=
  blocks_rotate _ [true, true, true, false, true, false, true, false, false, false, true] k t

lemma rotateBlock22 (k : ℕ) (t : List Bool) :
    blocks [true, true, true, true, true, false, false, false, true, false, true, false] k (true :: t) =
      true :: blocks [true, true, true, true, false, false, false, true, false, true, false, true] k t :=
  blocks_rotate _ [true, true, true, true, false, false, false, true, false, true, false] k t

lemma rotateBlock23 (k : ℕ) (t : List Bool) :
    blocks [true, true, true, true, true, false, true, false, true, false, false, false] k (true :: t) =
      true :: blocks [true, true, true, true, false, true, false, true, false, false, false, true] k t :=
  blocks_rotate _ [true, true, true, true, false, true, false, true, false, false, false] k t

lemma update000 : update false false false = true := by decide
lemma update001 : update false false true = false := by decide
lemma update010 : update false true false = true := by decide
lemma update011 : update false true true = true := by decide
lemma update100 : update true false false = false := by decide
lemma update101 : update true false true = true := by decide
lemma update110 : update true true false = true := by decide
lemma update111 : update true true true = false := by decide

def phase0 (k : ℕ) : Bool × List Bool :=
  (true, false :: true :: false :: true :: true :: true :: true :: true :: false :: false :: false :: true :: (blocks [false, true, false, true, true, true, true, true, false, false, false, true] k (true :: true :: true :: true :: false :: true :: false :: (blocks [true, false, false, false, true, true, true, true, true, false, true, false] k ([])))))

def phase1 (k : ℕ) : Bool × List Bool :=
  (false, true :: true :: true :: true :: true :: false :: false :: false :: true :: false :: true :: false :: (blocks [true, true, true, true, true, false, false, false, true, false, true, false] k (true :: false :: false :: false :: true :: true :: true :: (blocks [true, true, false, true, false, true, false, false, false, true, true, true] k (true :: true :: [])))))

def phase2 (k : ℕ) : Bool × List Bool :=
  (true, false :: true :: false :: false :: false :: true :: false :: true :: false :: true :: true :: true :: (blocks [true, true, false, false, false, true, false, true, false, true, true, true] k (true :: true :: false :: true :: false :: true :: false :: (blocks [false, false, true, true, true, true, true, false, true, false, true, false] k (false :: false :: true :: false :: [])))))

def phase3 (k : ℕ) : Bool × List Bool :=
  (false, true :: true :: true :: false :: true :: false :: true :: true :: true :: true :: true :: false :: (blocks [false, false, true, false, true, false, true, true, true, true, true, false] k (false :: false :: true :: true :: true :: true :: true :: (blocks [false, true, false, true, false, false, false, true, true, true, true, true] k (false :: true :: false :: true :: true :: true :: [])))))

def phase4 (k : ℕ) : Bool × List Bool :=
  (true, false :: true :: false :: true :: true :: true :: true :: true :: false :: false :: false :: true :: (blocks [false, true, false, true, true, true, true, true, false, false, false, true] k (false :: true :: false :: true :: false :: false :: false :: (blocks [true, true, true, true, true, false, true, false, true, false, false, false] k (true :: true :: true :: true :: true :: false :: true :: false :: [])))))

def phase5 (k : ℕ) : Bool × List Bool :=
  (false, true :: true :: true :: true :: true :: false :: false :: false :: true :: false :: true :: false :: (blocks [true, true, true, true, true, false, false, false, true, false, true, false] k (true :: true :: true :: true :: true :: false :: true :: (blocks [false, true, false, false, false, true, true, true, true, true, false, true] k (false :: true :: false :: false :: false :: true :: true :: true :: true :: true :: [])))))

def phase6 (k : ℕ) : Bool × List Bool :=
  (true, false :: true :: false :: false :: false :: true :: false :: true :: false :: true :: true :: true :: (blocks [true, true, false, false, false, true, false, true, false, true, true, true] k (true :: true :: false :: false :: false :: true :: true :: (blocks [true, true, true, false, true, false, true, false, false, false, true, true] k (true :: true :: true :: false :: true :: false :: true :: false :: false :: false :: true :: false :: [])))))

def phase7 (k : ℕ) : Bool × List Bool :=
  (false, true :: true :: true :: false :: true :: false :: true :: true :: true :: true :: true :: false :: (blocks [false, false, true, false, true, false, true, true, true, true, true, false] k (false :: false :: true :: false :: true :: false :: true :: (blocks [false, false, false, true, true, true, true, true, false, true, false, true] k (false :: false :: false :: true :: true :: true :: true :: true :: false :: true :: false :: true :: true :: true :: [])))))

def phase8 (k : ℕ) : Bool × List Bool :=
  (true, false :: true :: false :: true :: true :: true :: true :: true :: false :: false :: false :: true :: (blocks [false, true, false, true, true, true, true, true, false, false, false, true] k (false :: true :: false :: true :: true :: true :: true :: (blocks [true, false, true, false, true, false, false, false, true, true, true, true] k (true :: false :: true :: false :: true :: false :: false :: false :: true :: true :: true :: true :: true :: false :: true :: false :: [])))))

def phase9 (k : ℕ) : Bool × List Bool :=
  (false, true :: true :: true :: true :: true :: false :: false :: false :: true :: false :: true :: false :: (blocks [true, true, true, true, true, false, false, false, true, false, true, false] k (true :: true :: true :: true :: true :: false :: false :: (blocks [false, true, true, true, true, true, false, true, false, true, false, false] k (false :: true :: true :: true :: true :: true :: false :: true :: false :: true :: false :: false :: false :: true :: true :: true :: true :: true :: [])))))

def phase10 (k : ℕ) : Bool × List Bool :=
  (true, false :: true :: false :: false :: false :: true :: false :: true :: false :: true :: true :: true :: (blocks [true, true, false, false, false, true, false, true, false, true, true, true] k (true :: true :: false :: false :: false :: true :: false :: (blocks [true, false, true, false, false, false, true, true, true, true, true, false] k (true :: false :: true :: false :: false :: false :: true :: true :: true :: true :: true :: false :: true :: false :: true :: false :: false :: false :: true :: false :: [])))))

def phase11 (k : ℕ) : Bool × List Bool :=
  (false, true :: true :: true :: false :: true :: false :: true :: true :: true :: true :: true :: false :: (blocks [false, false, true, false, true, false, true, true, true, true, true, false] k (false :: false :: true :: false :: true :: false :: true :: (blocks [true, true, true, true, false, true, false, true, false, false, false, true] k (true :: true :: true :: true :: false :: true :: false :: true :: false :: false :: false :: true :: true :: true :: true :: true :: false :: true :: false :: true :: true :: true :: [])))))

lemma advance0 (k : ℕ) : advance (phase0 k) = phase1 k := by
  simp only [advance, phase0, phase1, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, sweepBlock3, sweepBlock4, sweepBlock5, sweepBlock6, sweepBlock7, sweepBlock8, sweepBlock9, sweepBlock10, sweepBlock11, sweepBlock12, sweepBlock13, sweepBlock14, sweepBlock15, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2, rotateBlock3, rotateBlock4, rotateBlock5, rotateBlock6, rotateBlock7, rotateBlock8, rotateBlock9, rotateBlock10, rotateBlock11, rotateBlock12, rotateBlock13, rotateBlock14, rotateBlock15, rotateBlock16, rotateBlock17, rotateBlock18, rotateBlock19, rotateBlock20, rotateBlock21, rotateBlock22, rotateBlock23]

lemma advance1 (k : ℕ) : advance (phase1 k) = phase2 k := by
  simp only [advance, phase1, phase2, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, sweepBlock3, sweepBlock4, sweepBlock5, sweepBlock6, sweepBlock7, sweepBlock8, sweepBlock9, sweepBlock10, sweepBlock11, sweepBlock12, sweepBlock13, sweepBlock14, sweepBlock15, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2, rotateBlock3, rotateBlock4, rotateBlock5, rotateBlock6, rotateBlock7, rotateBlock8, rotateBlock9, rotateBlock10, rotateBlock11, rotateBlock12, rotateBlock13, rotateBlock14, rotateBlock15, rotateBlock16, rotateBlock17, rotateBlock18, rotateBlock19, rotateBlock20, rotateBlock21, rotateBlock22, rotateBlock23]

lemma advance2 (k : ℕ) : advance (phase2 k) = phase3 k := by
  simp only [advance, phase2, phase3, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, sweepBlock3, sweepBlock4, sweepBlock5, sweepBlock6, sweepBlock7, sweepBlock8, sweepBlock9, sweepBlock10, sweepBlock11, sweepBlock12, sweepBlock13, sweepBlock14, sweepBlock15, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2, rotateBlock3, rotateBlock4, rotateBlock5, rotateBlock6, rotateBlock7, rotateBlock8, rotateBlock9, rotateBlock10, rotateBlock11, rotateBlock12, rotateBlock13, rotateBlock14, rotateBlock15, rotateBlock16, rotateBlock17, rotateBlock18, rotateBlock19, rotateBlock20, rotateBlock21, rotateBlock22, rotateBlock23]

lemma advance3 (k : ℕ) : advance (phase3 k) = phase4 k := by
  simp only [advance, phase3, phase4, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, sweepBlock3, sweepBlock4, sweepBlock5, sweepBlock6, sweepBlock7, sweepBlock8, sweepBlock9, sweepBlock10, sweepBlock11, sweepBlock12, sweepBlock13, sweepBlock14, sweepBlock15, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2, rotateBlock3, rotateBlock4, rotateBlock5, rotateBlock6, rotateBlock7, rotateBlock8, rotateBlock9, rotateBlock10, rotateBlock11, rotateBlock12, rotateBlock13, rotateBlock14, rotateBlock15, rotateBlock16, rotateBlock17, rotateBlock18, rotateBlock19, rotateBlock20, rotateBlock21, rotateBlock22, rotateBlock23]

lemma advance4 (k : ℕ) : advance (phase4 k) = phase5 k := by
  simp only [advance, phase4, phase5, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, sweepBlock3, sweepBlock4, sweepBlock5, sweepBlock6, sweepBlock7, sweepBlock8, sweepBlock9, sweepBlock10, sweepBlock11, sweepBlock12, sweepBlock13, sweepBlock14, sweepBlock15, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2, rotateBlock3, rotateBlock4, rotateBlock5, rotateBlock6, rotateBlock7, rotateBlock8, rotateBlock9, rotateBlock10, rotateBlock11, rotateBlock12, rotateBlock13, rotateBlock14, rotateBlock15, rotateBlock16, rotateBlock17, rotateBlock18, rotateBlock19, rotateBlock20, rotateBlock21, rotateBlock22, rotateBlock23]

lemma advance5 (k : ℕ) : advance (phase5 k) = phase6 k := by
  simp only [advance, phase5, phase6, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, sweepBlock3, sweepBlock4, sweepBlock5, sweepBlock6, sweepBlock7, sweepBlock8, sweepBlock9, sweepBlock10, sweepBlock11, sweepBlock12, sweepBlock13, sweepBlock14, sweepBlock15, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2, rotateBlock3, rotateBlock4, rotateBlock5, rotateBlock6, rotateBlock7, rotateBlock8, rotateBlock9, rotateBlock10, rotateBlock11, rotateBlock12, rotateBlock13, rotateBlock14, rotateBlock15, rotateBlock16, rotateBlock17, rotateBlock18, rotateBlock19, rotateBlock20, rotateBlock21, rotateBlock22, rotateBlock23]

lemma advance6 (k : ℕ) : advance (phase6 k) = phase7 k := by
  simp only [advance, phase6, phase7, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, sweepBlock3, sweepBlock4, sweepBlock5, sweepBlock6, sweepBlock7, sweepBlock8, sweepBlock9, sweepBlock10, sweepBlock11, sweepBlock12, sweepBlock13, sweepBlock14, sweepBlock15, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2, rotateBlock3, rotateBlock4, rotateBlock5, rotateBlock6, rotateBlock7, rotateBlock8, rotateBlock9, rotateBlock10, rotateBlock11, rotateBlock12, rotateBlock13, rotateBlock14, rotateBlock15, rotateBlock16, rotateBlock17, rotateBlock18, rotateBlock19, rotateBlock20, rotateBlock21, rotateBlock22, rotateBlock23]

lemma advance7 (k : ℕ) : advance (phase7 k) = phase8 k := by
  simp only [advance, phase7, phase8, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, sweepBlock3, sweepBlock4, sweepBlock5, sweepBlock6, sweepBlock7, sweepBlock8, sweepBlock9, sweepBlock10, sweepBlock11, sweepBlock12, sweepBlock13, sweepBlock14, sweepBlock15, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2, rotateBlock3, rotateBlock4, rotateBlock5, rotateBlock6, rotateBlock7, rotateBlock8, rotateBlock9, rotateBlock10, rotateBlock11, rotateBlock12, rotateBlock13, rotateBlock14, rotateBlock15, rotateBlock16, rotateBlock17, rotateBlock18, rotateBlock19, rotateBlock20, rotateBlock21, rotateBlock22, rotateBlock23]

lemma advance8 (k : ℕ) : advance (phase8 k) = phase9 k := by
  simp only [advance, phase8, phase9, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, sweepBlock3, sweepBlock4, sweepBlock5, sweepBlock6, sweepBlock7, sweepBlock8, sweepBlock9, sweepBlock10, sweepBlock11, sweepBlock12, sweepBlock13, sweepBlock14, sweepBlock15, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2, rotateBlock3, rotateBlock4, rotateBlock5, rotateBlock6, rotateBlock7, rotateBlock8, rotateBlock9, rotateBlock10, rotateBlock11, rotateBlock12, rotateBlock13, rotateBlock14, rotateBlock15, rotateBlock16, rotateBlock17, rotateBlock18, rotateBlock19, rotateBlock20, rotateBlock21, rotateBlock22, rotateBlock23]

lemma advance9 (k : ℕ) : advance (phase9 k) = phase10 k := by
  simp only [advance, phase9, phase10, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, sweepBlock3, sweepBlock4, sweepBlock5, sweepBlock6, sweepBlock7, sweepBlock8, sweepBlock9, sweepBlock10, sweepBlock11, sweepBlock12, sweepBlock13, sweepBlock14, sweepBlock15, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2, rotateBlock3, rotateBlock4, rotateBlock5, rotateBlock6, rotateBlock7, rotateBlock8, rotateBlock9, rotateBlock10, rotateBlock11, rotateBlock12, rotateBlock13, rotateBlock14, rotateBlock15, rotateBlock16, rotateBlock17, rotateBlock18, rotateBlock19, rotateBlock20, rotateBlock21, rotateBlock22, rotateBlock23]

lemma advance10 (k : ℕ) : advance (phase10 k) = phase11 k := by
  simp only [advance, phase10, phase11, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, sweepBlock3, sweepBlock4, sweepBlock5, sweepBlock6, sweepBlock7, sweepBlock8, sweepBlock9, sweepBlock10, sweepBlock11, sweepBlock12, sweepBlock13, sweepBlock14, sweepBlock15, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2, rotateBlock3, rotateBlock4, rotateBlock5, rotateBlock6, rotateBlock7, rotateBlock8, rotateBlock9, rotateBlock10, rotateBlock11, rotateBlock12, rotateBlock13, rotateBlock14, rotateBlock15, rotateBlock16, rotateBlock17, rotateBlock18, rotateBlock19, rotateBlock20, rotateBlock21, rotateBlock22, rotateBlock23]

lemma advance11 (k : ℕ) : advance (phase11 k) = phase0 (k + 1) := by
  simp only [advance, phase11, phase0, List.cons_append, List.nil_append, blocks_append, sweep, sweepBlock0, sweepBlock1, sweepBlock2, sweepBlock3, sweepBlock4, sweepBlock5, sweepBlock6, sweepBlock7, sweepBlock8, sweepBlock9, sweepBlock10, sweepBlock11, sweepBlock12, sweepBlock13, sweepBlock14, sweepBlock15, update000, update001, update010, update011, update100, update101, update110, update111]
  all_goals simp only [blocks, List.cons_append, List.nil_append, rotateBlock0, rotateBlock1, rotateBlock2, rotateBlock3, rotateBlock4, rotateBlock5, rotateBlock6, rotateBlock7, rotateBlock8, rotateBlock9, rotateBlock10, rotateBlock11, rotateBlock12, rotateBlock13, rotateBlock14, rotateBlock15, rotateBlock16, rotateBlock17, rotateBlock18, rotateBlock19, rotateBlock20, rotateBlock21, rotateBlock22, rotateBlock23]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
lemma row_phases (k : ℕ) :
    row (12 * k + 9) = phase0 k ∧
    row (12 * k + 10) = phase1 k ∧
    row (12 * k + 11) = phase2 k ∧
    row (12 * k + 12) = phase3 k ∧
    row (12 * k + 13) = phase4 k ∧
    row (12 * k + 14) = phase5 k ∧
    row (12 * k + 15) = phase6 k ∧
    row (12 * k + 16) = phase7 k ∧
    row (12 * k + 17) = phase8 k ∧
    row (12 * k + 18) = phase9 k ∧
    row (12 * k + 19) = phase10 k ∧
    row (12 * k + 20) = phase11 k := by
  induction k with
  | zero => exact ⟨seed9, seed10, seed11, seed12, seed13, seed14, seed15, seed16, seed17, seed18, seed19, seed20⟩
  | succ k ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, old⟩ := ih
    have step0 : row (12 * (k + 1) + 9) = phase0 (k + 1) := by
      rw [show (12 * (k + 1) + 9) = (12 * k + 20) + 1 by omega, row_next (12 * k + 20), old, advance11]
    have step1 : row (12 * (k + 1) + 10) = phase1 (k + 1) := by
      rw [show (12 * (k + 1) + 10) = (12 * (k + 1) + 9) + 1 by omega, row_next (12 * (k + 1) + 9), step0, advance0]
    have step2 : row (12 * (k + 1) + 11) = phase2 (k + 1) := by
      rw [show (12 * (k + 1) + 11) = (12 * (k + 1) + 10) + 1 by omega, row_next (12 * (k + 1) + 10), step1, advance1]
    have step3 : row (12 * (k + 1) + 12) = phase3 (k + 1) := by
      rw [show (12 * (k + 1) + 12) = (12 * (k + 1) + 11) + 1 by omega, row_next (12 * (k + 1) + 11), step2, advance2]
    have step4 : row (12 * (k + 1) + 13) = phase4 (k + 1) := by
      rw [show (12 * (k + 1) + 13) = (12 * (k + 1) + 12) + 1 by omega, row_next (12 * (k + 1) + 12), step3, advance3]
    have step5 : row (12 * (k + 1) + 14) = phase5 (k + 1) := by
      rw [show (12 * (k + 1) + 14) = (12 * (k + 1) + 13) + 1 by omega, row_next (12 * (k + 1) + 13), step4, advance4]
    have step6 : row (12 * (k + 1) + 15) = phase6 (k + 1) := by
      rw [show (12 * (k + 1) + 15) = (12 * (k + 1) + 14) + 1 by omega, row_next (12 * (k + 1) + 14), step5, advance5]
    have step7 : row (12 * (k + 1) + 16) = phase7 (k + 1) := by
      rw [show (12 * (k + 1) + 16) = (12 * (k + 1) + 15) + 1 by omega, row_next (12 * (k + 1) + 15), step6, advance6]
    have step8 : row (12 * (k + 1) + 17) = phase8 (k + 1) := by
      rw [show (12 * (k + 1) + 17) = (12 * (k + 1) + 16) + 1 by omega, row_next (12 * (k + 1) + 16), step7, advance7]
    have step9 : row (12 * (k + 1) + 18) = phase9 (k + 1) := by
      rw [show (12 * (k + 1) + 18) = (12 * (k + 1) + 17) + 1 by omega, row_next (12 * (k + 1) + 17), step8, advance8]
    have step10 : row (12 * (k + 1) + 19) = phase10 (k + 1) := by
      rw [show (12 * (k + 1) + 19) = (12 * (k + 1) + 18) + 1 by omega, row_next (12 * (k + 1) + 18), step9, advance9]
    have step11 : row (12 * (k + 1) + 20) = phase11 (k + 1) := by
      rw [show (12 * (k + 1) + 20) = (12 * (k + 1) + 19) + 1 by omega, row_next (12 * (k + 1) + 19), step10, advance10]
    exact ⟨step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11⟩

lemma initial0 : a 0 = 1 := by
  rw [a, countRow, seed0] <;> rfl

lemma initial1 : a 1 = 2 := by
  rw [a, initial0, countRow, seed1] <;> rfl

lemma initial2 : a 2 = 7 := by
  rw [a, initial1, countRow, seed2] <;> rfl

lemma initial3 : a 3 = 9 := by
  rw [a, initial2, countRow, seed3] <;> rfl

lemma initial4 : a 4 = 16 := by
  rw [a, initial3, countRow, seed4] <;> rfl

lemma initial5 : a 5 = 23 := by
  rw [a, initial4, countRow, seed5] <;> rfl

lemma initial6 : a 6 = 33 := by
  rw [a, initial5, countRow, seed6] <;> rfl

lemma initial7 : a 7 = 38 := by
  rw [a, initial6, countRow, seed7] <;> rfl

lemma initial8 : a 8 = 51 := by
  rw [a, initial7, countRow, seed8] <;> rfl

lemma initial9 : a 9 = 63 := by
  rw [a, initial8, countRow, seed9] <;> rfl

lemma initial10 : a 10 = 76 := by
  rw [a, initial9, countRow, seed10] <;> rfl

lemma initial11 : a 11 = 87 := by
  rw [a, initial10, countRow, seed11] <;> rfl

lemma initial12 : a 12 = 105 := by
  rw [a, initial11, countRow, seed12] <;> rfl

lemma initial13 : a 13 = 120 := by
  rw [a, initial12, countRow, seed13] <;> rfl

lemma initial14 : a 14 = 139 := by
  rw [a, initial13, countRow, seed14] <;> rfl

lemma initial15 : a 15 = 155 := by
  rw [a, initial14, countRow, seed15] <;> rfl

lemma initial16 : a 16 = 176 := by
  rw [a, initial15, countRow, seed16] <;> rfl

lemma initial17 : a 17 = 197 := by
  rw [a, initial16, countRow, seed17] <;> rfl

lemma initial18 : a 18 = 221 := by
  rw [a, initial17, countRow, seed18] <;> rfl

lemma initial19 : a 19 = 240 := by
  rw [a, initial18, countRow, seed19] <;> rfl

lemma initial20 : a 20 = 267 := by
  rw [a, initial19, countRow, seed20] <;> rfl

lemma count_blocks (w : List Bool) (k : ℕ) (s : List Bool) :
    (blocks w k s).count true = k * w.count true + s.count true := by
  induction k with
  | zero => simp [blocks]
  | succ k ih => simp [blocks, List.count_append, ih, Nat.succ_mul]; omega

lemma rowValue0 (k : ℕ) : (countRow (12 * k + 9) : ℚ) = 12 + 14 * ((k : ℕ) : ℚ) := by
  rw [countRow, (row_phases k).1]
  simp [phase0, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue1 (k : ℕ) : (countRow (12 * k + 10) : ℚ) = 13 + 14 * ((k : ℕ) : ℚ) := by
  rw [countRow, (row_phases k).2.1]
  simp [phase1, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue2 (k : ℕ) : (countRow (12 * k + 11) : ℚ) = 11 + 14 * ((k : ℕ) : ℚ) := by
  rw [countRow, (row_phases k).2.2.1]
  simp [phase2, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue3 (k : ℕ) : (countRow (12 * k + 12) : ℚ) = 18 + 14 * ((k : ℕ) : ℚ) := by
  rw [countRow, (row_phases k).2.2.2.1]
  simp [phase3, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue4 (k : ℕ) : (countRow (12 * k + 13) : ℚ) = 15 + 14 * ((k : ℕ) : ℚ) := by
  rw [countRow, (row_phases k).2.2.2.2.1]
  simp [phase4, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue5 (k : ℕ) : (countRow (12 * k + 14) : ℚ) = 19 + 14 * ((k : ℕ) : ℚ) := by
  rw [countRow, (row_phases k).2.2.2.2.2.1]
  simp [phase5, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue6 (k : ℕ) : (countRow (12 * k + 15) : ℚ) = 16 + 14 * ((k : ℕ) : ℚ) := by
  rw [countRow, (row_phases k).2.2.2.2.2.2.1]
  simp [phase6, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue7 (k : ℕ) : (countRow (12 * k + 16) : ℚ) = 21 + 14 * ((k : ℕ) : ℚ) := by
  rw [countRow, (row_phases k).2.2.2.2.2.2.2.1]
  simp [phase7, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue8 (k : ℕ) : (countRow (12 * k + 17) : ℚ) = 21 + 14 * ((k : ℕ) : ℚ) := by
  rw [countRow, (row_phases k).2.2.2.2.2.2.2.2.1]
  simp [phase8, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue9 (k : ℕ) : (countRow (12 * k + 18) : ℚ) = 24 + 14 * ((k : ℕ) : ℚ) := by
  rw [countRow, (row_phases k).2.2.2.2.2.2.2.2.2.1]
  simp [phase9, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue10 (k : ℕ) : (countRow (12 * k + 19) : ℚ) = 19 + 14 * ((k : ℕ) : ℚ) := by
  rw [countRow, (row_phases k).2.2.2.2.2.2.2.2.2.2.1]
  simp [phase10, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue11 (k : ℕ) : (countRow (12 * k + 20) : ℚ) = 27 + 14 * ((k : ℕ) : ℚ) := by
  rw [countRow, (row_phases k).2.2.2.2.2.2.2.2.2.2.2]
  simp [phase11, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
lemma total_phases (k : ℕ) :
    (a (12 * k + 9) : ℚ) = 63 + 146 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 ∧
    (a (12 * k + 10) : ℚ) = 76 + 160 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 ∧
    (a (12 * k + 11) : ℚ) = 87 + 174 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 ∧
    (a (12 * k + 12) : ℚ) = 105 + 188 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 ∧
    (a (12 * k + 13) : ℚ) = 120 + 202 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 ∧
    (a (12 * k + 14) : ℚ) = 139 + 216 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 ∧
    (a (12 * k + 15) : ℚ) = 155 + 230 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 ∧
    (a (12 * k + 16) : ℚ) = 176 + 244 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 ∧
    (a (12 * k + 17) : ℚ) = 197 + 258 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 ∧
    (a (12 * k + 18) : ℚ) = 221 + 272 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 ∧
    (a (12 * k + 19) : ℚ) = 240 + 286 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 ∧
    (a (12 * k + 20) : ℚ) = 267 + 300 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
  induction k with
  | zero =>
    norm_num [initial9, initial10, initial11, initial12, initial13, initial14, initial15, initial16, initial17, initial18, initial19, initial20]
  | succ k ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, old⟩ := ih
    have step0 : (a (12 * (k + 1) + 9) : ℚ) = 63 + 146 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      have addRow : a (12 * (k + 1) + 9) = a (12 * k + 20) + countRow (12 * (k + 1) + 9) := by
        rw [show (12 * (k + 1) + 9) = (12 * k + 20) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, old, rowValue0]
      push_cast
      try simp only [pow_succ]
      ring
    have step1 : (a (12 * (k + 1) + 10) : ℚ) = 76 + 160 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      have addRow : a (12 * (k + 1) + 10) = a (12 * (k + 1) + 9) + countRow (12 * (k + 1) + 10) := by
        rw [show (12 * (k + 1) + 10) = (12 * (k + 1) + 9) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, step0, rowValue1]
      push_cast
      try simp only [pow_succ]
      ring
    have step2 : (a (12 * (k + 1) + 11) : ℚ) = 87 + 174 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      have addRow : a (12 * (k + 1) + 11) = a (12 * (k + 1) + 10) + countRow (12 * (k + 1) + 11) := by
        rw [show (12 * (k + 1) + 11) = (12 * (k + 1) + 10) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, step1, rowValue2]
      push_cast
      try simp only [pow_succ]
      ring
    have step3 : (a (12 * (k + 1) + 12) : ℚ) = 105 + 188 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      have addRow : a (12 * (k + 1) + 12) = a (12 * (k + 1) + 11) + countRow (12 * (k + 1) + 12) := by
        rw [show (12 * (k + 1) + 12) = (12 * (k + 1) + 11) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, step2, rowValue3]
      push_cast
      try simp only [pow_succ]
      ring
    have step4 : (a (12 * (k + 1) + 13) : ℚ) = 120 + 202 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      have addRow : a (12 * (k + 1) + 13) = a (12 * (k + 1) + 12) + countRow (12 * (k + 1) + 13) := by
        rw [show (12 * (k + 1) + 13) = (12 * (k + 1) + 12) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, step3, rowValue4]
      push_cast
      try simp only [pow_succ]
      ring
    have step5 : (a (12 * (k + 1) + 14) : ℚ) = 139 + 216 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      have addRow : a (12 * (k + 1) + 14) = a (12 * (k + 1) + 13) + countRow (12 * (k + 1) + 14) := by
        rw [show (12 * (k + 1) + 14) = (12 * (k + 1) + 13) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, step4, rowValue5]
      push_cast
      try simp only [pow_succ]
      ring
    have step6 : (a (12 * (k + 1) + 15) : ℚ) = 155 + 230 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      have addRow : a (12 * (k + 1) + 15) = a (12 * (k + 1) + 14) + countRow (12 * (k + 1) + 15) := by
        rw [show (12 * (k + 1) + 15) = (12 * (k + 1) + 14) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, step5, rowValue6]
      push_cast
      try simp only [pow_succ]
      ring
    have step7 : (a (12 * (k + 1) + 16) : ℚ) = 176 + 244 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      have addRow : a (12 * (k + 1) + 16) = a (12 * (k + 1) + 15) + countRow (12 * (k + 1) + 16) := by
        rw [show (12 * (k + 1) + 16) = (12 * (k + 1) + 15) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, step6, rowValue7]
      push_cast
      try simp only [pow_succ]
      ring
    have step8 : (a (12 * (k + 1) + 17) : ℚ) = 197 + 258 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      have addRow : a (12 * (k + 1) + 17) = a (12 * (k + 1) + 16) + countRow (12 * (k + 1) + 17) := by
        rw [show (12 * (k + 1) + 17) = (12 * (k + 1) + 16) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, step7, rowValue8]
      push_cast
      try simp only [pow_succ]
      ring
    have step9 : (a (12 * (k + 1) + 18) : ℚ) = 221 + 272 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      have addRow : a (12 * (k + 1) + 18) = a (12 * (k + 1) + 17) + countRow (12 * (k + 1) + 18) := by
        rw [show (12 * (k + 1) + 18) = (12 * (k + 1) + 17) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, step8, rowValue9]
      push_cast
      try simp only [pow_succ]
      ring
    have step10 : (a (12 * (k + 1) + 19) : ℚ) = 240 + 286 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      have addRow : a (12 * (k + 1) + 19) = a (12 * (k + 1) + 18) + countRow (12 * (k + 1) + 19) := by
        rw [show (12 * (k + 1) + 19) = (12 * (k + 1) + 18) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, step9, rowValue10]
      push_cast
      try simp only [pow_succ]
      ring
    have step11 : (a (12 * (k + 1) + 20) : ℚ) = 267 + 300 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      have addRow : a (12 * (k + 1) + 20) = a (12 * (k + 1) + 19) + countRow (12 * (k + 1) + 20) := by
        rw [show (12 * (k + 1) + 20) = (12 * (k + 1) + 19) + 1 by omega]
        rfl
      rw [addRow, Nat.cast_add, step10, rowValue11]
      push_cast
      try simp only [pow_succ]
      ring
    exact ⟨step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
lemma claim0 : ∀ n : ℕ, 7 < n → (a n : ℚ) = (a (n - 1) : ℚ) + (a (n - 3) : ℚ) - (a (n - 5) : ℚ) - (a (n - 7) : ℚ) + (a (n - 8) : ℚ) := by
  intro n hn
  by_cases small : n < 17
  · interval_cases n <;> norm_num [initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7, initial8, initial9, initial10, initial11, initial12, initial13, initial14, initial15, initial16] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 12 + 17 ∨ n = k * 12 + 18 ∨ n = k * 12 + 19 ∨ n = k * 12 + 20 ∨ n = k * 12 + 21 ∨ n = k * 12 + 22 ∨ n = k * 12 + 23 ∨ n = k * 12 + 24 ∨ n = k * 12 + 25 ∨ n = k * 12 + 26 ∨ n = k * 12 + 27 ∨ n = k * 12 + 28 := ⟨(n - 17) / 12, by omega⟩
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have val0 : (a (k * 12 + 17) : ℚ) = 197 + 258 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 17 = (12 * k + 17) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.1
    have val1 : (a (k * 12 + 17 - 1) : ℚ) = 176 + 244 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 17 - 1 = (12 * k + 16) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.1
    have val3 : (a (k * 12 + 17 - 3) : ℚ) = 139 + 216 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 17 - 3 = (12 * k + 14) by omega]
      exact (total_phases k).2.2.2.2.2.1
    have val5 : (a (k * 12 + 17 - 5) : ℚ) = 105 + 188 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 17 - 5 = (12 * k + 12) by omega]
      exact (total_phases k).2.2.2.1
    have val7 : (a (k * 12 + 17 - 7) : ℚ) = 76 + 160 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 17 - 7 = (12 * k + 10) by omega]
      exact (total_phases k).2.1
    have val8 : (a (k * 12 + 17 - 8) : ℚ) = 63 + 146 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 17 - 8 = (12 * k + 9) by omega]
      exact (total_phases k).1
    simp only [val0, val1, val3, val5, val7, val8]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 18) : ℚ) = 221 + 272 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 18 = (12 * k + 18) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.1
    have val1 : (a (k * 12 + 18 - 1) : ℚ) = 197 + 258 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 18 - 1 = (12 * k + 17) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.1
    have val3 : (a (k * 12 + 18 - 3) : ℚ) = 155 + 230 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 18 - 3 = (12 * k + 15) by omega]
      exact (total_phases k).2.2.2.2.2.2.1
    have val5 : (a (k * 12 + 18 - 5) : ℚ) = 120 + 202 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 18 - 5 = (12 * k + 13) by omega]
      exact (total_phases k).2.2.2.2.1
    have val7 : (a (k * 12 + 18 - 7) : ℚ) = 87 + 174 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 18 - 7 = (12 * k + 11) by omega]
      exact (total_phases k).2.2.1
    have val8 : (a (k * 12 + 18 - 8) : ℚ) = 76 + 160 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 18 - 8 = (12 * k + 10) by omega]
      exact (total_phases k).2.1
    simp only [val0, val1, val3, val5, val7, val8]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 19) : ℚ) = 240 + 286 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 19 = (12 * k + 19) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.1
    have val1 : (a (k * 12 + 19 - 1) : ℚ) = 221 + 272 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 19 - 1 = (12 * k + 18) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.1
    have val3 : (a (k * 12 + 19 - 3) : ℚ) = 176 + 244 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 19 - 3 = (12 * k + 16) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.1
    have val5 : (a (k * 12 + 19 - 5) : ℚ) = 139 + 216 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 19 - 5 = (12 * k + 14) by omega]
      exact (total_phases k).2.2.2.2.2.1
    have val7 : (a (k * 12 + 19 - 7) : ℚ) = 105 + 188 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 19 - 7 = (12 * k + 12) by omega]
      exact (total_phases k).2.2.2.1
    have val8 : (a (k * 12 + 19 - 8) : ℚ) = 87 + 174 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 19 - 8 = (12 * k + 11) by omega]
      exact (total_phases k).2.2.1
    simp only [val0, val1, val3, val5, val7, val8]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 20) : ℚ) = 267 + 300 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 20 = (12 * k + 20) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.2
    have val1 : (a (k * 12 + 20 - 1) : ℚ) = 240 + 286 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 20 - 1 = (12 * k + 19) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.1
    have val3 : (a (k * 12 + 20 - 3) : ℚ) = 197 + 258 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 20 - 3 = (12 * k + 17) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.1
    have val5 : (a (k * 12 + 20 - 5) : ℚ) = 155 + 230 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 20 - 5 = (12 * k + 15) by omega]
      exact (total_phases k).2.2.2.2.2.2.1
    have val7 : (a (k * 12 + 20 - 7) : ℚ) = 120 + 202 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 20 - 7 = (12 * k + 13) by omega]
      exact (total_phases k).2.2.2.2.1
    have val8 : (a (k * 12 + 20 - 8) : ℚ) = 105 + 188 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 20 - 8 = (12 * k + 12) by omega]
      exact (total_phases k).2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 21) : ℚ) = 63 + 146 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 21 = (12 * (k + 1) + 9) by omega]
      exact (total_phases (k + 1)).1
    have val1 : (a (k * 12 + 21 - 1) : ℚ) = 267 + 300 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 21 - 1 = (12 * k + 20) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.2
    have val3 : (a (k * 12 + 21 - 3) : ℚ) = 221 + 272 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 21 - 3 = (12 * k + 18) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.1
    have val5 : (a (k * 12 + 21 - 5) : ℚ) = 176 + 244 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 21 - 5 = (12 * k + 16) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.1
    have val7 : (a (k * 12 + 21 - 7) : ℚ) = 139 + 216 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 21 - 7 = (12 * k + 14) by omega]
      exact (total_phases k).2.2.2.2.2.1
    have val8 : (a (k * 12 + 21 - 8) : ℚ) = 120 + 202 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 21 - 8 = (12 * k + 13) by omega]
      exact (total_phases k).2.2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 22) : ℚ) = 76 + 160 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 22 = (12 * (k + 1) + 10) by omega]
      exact (total_phases (k + 1)).2.1
    have val1 : (a (k * 12 + 22 - 1) : ℚ) = 63 + 146 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 22 - 1 = (12 * (k + 1) + 9) by omega]
      exact (total_phases (k + 1)).1
    have val3 : (a (k * 12 + 22 - 3) : ℚ) = 240 + 286 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 22 - 3 = (12 * k + 19) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.1
    have val5 : (a (k * 12 + 22 - 5) : ℚ) = 197 + 258 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 22 - 5 = (12 * k + 17) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.1
    have val7 : (a (k * 12 + 22 - 7) : ℚ) = 155 + 230 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 22 - 7 = (12 * k + 15) by omega]
      exact (total_phases k).2.2.2.2.2.2.1
    have val8 : (a (k * 12 + 22 - 8) : ℚ) = 139 + 216 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 22 - 8 = (12 * k + 14) by omega]
      exact (total_phases k).2.2.2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 23) : ℚ) = 87 + 174 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 23 = (12 * (k + 1) + 11) by omega]
      exact (total_phases (k + 1)).2.2.1
    have val1 : (a (k * 12 + 23 - 1) : ℚ) = 76 + 160 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 23 - 1 = (12 * (k + 1) + 10) by omega]
      exact (total_phases (k + 1)).2.1
    have val3 : (a (k * 12 + 23 - 3) : ℚ) = 267 + 300 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 23 - 3 = (12 * k + 20) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.2
    have val5 : (a (k * 12 + 23 - 5) : ℚ) = 221 + 272 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 23 - 5 = (12 * k + 18) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.1
    have val7 : (a (k * 12 + 23 - 7) : ℚ) = 176 + 244 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 23 - 7 = (12 * k + 16) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.1
    have val8 : (a (k * 12 + 23 - 8) : ℚ) = 155 + 230 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 23 - 8 = (12 * k + 15) by omega]
      exact (total_phases k).2.2.2.2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 24) : ℚ) = 105 + 188 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 24 = (12 * (k + 1) + 12) by omega]
      exact (total_phases (k + 1)).2.2.2.1
    have val1 : (a (k * 12 + 24 - 1) : ℚ) = 87 + 174 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 24 - 1 = (12 * (k + 1) + 11) by omega]
      exact (total_phases (k + 1)).2.2.1
    have val3 : (a (k * 12 + 24 - 3) : ℚ) = 63 + 146 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 24 - 3 = (12 * (k + 1) + 9) by omega]
      exact (total_phases (k + 1)).1
    have val5 : (a (k * 12 + 24 - 5) : ℚ) = 240 + 286 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 24 - 5 = (12 * k + 19) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.1
    have val7 : (a (k * 12 + 24 - 7) : ℚ) = 197 + 258 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 24 - 7 = (12 * k + 17) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.1
    have val8 : (a (k * 12 + 24 - 8) : ℚ) = 176 + 244 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 24 - 8 = (12 * k + 16) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 25) : ℚ) = 120 + 202 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 25 = (12 * (k + 1) + 13) by omega]
      exact (total_phases (k + 1)).2.2.2.2.1
    have val1 : (a (k * 12 + 25 - 1) : ℚ) = 105 + 188 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 25 - 1 = (12 * (k + 1) + 12) by omega]
      exact (total_phases (k + 1)).2.2.2.1
    have val3 : (a (k * 12 + 25 - 3) : ℚ) = 76 + 160 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 25 - 3 = (12 * (k + 1) + 10) by omega]
      exact (total_phases (k + 1)).2.1
    have val5 : (a (k * 12 + 25 - 5) : ℚ) = 267 + 300 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 25 - 5 = (12 * k + 20) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.2
    have val7 : (a (k * 12 + 25 - 7) : ℚ) = 221 + 272 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 25 - 7 = (12 * k + 18) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.1
    have val8 : (a (k * 12 + 25 - 8) : ℚ) = 197 + 258 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 25 - 8 = (12 * k + 17) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 26) : ℚ) = 139 + 216 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 26 = (12 * (k + 1) + 14) by omega]
      exact (total_phases (k + 1)).2.2.2.2.2.1
    have val1 : (a (k * 12 + 26 - 1) : ℚ) = 120 + 202 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 26 - 1 = (12 * (k + 1) + 13) by omega]
      exact (total_phases (k + 1)).2.2.2.2.1
    have val3 : (a (k * 12 + 26 - 3) : ℚ) = 87 + 174 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 26 - 3 = (12 * (k + 1) + 11) by omega]
      exact (total_phases (k + 1)).2.2.1
    have val5 : (a (k * 12 + 26 - 5) : ℚ) = 63 + 146 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 26 - 5 = (12 * (k + 1) + 9) by omega]
      exact (total_phases (k + 1)).1
    have val7 : (a (k * 12 + 26 - 7) : ℚ) = 240 + 286 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 26 - 7 = (12 * k + 19) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.1
    have val8 : (a (k * 12 + 26 - 8) : ℚ) = 221 + 272 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 26 - 8 = (12 * k + 18) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 27) : ℚ) = 155 + 230 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 27 = (12 * (k + 1) + 15) by omega]
      exact (total_phases (k + 1)).2.2.2.2.2.2.1
    have val1 : (a (k * 12 + 27 - 1) : ℚ) = 139 + 216 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 27 - 1 = (12 * (k + 1) + 14) by omega]
      exact (total_phases (k + 1)).2.2.2.2.2.1
    have val3 : (a (k * 12 + 27 - 3) : ℚ) = 105 + 188 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 27 - 3 = (12 * (k + 1) + 12) by omega]
      exact (total_phases (k + 1)).2.2.2.1
    have val5 : (a (k * 12 + 27 - 5) : ℚ) = 76 + 160 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 27 - 5 = (12 * (k + 1) + 10) by omega]
      exact (total_phases (k + 1)).2.1
    have val7 : (a (k * 12 + 27 - 7) : ℚ) = 267 + 300 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 27 - 7 = (12 * k + 20) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.2
    have val8 : (a (k * 12 + 27 - 8) : ℚ) = 240 + 286 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 27 - 8 = (12 * k + 19) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 28) : ℚ) = 176 + 244 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 28 = (12 * (k + 1) + 16) by omega]
      exact (total_phases (k + 1)).2.2.2.2.2.2.2.1
    have val1 : (a (k * 12 + 28 - 1) : ℚ) = 155 + 230 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 28 - 1 = (12 * (k + 1) + 15) by omega]
      exact (total_phases (k + 1)).2.2.2.2.2.2.1
    have val3 : (a (k * 12 + 28 - 3) : ℚ) = 120 + 202 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 28 - 3 = (12 * (k + 1) + 13) by omega]
      exact (total_phases (k + 1)).2.2.2.2.1
    have val5 : (a (k * 12 + 28 - 5) : ℚ) = 87 + 174 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 28 - 5 = (12 * (k + 1) + 11) by omega]
      exact (total_phases (k + 1)).2.2.1
    have val7 : (a (k * 12 + 28 - 7) : ℚ) = 63 + 146 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 28 - 7 = (12 * (k + 1) + 9) by omega]
      exact (total_phases (k + 1)).1
    have val8 : (a (k * 12 + 28 - 8) : ℚ) = 267 + 300 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 28 - 8 = (12 * k + 20) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.2
    simp only [val0, val1, val3, val5, val7, val8]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
lemma convolution : ∀ n : ℕ, (1) * (if 0 ≤ n then (a (n - 0) : ℚ) else 0) + (-1) * (if 1 ≤ n then (a (n - 1) : ℚ) else 0) + (-1) * (if 3 ≤ n then (a (n - 3) : ℚ) else 0) + (1) * (if 5 ≤ n then (a (n - 5) : ℚ) else 0) + (1) * (if 7 ≤ n then (a (n - 7) : ℚ) else 0) + (-1) * (if 8 ≤ n then (a (n - 8) : ℚ) else 0) =
      (1) * (if n = 0 then (1 : ℚ) else 0) + (1) * (if n = 1 then (1 : ℚ) else 0) + (5) * (if n = 2 then (1 : ℚ) else 0) + (1) * (if n = 3 then (1 : ℚ) else 0) + (5) * (if n = 4 then (1 : ℚ) else 0) + (1) * (if n = 5 then (1 : ℚ) else 0) + (3) * (if n = 6 then (1 : ℚ) else 0) + (-3) * (if n = 7 then (1 : ℚ) else 0) := by
  intro n
  by_cases small : n < 17
  · interval_cases n <;> norm_num [initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7, initial8, initial9, initial10, initial11, initial12, initial13, initial14, initial15, initial16] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 12 + 17 ∨ n = k * 12 + 18 ∨ n = k * 12 + 19 ∨ n = k * 12 + 20 ∨ n = k * 12 + 21 ∨ n = k * 12 + 22 ∨ n = k * 12 + 23 ∨ n = k * 12 + 24 ∨ n = k * 12 + 25 ∨ n = k * 12 + 26 ∨ n = k * 12 + 27 ∨ n = k * 12 + 28 := ⟨(n - 17) / 12, by omega⟩
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have val0 : (a (k * 12 + 17) : ℚ) = 197 + 258 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 17 = (12 * k + 17) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.1
    have val1 : (a (k * 12 + 17 - 1) : ℚ) = 176 + 244 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 17 - 1 = (12 * k + 16) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.1
    have val3 : (a (k * 12 + 17 - 3) : ℚ) = 139 + 216 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 17 - 3 = (12 * k + 14) by omega]
      exact (total_phases k).2.2.2.2.2.1
    have val5 : (a (k * 12 + 17 - 5) : ℚ) = 105 + 188 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 17 - 5 = (12 * k + 12) by omega]
      exact (total_phases k).2.2.2.1
    have val7 : (a (k * 12 + 17 - 7) : ℚ) = 76 + 160 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 17 - 7 = (12 * k + 10) by omega]
      exact (total_phases k).2.1
    have val8 : (a (k * 12 + 17 - 8) : ℚ) = 63 + 146 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 17 - 8 = (12 * k + 9) by omega]
      exact (total_phases k).1
    simp only [val0, val1, val3, val5, val7, val8, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 18) : ℚ) = 221 + 272 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 18 = (12 * k + 18) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.1
    have val1 : (a (k * 12 + 18 - 1) : ℚ) = 197 + 258 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 18 - 1 = (12 * k + 17) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.1
    have val3 : (a (k * 12 + 18 - 3) : ℚ) = 155 + 230 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 18 - 3 = (12 * k + 15) by omega]
      exact (total_phases k).2.2.2.2.2.2.1
    have val5 : (a (k * 12 + 18 - 5) : ℚ) = 120 + 202 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 18 - 5 = (12 * k + 13) by omega]
      exact (total_phases k).2.2.2.2.1
    have val7 : (a (k * 12 + 18 - 7) : ℚ) = 87 + 174 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 18 - 7 = (12 * k + 11) by omega]
      exact (total_phases k).2.2.1
    have val8 : (a (k * 12 + 18 - 8) : ℚ) = 76 + 160 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 18 - 8 = (12 * k + 10) by omega]
      exact (total_phases k).2.1
    simp only [val0, val1, val3, val5, val7, val8, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 19) : ℚ) = 240 + 286 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 19 = (12 * k + 19) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.1
    have val1 : (a (k * 12 + 19 - 1) : ℚ) = 221 + 272 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 19 - 1 = (12 * k + 18) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.1
    have val3 : (a (k * 12 + 19 - 3) : ℚ) = 176 + 244 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 19 - 3 = (12 * k + 16) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.1
    have val5 : (a (k * 12 + 19 - 5) : ℚ) = 139 + 216 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 19 - 5 = (12 * k + 14) by omega]
      exact (total_phases k).2.2.2.2.2.1
    have val7 : (a (k * 12 + 19 - 7) : ℚ) = 105 + 188 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 19 - 7 = (12 * k + 12) by omega]
      exact (total_phases k).2.2.2.1
    have val8 : (a (k * 12 + 19 - 8) : ℚ) = 87 + 174 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 19 - 8 = (12 * k + 11) by omega]
      exact (total_phases k).2.2.1
    simp only [val0, val1, val3, val5, val7, val8, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 20) : ℚ) = 267 + 300 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 20 = (12 * k + 20) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.2
    have val1 : (a (k * 12 + 20 - 1) : ℚ) = 240 + 286 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 20 - 1 = (12 * k + 19) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.1
    have val3 : (a (k * 12 + 20 - 3) : ℚ) = 197 + 258 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 20 - 3 = (12 * k + 17) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.1
    have val5 : (a (k * 12 + 20 - 5) : ℚ) = 155 + 230 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 20 - 5 = (12 * k + 15) by omega]
      exact (total_phases k).2.2.2.2.2.2.1
    have val7 : (a (k * 12 + 20 - 7) : ℚ) = 120 + 202 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 20 - 7 = (12 * k + 13) by omega]
      exact (total_phases k).2.2.2.2.1
    have val8 : (a (k * 12 + 20 - 8) : ℚ) = 105 + 188 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 20 - 8 = (12 * k + 12) by omega]
      exact (total_phases k).2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 21) : ℚ) = 63 + 146 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 21 = (12 * (k + 1) + 9) by omega]
      exact (total_phases (k + 1)).1
    have val1 : (a (k * 12 + 21 - 1) : ℚ) = 267 + 300 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 21 - 1 = (12 * k + 20) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.2
    have val3 : (a (k * 12 + 21 - 3) : ℚ) = 221 + 272 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 21 - 3 = (12 * k + 18) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.1
    have val5 : (a (k * 12 + 21 - 5) : ℚ) = 176 + 244 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 21 - 5 = (12 * k + 16) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.1
    have val7 : (a (k * 12 + 21 - 7) : ℚ) = 139 + 216 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 21 - 7 = (12 * k + 14) by omega]
      exact (total_phases k).2.2.2.2.2.1
    have val8 : (a (k * 12 + 21 - 8) : ℚ) = 120 + 202 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 21 - 8 = (12 * k + 13) by omega]
      exact (total_phases k).2.2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 22) : ℚ) = 76 + 160 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 22 = (12 * (k + 1) + 10) by omega]
      exact (total_phases (k + 1)).2.1
    have val1 : (a (k * 12 + 22 - 1) : ℚ) = 63 + 146 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 22 - 1 = (12 * (k + 1) + 9) by omega]
      exact (total_phases (k + 1)).1
    have val3 : (a (k * 12 + 22 - 3) : ℚ) = 240 + 286 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 22 - 3 = (12 * k + 19) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.1
    have val5 : (a (k * 12 + 22 - 5) : ℚ) = 197 + 258 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 22 - 5 = (12 * k + 17) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.1
    have val7 : (a (k * 12 + 22 - 7) : ℚ) = 155 + 230 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 22 - 7 = (12 * k + 15) by omega]
      exact (total_phases k).2.2.2.2.2.2.1
    have val8 : (a (k * 12 + 22 - 8) : ℚ) = 139 + 216 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 22 - 8 = (12 * k + 14) by omega]
      exact (total_phases k).2.2.2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 23) : ℚ) = 87 + 174 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 23 = (12 * (k + 1) + 11) by omega]
      exact (total_phases (k + 1)).2.2.1
    have val1 : (a (k * 12 + 23 - 1) : ℚ) = 76 + 160 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 23 - 1 = (12 * (k + 1) + 10) by omega]
      exact (total_phases (k + 1)).2.1
    have val3 : (a (k * 12 + 23 - 3) : ℚ) = 267 + 300 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 23 - 3 = (12 * k + 20) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.2
    have val5 : (a (k * 12 + 23 - 5) : ℚ) = 221 + 272 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 23 - 5 = (12 * k + 18) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.1
    have val7 : (a (k * 12 + 23 - 7) : ℚ) = 176 + 244 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 23 - 7 = (12 * k + 16) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.1
    have val8 : (a (k * 12 + 23 - 8) : ℚ) = 155 + 230 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 23 - 8 = (12 * k + 15) by omega]
      exact (total_phases k).2.2.2.2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 24) : ℚ) = 105 + 188 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 24 = (12 * (k + 1) + 12) by omega]
      exact (total_phases (k + 1)).2.2.2.1
    have val1 : (a (k * 12 + 24 - 1) : ℚ) = 87 + 174 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 24 - 1 = (12 * (k + 1) + 11) by omega]
      exact (total_phases (k + 1)).2.2.1
    have val3 : (a (k * 12 + 24 - 3) : ℚ) = 63 + 146 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 24 - 3 = (12 * (k + 1) + 9) by omega]
      exact (total_phases (k + 1)).1
    have val5 : (a (k * 12 + 24 - 5) : ℚ) = 240 + 286 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 24 - 5 = (12 * k + 19) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.1
    have val7 : (a (k * 12 + 24 - 7) : ℚ) = 197 + 258 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 24 - 7 = (12 * k + 17) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.1
    have val8 : (a (k * 12 + 24 - 8) : ℚ) = 176 + 244 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 24 - 8 = (12 * k + 16) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 25) : ℚ) = 120 + 202 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 25 = (12 * (k + 1) + 13) by omega]
      exact (total_phases (k + 1)).2.2.2.2.1
    have val1 : (a (k * 12 + 25 - 1) : ℚ) = 105 + 188 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 25 - 1 = (12 * (k + 1) + 12) by omega]
      exact (total_phases (k + 1)).2.2.2.1
    have val3 : (a (k * 12 + 25 - 3) : ℚ) = 76 + 160 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 25 - 3 = (12 * (k + 1) + 10) by omega]
      exact (total_phases (k + 1)).2.1
    have val5 : (a (k * 12 + 25 - 5) : ℚ) = 267 + 300 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 25 - 5 = (12 * k + 20) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.2
    have val7 : (a (k * 12 + 25 - 7) : ℚ) = 221 + 272 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 25 - 7 = (12 * k + 18) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.1
    have val8 : (a (k * 12 + 25 - 8) : ℚ) = 197 + 258 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 25 - 8 = (12 * k + 17) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 26) : ℚ) = 139 + 216 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 26 = (12 * (k + 1) + 14) by omega]
      exact (total_phases (k + 1)).2.2.2.2.2.1
    have val1 : (a (k * 12 + 26 - 1) : ℚ) = 120 + 202 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 26 - 1 = (12 * (k + 1) + 13) by omega]
      exact (total_phases (k + 1)).2.2.2.2.1
    have val3 : (a (k * 12 + 26 - 3) : ℚ) = 87 + 174 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 26 - 3 = (12 * (k + 1) + 11) by omega]
      exact (total_phases (k + 1)).2.2.1
    have val5 : (a (k * 12 + 26 - 5) : ℚ) = 63 + 146 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 26 - 5 = (12 * (k + 1) + 9) by omega]
      exact (total_phases (k + 1)).1
    have val7 : (a (k * 12 + 26 - 7) : ℚ) = 240 + 286 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 26 - 7 = (12 * k + 19) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.1
    have val8 : (a (k * 12 + 26 - 8) : ℚ) = 221 + 272 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 26 - 8 = (12 * k + 18) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 27) : ℚ) = 155 + 230 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 27 = (12 * (k + 1) + 15) by omega]
      exact (total_phases (k + 1)).2.2.2.2.2.2.1
    have val1 : (a (k * 12 + 27 - 1) : ℚ) = 139 + 216 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 27 - 1 = (12 * (k + 1) + 14) by omega]
      exact (total_phases (k + 1)).2.2.2.2.2.1
    have val3 : (a (k * 12 + 27 - 3) : ℚ) = 105 + 188 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 27 - 3 = (12 * (k + 1) + 12) by omega]
      exact (total_phases (k + 1)).2.2.2.1
    have val5 : (a (k * 12 + 27 - 5) : ℚ) = 76 + 160 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 27 - 5 = (12 * (k + 1) + 10) by omega]
      exact (total_phases (k + 1)).2.1
    have val7 : (a (k * 12 + 27 - 7) : ℚ) = 267 + 300 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 27 - 7 = (12 * k + 20) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.2
    have val8 : (a (k * 12 + 27 - 8) : ℚ) = 240 + 286 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 27 - 8 = (12 * k + 19) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.1
    simp only [val0, val1, val3, val5, val7, val8, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 28) : ℚ) = 176 + 244 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 28 = (12 * (k + 1) + 16) by omega]
      exact (total_phases (k + 1)).2.2.2.2.2.2.2.1
    have val1 : (a (k * 12 + 28 - 1) : ℚ) = 155 + 230 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 28 - 1 = (12 * (k + 1) + 15) by omega]
      exact (total_phases (k + 1)).2.2.2.2.2.2.1
    have val3 : (a (k * 12 + 28 - 3) : ℚ) = 120 + 202 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 28 - 3 = (12 * (k + 1) + 13) by omega]
      exact (total_phases (k + 1)).2.2.2.2.1
    have val5 : (a (k * 12 + 28 - 5) : ℚ) = 87 + 174 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 28 - 5 = (12 * (k + 1) + 11) by omega]
      exact (total_phases (k + 1)).2.2.1
    have val7 : (a (k * 12 + 28 - 7) : ℚ) = 63 + 146 * (((k + 1) : ℕ) : ℚ) + 84 * (((k + 1) : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 28 - 7 = (12 * (k + 1) + 9) by omega]
      exact (total_phases (k + 1)).1
    have val8 : (a (k * 12 + 28 - 8) : ℚ) = 267 + 300 * ((k : ℕ) : ℚ) + 84 * ((k : ℕ) : ℚ) ^ 2 := by
      rw [show k * 12 + 28 - 8 = (12 * k + 20) by omega]
      exact (total_phases k).2.2.2.2.2.2.2.2.2.2.2
    simp only [val0, val1, val3, val5, val7, val8, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring

open PowerSeries

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
lemma generating_function : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2)) =
      1 + X + 5 * X ^ 2 + X ^ 3 + 5 * X ^ 4 + X ^ 5 + 3 * X ^ 6 - 3 * X ^ 7 := by
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  calc
    _ = C (1 : ℚ) * (s * X ^ 0) + C (-1 : ℚ) * (s * X ^ 1) + C (-1 : ℚ) * (s * X ^ 3) + C (1 : ℚ) * (s * X ^ 5) + C (1 : ℚ) * (s * X ^ 7) + C (-1 : ℚ) * (s * X ^ 8) := by simp only [map_neg, map_one, map_ofNat] <;> ring
    _ = C (1 : ℚ) * (X ^ 0) + C (1 : ℚ) * (X ^ 1) + C (5 : ℚ) * (X ^ 2) + C (1 : ℚ) * (X ^ 3) + C (5 : ℚ) * (X ^ 4) + C (1 : ℚ) * (X ^ 5) + C (3 : ℚ) * (X ^ 6) + C (-3 : ℚ) * (X ^ 7) := by
      apply PowerSeries.ext
      intro n
      simp only [map_add, coeff_C_mul]
      simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
      exact convolution n
    _ = _ := by simp only [map_neg, map_one, map_ofNat] <;> ring

end RowProof

open RowProof

open Ours_oeis_a267212
open PowerSeries in
lemma old_result :
    (∀ n : ℕ, 7 < n → (a n : ℚ) = (a (n - 1) : ℚ) + (a (n - 3) : ℚ) - (a (n - 5) : ℚ) - (a (n - 7) : ℚ) + (a (n - 8) : ℚ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2)) =
      1 + X + 5 * X ^ 2 + X ^ 3 + 5 * X ^ 4 + X ^ 5 + 3 * X ^ 6 - 3 * X ^ 7) :=
  ⟨claim0, generating_function⟩

namespace Ours_oeis_a267212

def window (t : ℕ) (i : ℤ) : ℕ → List Bool
  | 0 => []
  | m + 1 => OMA.S_oeis_a267212.cell 109 t i :: window t (i + 1) m

lemma window_append (t : ℕ) (i : ℤ) (m k : ℕ) :
    window t i (m + k) = window t i m ++ window t (i + m) k := by
  induction m generalizing i with
  | zero => simp [window]
  | succ m ih =>
    rw [Nat.succ_add, window, window, List.cons_append, ih]
    congr 3 <;> push_cast <;> ring

lemma outside_window (t : ℕ) (i : ℤ) (hi : i < -(t : ℤ) ∨ (t : ℤ) < i) :
    OMA.S_oeis_a267212.cell 109 t i = (row t).1 := by
  induction t generalizing i with
  | zero => simp [OMA.S_oeis_a267212.cell, row, show i ≠ 0 by omega]
  | succ t ih =>
    simp only [OMA.S_oeis_a267212.cell]
    rw [ih (i - 1) (by omega), ih i (by omega), ih (i + 1) (by omega)]
    rfl

lemma scan_window (t : ℕ) (i : ℤ) (m : ℕ) :
    sweep (OMA.S_oeis_a267212.cell 109 t (i - 2)) (OMA.S_oeis_a267212.cell 109 t (i - 1)) (window t i m) =
      window (t + 1) (i - 1) m := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
    simp only [window, sweep, List.cons.injEq]
    constructor
    · simp only [OMA.S_oeis_a267212.cell, show i - 1 - 1 = i - 2 by ring, show i - 1 + 1 = i by ring]
      rfl
    · simpa only [show i + 1 - 2 = i - 1 by ring, show i + 1 - 1 = i by ring,
        show i - 1 + 1 = i by ring] using ih (i + 1)

lemma row_window (t : ℕ) : (row t).2 = window t (-(t : ℤ)) (2 * t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change sweep ((row t).1) ((row t).1) ((row t).2 ++ [(row t).1, (row t).1]) = _
    let i := -(t : ℤ)
    have hr : window t (i + (2 * t + 1 : ℕ)) 2 = [(row t).1, (row t).1] := by
      simp only [window]
      rw [outside_window t (i + (2 * t + 1 : ℕ)) (by right; dsimp [i]; push_cast; omega),
          outside_window t (i + (2 * t + 1 : ℕ) + 1) (by right; dsimp [i]; push_cast; omega)]
    have hs := scan_window t i ((2 * t + 1) + 2)
    rw [outside_window t (i - 2) (by left; dsimp [i]; omega),
        outside_window t (i - 1) (by left; dsimp [i]; omega),
        window_append t i (2 * t + 1) 2, hr] at hs
    rw [ih]
    simpa only [i, Nat.cast_succ, show -(t : ℤ) - 1 = -((t : ℤ) + 1) by ring,
      show (2 * t + 1) + 2 = 2 * (t + 1) + 1 by omega] using hs

lemma window_count (t m : ℕ) (i : ℤ) :
    (window t i m).count true =
      ∑ j ∈ Finset.range m, if OMA.S_oeis_a267212.cell 109 t ((j : ℤ) + i) then 1 else 0 := by
  induction m generalizing i with
  | zero => simp [window]
  | succ m ih =>
    rw [window, List.count_cons, ih, Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Int.zero_add, Nat.cast_zero,
      Int.add_right_comm _ 1 i, Int.add_assoc]
    cases OMA.S_oeis_a267212.cell 109 t i <;> simp

lemma row_on (t : ℕ) : ((row t).2).count true = OMA.S_oeis_a267212.onCount 109 t := by
  rw [row_window, window_count]
  simp only [OMA.S_oeis_a267212.onCount, sub_eq_add_neg]


lemma sequence_eq (n : ℕ) : OMA.S_oeis_a267212.a n = (a n : ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [OMA.S_oeis_a267212.a, Finset.sum_range_succ _ (n + 1), a, Nat.cast_add, countRow] at *
    rw [ih, row_on] <;> push_cast <;> rfl

end Ours_oeis_a267212

theorem OMA.solution : type_of% @OMA.S_oeis_a267212.main := by
  simp only [sequence_eq, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat] 
  exact ⟨by
    intro n h
    first | exact old_result.1 n h | exact_mod_cast old_result.1 n h, old_result.2⟩
