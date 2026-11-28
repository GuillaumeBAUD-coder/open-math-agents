import OMAStatements.S_oeis_a267213

namespace Ours_oeis_a267213

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

def a (n : ℕ) : ℕ := (row n).2.count false

end Ours_oeis_a267213

open Ours_oeis_a267213

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

lemma initial0 : a 0 = 0 := by
  rw [a, seed0] <;> rfl

lemma initial1 : a 1 = 2 := by
  rw [a, seed1] <;> rfl

lemma initial2 : a 2 = 0 := by
  rw [a, seed2] <;> rfl

lemma initial3 : a 3 = 5 := by
  rw [a, seed3] <;> rfl

lemma initial4 : a 4 = 2 := by
  rw [a, seed4] <;> rfl

lemma initial5 : a 5 = 4 := by
  rw [a, seed5] <;> rfl

lemma initial6 : a 6 = 3 := by
  rw [a, seed6] <;> rfl

lemma initial7 : a 7 = 10 := by
  rw [a, seed7] <;> rfl

lemma initial8 : a 8 = 4 := by
  rw [a, seed8] <;> rfl

lemma initial9 : a 9 = 7 := by
  rw [a, seed9] <;> rfl

lemma initial10 : a 10 = 8 := by
  rw [a, seed10] <;> rfl

lemma initial11 : a 11 = 12 := by
  rw [a, seed11] <;> rfl

lemma initial12 : a 12 = 7 := by
  rw [a, seed12] <;> rfl

lemma initial13 : a 13 = 12 := by
  rw [a, seed13] <;> rfl

lemma initial14 : a 14 = 10 := by
  rw [a, seed14] <;> rfl

lemma initial15 : a 15 = 15 := by
  rw [a, seed15] <;> rfl

lemma initial16 : a 16 = 12 := by
  rw [a, seed16] <;> rfl

lemma initial17 : a 17 = 14 := by
  rw [a, seed17] <;> rfl

lemma initial18 : a 18 = 13 := by
  rw [a, seed18] <;> rfl

lemma initial19 : a 19 = 20 := by
  rw [a, seed19] <;> rfl

lemma initial20 : a 20 = 14 := by
  rw [a, seed20] <;> rfl

lemma count_blocks (w : List Bool) (k : ℕ) (s : List Bool) :
    (blocks w k s).count false = k * w.count false + s.count false := by
  induction k with
  | zero => simp [blocks]
  | succ k ih => simp [blocks, List.count_append, ih, Nat.succ_mul]; omega

lemma rowValue0 (k : ℕ) : (a (12 * k + 9) : ℚ) = 7 + 10 * ((k : ℕ) : ℚ) := by
  rw [a, (row_phases k).1]
  simp [phase0, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue1 (k : ℕ) : (a (12 * k + 10) : ℚ) = 8 + 10 * ((k : ℕ) : ℚ) := by
  rw [a, (row_phases k).2.1]
  simp [phase1, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue2 (k : ℕ) : (a (12 * k + 11) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
  rw [a, (row_phases k).2.2.1]
  simp [phase2, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue3 (k : ℕ) : (a (12 * k + 12) : ℚ) = 7 + 10 * ((k : ℕ) : ℚ) := by
  rw [a, (row_phases k).2.2.2.1]
  simp [phase3, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue4 (k : ℕ) : (a (12 * k + 13) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
  rw [a, (row_phases k).2.2.2.2.1]
  simp [phase4, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue5 (k : ℕ) : (a (12 * k + 14) : ℚ) = 10 + 10 * ((k : ℕ) : ℚ) := by
  rw [a, (row_phases k).2.2.2.2.2.1]
  simp [phase5, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue6 (k : ℕ) : (a (12 * k + 15) : ℚ) = 15 + 10 * ((k : ℕ) : ℚ) := by
  rw [a, (row_phases k).2.2.2.2.2.2.1]
  simp [phase6, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue7 (k : ℕ) : (a (12 * k + 16) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
  rw [a, (row_phases k).2.2.2.2.2.2.2.1]
  simp [phase7, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue8 (k : ℕ) : (a (12 * k + 17) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
  rw [a, (row_phases k).2.2.2.2.2.2.2.2.1]
  simp [phase8, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue9 (k : ℕ) : (a (12 * k + 18) : ℚ) = 13 + 10 * ((k : ℕ) : ℚ) := by
  rw [a, (row_phases k).2.2.2.2.2.2.2.2.2.1]
  simp [phase9, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue10 (k : ℕ) : (a (12 * k + 19) : ℚ) = 20 + 10 * ((k : ℕ) : ℚ) := by
  rw [a, (row_phases k).2.2.2.2.2.2.2.2.2.2.1]
  simp [phase10, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

lemma rowValue11 (k : ℕ) : (a (12 * k + 20) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
  rw [a, (row_phases k).2.2.2.2.2.2.2.2.2.2.2]
  simp [phase11, count_blocks, List.count_cons, Nat.cast_add, Nat.cast_mul]
  <;> ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
lemma claim0 : ∀ n : ℕ, 7 < n → (a n : ℚ) = (a (n - 3) : ℚ) + (a (n - 4) : ℚ) - (a (n - 7) : ℚ) := by
  intro n hn
  by_cases small : n < 16
  · interval_cases n <;> norm_num [initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7, initial8, initial9, initial10, initial11, initial12, initial13, initial14, initial15] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 12 + 16 ∨ n = k * 12 + 17 ∨ n = k * 12 + 18 ∨ n = k * 12 + 19 ∨ n = k * 12 + 20 ∨ n = k * 12 + 21 ∨ n = k * 12 + 22 ∨ n = k * 12 + 23 ∨ n = k * 12 + 24 ∨ n = k * 12 + 25 ∨ n = k * 12 + 26 ∨ n = k * 12 + 27 := ⟨(n - 16) / 12, by omega⟩
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have val0 : (a (k * 12 + 16) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 16 = (12 * k + 16) by omega]
      exact rowValue7 k
    have val3 : (a (k * 12 + 16 - 3) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 16 - 3 = (12 * k + 13) by omega]
      exact rowValue4 k
    have val4 : (a (k * 12 + 16 - 4) : ℚ) = 7 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 16 - 4 = (12 * k + 12) by omega]
      exact rowValue3 k
    have val7 : (a (k * 12 + 16 - 7) : ℚ) = 7 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 16 - 7 = (12 * k + 9) by omega]
      exact rowValue0 k
    simp only [val0, val3, val4, val7]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 17) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 17 = (12 * k + 17) by omega]
      exact rowValue8 k
    have val3 : (a (k * 12 + 17 - 3) : ℚ) = 10 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 17 - 3 = (12 * k + 14) by omega]
      exact rowValue5 k
    have val4 : (a (k * 12 + 17 - 4) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 17 - 4 = (12 * k + 13) by omega]
      exact rowValue4 k
    have val7 : (a (k * 12 + 17 - 7) : ℚ) = 8 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 17 - 7 = (12 * k + 10) by omega]
      exact rowValue1 k
    simp only [val0, val3, val4, val7]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 18) : ℚ) = 13 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 18 = (12 * k + 18) by omega]
      exact rowValue9 k
    have val3 : (a (k * 12 + 18 - 3) : ℚ) = 15 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 18 - 3 = (12 * k + 15) by omega]
      exact rowValue6 k
    have val4 : (a (k * 12 + 18 - 4) : ℚ) = 10 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 18 - 4 = (12 * k + 14) by omega]
      exact rowValue5 k
    have val7 : (a (k * 12 + 18 - 7) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 18 - 7 = (12 * k + 11) by omega]
      exact rowValue2 k
    simp only [val0, val3, val4, val7]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 19) : ℚ) = 20 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 19 = (12 * k + 19) by omega]
      exact rowValue10 k
    have val3 : (a (k * 12 + 19 - 3) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 19 - 3 = (12 * k + 16) by omega]
      exact rowValue7 k
    have val4 : (a (k * 12 + 19 - 4) : ℚ) = 15 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 19 - 4 = (12 * k + 15) by omega]
      exact rowValue6 k
    have val7 : (a (k * 12 + 19 - 7) : ℚ) = 7 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 19 - 7 = (12 * k + 12) by omega]
      exact rowValue3 k
    simp only [val0, val3, val4, val7]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 20) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 20 = (12 * k + 20) by omega]
      exact rowValue11 k
    have val3 : (a (k * 12 + 20 - 3) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 20 - 3 = (12 * k + 17) by omega]
      exact rowValue8 k
    have val4 : (a (k * 12 + 20 - 4) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 20 - 4 = (12 * k + 16) by omega]
      exact rowValue7 k
    have val7 : (a (k * 12 + 20 - 7) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 20 - 7 = (12 * k + 13) by omega]
      exact rowValue4 k
    simp only [val0, val3, val4, val7]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 21) : ℚ) = 7 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 21 = (12 * (k + 1) + 9) by omega]
      exact rowValue0 (k + 1)
    have val3 : (a (k * 12 + 21 - 3) : ℚ) = 13 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 21 - 3 = (12 * k + 18) by omega]
      exact rowValue9 k
    have val4 : (a (k * 12 + 21 - 4) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 21 - 4 = (12 * k + 17) by omega]
      exact rowValue8 k
    have val7 : (a (k * 12 + 21 - 7) : ℚ) = 10 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 21 - 7 = (12 * k + 14) by omega]
      exact rowValue5 k
    simp only [val0, val3, val4, val7]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 22) : ℚ) = 8 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 22 = (12 * (k + 1) + 10) by omega]
      exact rowValue1 (k + 1)
    have val3 : (a (k * 12 + 22 - 3) : ℚ) = 20 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 22 - 3 = (12 * k + 19) by omega]
      exact rowValue10 k
    have val4 : (a (k * 12 + 22 - 4) : ℚ) = 13 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 22 - 4 = (12 * k + 18) by omega]
      exact rowValue9 k
    have val7 : (a (k * 12 + 22 - 7) : ℚ) = 15 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 22 - 7 = (12 * k + 15) by omega]
      exact rowValue6 k
    simp only [val0, val3, val4, val7]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 23) : ℚ) = 12 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 23 = (12 * (k + 1) + 11) by omega]
      exact rowValue2 (k + 1)
    have val3 : (a (k * 12 + 23 - 3) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 23 - 3 = (12 * k + 20) by omega]
      exact rowValue11 k
    have val4 : (a (k * 12 + 23 - 4) : ℚ) = 20 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 23 - 4 = (12 * k + 19) by omega]
      exact rowValue10 k
    have val7 : (a (k * 12 + 23 - 7) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 23 - 7 = (12 * k + 16) by omega]
      exact rowValue7 k
    simp only [val0, val3, val4, val7]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 24) : ℚ) = 7 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 24 = (12 * (k + 1) + 12) by omega]
      exact rowValue3 (k + 1)
    have val3 : (a (k * 12 + 24 - 3) : ℚ) = 7 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 24 - 3 = (12 * (k + 1) + 9) by omega]
      exact rowValue0 (k + 1)
    have val4 : (a (k * 12 + 24 - 4) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 24 - 4 = (12 * k + 20) by omega]
      exact rowValue11 k
    have val7 : (a (k * 12 + 24 - 7) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 24 - 7 = (12 * k + 17) by omega]
      exact rowValue8 k
    simp only [val0, val3, val4, val7]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 25) : ℚ) = 12 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 25 = (12 * (k + 1) + 13) by omega]
      exact rowValue4 (k + 1)
    have val3 : (a (k * 12 + 25 - 3) : ℚ) = 8 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 25 - 3 = (12 * (k + 1) + 10) by omega]
      exact rowValue1 (k + 1)
    have val4 : (a (k * 12 + 25 - 4) : ℚ) = 7 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 25 - 4 = (12 * (k + 1) + 9) by omega]
      exact rowValue0 (k + 1)
    have val7 : (a (k * 12 + 25 - 7) : ℚ) = 13 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 25 - 7 = (12 * k + 18) by omega]
      exact rowValue9 k
    simp only [val0, val3, val4, val7]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 26) : ℚ) = 10 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 26 = (12 * (k + 1) + 14) by omega]
      exact rowValue5 (k + 1)
    have val3 : (a (k * 12 + 26 - 3) : ℚ) = 12 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 26 - 3 = (12 * (k + 1) + 11) by omega]
      exact rowValue2 (k + 1)
    have val4 : (a (k * 12 + 26 - 4) : ℚ) = 8 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 26 - 4 = (12 * (k + 1) + 10) by omega]
      exact rowValue1 (k + 1)
    have val7 : (a (k * 12 + 26 - 7) : ℚ) = 20 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 26 - 7 = (12 * k + 19) by omega]
      exact rowValue10 k
    simp only [val0, val3, val4, val7]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 27) : ℚ) = 15 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 27 = (12 * (k + 1) + 15) by omega]
      exact rowValue6 (k + 1)
    have val3 : (a (k * 12 + 27 - 3) : ℚ) = 7 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 27 - 3 = (12 * (k + 1) + 12) by omega]
      exact rowValue3 (k + 1)
    have val4 : (a (k * 12 + 27 - 4) : ℚ) = 12 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 27 - 4 = (12 * (k + 1) + 11) by omega]
      exact rowValue2 (k + 1)
    have val7 : (a (k * 12 + 27 - 7) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 27 - 7 = (12 * k + 20) by omega]
      exact rowValue11 k
    simp only [val0, val3, val4, val7]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
lemma convolution : ∀ n : ℕ, (1) * (if 0 ≤ n then (a (n - 0) : ℚ) else 0) + (-1) * (if 3 ≤ n then (a (n - 3) : ℚ) else 0) + (-1) * (if 4 ≤ n then (a (n - 4) : ℚ) else 0) + (1) * (if 7 ≤ n then (a (n - 7) : ℚ) else 0) =
      (2) * (if n = 1 then (1 : ℚ) else 0) + (5) * (if n = 3 then (1 : ℚ) else 0) + (2) * (if n = 5 then (1 : ℚ) else 0) + (-2) * (if n = 6 then (1 : ℚ) else 0) + (3) * (if n = 7 then (1 : ℚ) else 0) := by
  intro n
  by_cases small : n < 16
  · interval_cases n <;> norm_num [initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7, initial8, initial9, initial10, initial11, initial12, initial13, initial14, initial15] at *
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k * 12 + 16 ∨ n = k * 12 + 17 ∨ n = k * 12 + 18 ∨ n = k * 12 + 19 ∨ n = k * 12 + 20 ∨ n = k * 12 + 21 ∨ n = k * 12 + 22 ∨ n = k * 12 + 23 ∨ n = k * 12 + 24 ∨ n = k * 12 + 25 ∨ n = k * 12 + 26 ∨ n = k * 12 + 27 := ⟨(n - 16) / 12, by omega⟩
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have val0 : (a (k * 12 + 16) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 16 = (12 * k + 16) by omega]
      exact rowValue7 k
    have val3 : (a (k * 12 + 16 - 3) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 16 - 3 = (12 * k + 13) by omega]
      exact rowValue4 k
    have val4 : (a (k * 12 + 16 - 4) : ℚ) = 7 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 16 - 4 = (12 * k + 12) by omega]
      exact rowValue3 k
    have val7 : (a (k * 12 + 16 - 7) : ℚ) = 7 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 16 - 7 = (12 * k + 9) by omega]
      exact rowValue0 k
    simp only [val0, val3, val4, val7, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 17) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 17 = (12 * k + 17) by omega]
      exact rowValue8 k
    have val3 : (a (k * 12 + 17 - 3) : ℚ) = 10 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 17 - 3 = (12 * k + 14) by omega]
      exact rowValue5 k
    have val4 : (a (k * 12 + 17 - 4) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 17 - 4 = (12 * k + 13) by omega]
      exact rowValue4 k
    have val7 : (a (k * 12 + 17 - 7) : ℚ) = 8 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 17 - 7 = (12 * k + 10) by omega]
      exact rowValue1 k
    simp only [val0, val3, val4, val7, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 18) : ℚ) = 13 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 18 = (12 * k + 18) by omega]
      exact rowValue9 k
    have val3 : (a (k * 12 + 18 - 3) : ℚ) = 15 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 18 - 3 = (12 * k + 15) by omega]
      exact rowValue6 k
    have val4 : (a (k * 12 + 18 - 4) : ℚ) = 10 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 18 - 4 = (12 * k + 14) by omega]
      exact rowValue5 k
    have val7 : (a (k * 12 + 18 - 7) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 18 - 7 = (12 * k + 11) by omega]
      exact rowValue2 k
    simp only [val0, val3, val4, val7, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 19) : ℚ) = 20 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 19 = (12 * k + 19) by omega]
      exact rowValue10 k
    have val3 : (a (k * 12 + 19 - 3) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 19 - 3 = (12 * k + 16) by omega]
      exact rowValue7 k
    have val4 : (a (k * 12 + 19 - 4) : ℚ) = 15 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 19 - 4 = (12 * k + 15) by omega]
      exact rowValue6 k
    have val7 : (a (k * 12 + 19 - 7) : ℚ) = 7 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 19 - 7 = (12 * k + 12) by omega]
      exact rowValue3 k
    simp only [val0, val3, val4, val7, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 20) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 20 = (12 * k + 20) by omega]
      exact rowValue11 k
    have val3 : (a (k * 12 + 20 - 3) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 20 - 3 = (12 * k + 17) by omega]
      exact rowValue8 k
    have val4 : (a (k * 12 + 20 - 4) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 20 - 4 = (12 * k + 16) by omega]
      exact rowValue7 k
    have val7 : (a (k * 12 + 20 - 7) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 20 - 7 = (12 * k + 13) by omega]
      exact rowValue4 k
    simp only [val0, val3, val4, val7, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 21) : ℚ) = 7 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 21 = (12 * (k + 1) + 9) by omega]
      exact rowValue0 (k + 1)
    have val3 : (a (k * 12 + 21 - 3) : ℚ) = 13 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 21 - 3 = (12 * k + 18) by omega]
      exact rowValue9 k
    have val4 : (a (k * 12 + 21 - 4) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 21 - 4 = (12 * k + 17) by omega]
      exact rowValue8 k
    have val7 : (a (k * 12 + 21 - 7) : ℚ) = 10 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 21 - 7 = (12 * k + 14) by omega]
      exact rowValue5 k
    simp only [val0, val3, val4, val7, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 22) : ℚ) = 8 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 22 = (12 * (k + 1) + 10) by omega]
      exact rowValue1 (k + 1)
    have val3 : (a (k * 12 + 22 - 3) : ℚ) = 20 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 22 - 3 = (12 * k + 19) by omega]
      exact rowValue10 k
    have val4 : (a (k * 12 + 22 - 4) : ℚ) = 13 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 22 - 4 = (12 * k + 18) by omega]
      exact rowValue9 k
    have val7 : (a (k * 12 + 22 - 7) : ℚ) = 15 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 22 - 7 = (12 * k + 15) by omega]
      exact rowValue6 k
    simp only [val0, val3, val4, val7, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 23) : ℚ) = 12 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 23 = (12 * (k + 1) + 11) by omega]
      exact rowValue2 (k + 1)
    have val3 : (a (k * 12 + 23 - 3) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 23 - 3 = (12 * k + 20) by omega]
      exact rowValue11 k
    have val4 : (a (k * 12 + 23 - 4) : ℚ) = 20 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 23 - 4 = (12 * k + 19) by omega]
      exact rowValue10 k
    have val7 : (a (k * 12 + 23 - 7) : ℚ) = 12 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 23 - 7 = (12 * k + 16) by omega]
      exact rowValue7 k
    simp only [val0, val3, val4, val7, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 24) : ℚ) = 7 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 24 = (12 * (k + 1) + 12) by omega]
      exact rowValue3 (k + 1)
    have val3 : (a (k * 12 + 24 - 3) : ℚ) = 7 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 24 - 3 = (12 * (k + 1) + 9) by omega]
      exact rowValue0 (k + 1)
    have val4 : (a (k * 12 + 24 - 4) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 24 - 4 = (12 * k + 20) by omega]
      exact rowValue11 k
    have val7 : (a (k * 12 + 24 - 7) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 24 - 7 = (12 * k + 17) by omega]
      exact rowValue8 k
    simp only [val0, val3, val4, val7, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 25) : ℚ) = 12 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 25 = (12 * (k + 1) + 13) by omega]
      exact rowValue4 (k + 1)
    have val3 : (a (k * 12 + 25 - 3) : ℚ) = 8 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 25 - 3 = (12 * (k + 1) + 10) by omega]
      exact rowValue1 (k + 1)
    have val4 : (a (k * 12 + 25 - 4) : ℚ) = 7 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 25 - 4 = (12 * (k + 1) + 9) by omega]
      exact rowValue0 (k + 1)
    have val7 : (a (k * 12 + 25 - 7) : ℚ) = 13 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 25 - 7 = (12 * k + 18) by omega]
      exact rowValue9 k
    simp only [val0, val3, val4, val7, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 26) : ℚ) = 10 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 26 = (12 * (k + 1) + 14) by omega]
      exact rowValue5 (k + 1)
    have val3 : (a (k * 12 + 26 - 3) : ℚ) = 12 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 26 - 3 = (12 * (k + 1) + 11) by omega]
      exact rowValue2 (k + 1)
    have val4 : (a (k * 12 + 26 - 4) : ℚ) = 8 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 26 - 4 = (12 * (k + 1) + 10) by omega]
      exact rowValue1 (k + 1)
    have val7 : (a (k * 12 + 26 - 7) : ℚ) = 20 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 26 - 7 = (12 * k + 19) by omega]
      exact rowValue10 k
    simp only [val0, val3, val4, val7, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring
  · have val0 : (a (k * 12 + 27) : ℚ) = 15 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 27 = (12 * (k + 1) + 15) by omega]
      exact rowValue6 (k + 1)
    have val3 : (a (k * 12 + 27 - 3) : ℚ) = 7 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 27 - 3 = (12 * (k + 1) + 12) by omega]
      exact rowValue3 (k + 1)
    have val4 : (a (k * 12 + 27 - 4) : ℚ) = 12 + 10 * (((k + 1) : ℕ) : ℚ) := by
      rw [show k * 12 + 27 - 4 = (12 * (k + 1) + 11) by omega]
      exact rowValue2 (k + 1)
    have val7 : (a (k * 12 + 27 - 7) : ℚ) = 14 + 10 * ((k : ℕ) : ℚ) := by
      rw [show k * 12 + 27 - 7 = (12 * k + 20) by omega]
      exact rowValue11 k
    simp only [val0, val3, val4, val7, if_pos (by omega), if_neg (by omega), Nat.sub_zero]
    <;> push_cast
    <;> norm_num [pow_add, pow_mul] <;> ring

open PowerSeries

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
lemma generating_function : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2)) =
      X * (2 + 5 * X ^ 2 + 2 * X ^ 4 - 2 * X ^ 5 + 3 * X ^ 6) := by
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  calc
    _ = C (1 : ℚ) * (s * X ^ 0) + C (-1 : ℚ) * (s * X ^ 3) + C (-1 : ℚ) * (s * X ^ 4) + C (1 : ℚ) * (s * X ^ 7) := by simp only [map_neg, map_one, map_ofNat] <;> ring
    _ = C (2 : ℚ) * (X ^ 1) + C (5 : ℚ) * (X ^ 3) + C (2 : ℚ) * (X ^ 5) + C (-2 : ℚ) * (X ^ 6) + C (3 : ℚ) * (X ^ 7) := by
      apply PowerSeries.ext
      intro n
      simp only [map_add, coeff_C_mul]
      simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
      exact convolution n
    _ = _ := by simp only [map_neg, map_one, map_ofNat] <;> ring

end RowProof

open RowProof

open Ours_oeis_a267213
open PowerSeries in
lemma old_result :
    (∀ n : ℕ, 7 < n → (a n : ℚ) = (a (n - 3) : ℚ) + (a (n - 4) : ℚ) - (a (n - 7) : ℚ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2)) =
      X * (2 + 5 * X ^ 2 + 2 * X ^ 4 - 2 * X ^ 5 + 3 * X ^ 6)) :=
  ⟨claim0, generating_function⟩

namespace Ours_oeis_a267213

def window (t : ℕ) (i : ℤ) : ℕ → List Bool
  | 0 => []
  | m + 1 => OMA.S_oeis_a267213.cell 109 t i :: window t (i + 1) m

lemma window_append (t : ℕ) (i : ℤ) (m k : ℕ) :
    window t i (m + k) = window t i m ++ window t (i + m) k := by
  induction m generalizing i with
  | zero => simp [window]
  | succ m ih =>
    rw [Nat.succ_add, window, window, List.cons_append, ih]
    congr 3 <;> push_cast <;> ring

lemma outside_window (t : ℕ) (i : ℤ) (hi : i < -(t : ℤ) ∨ (t : ℤ) < i) :
    OMA.S_oeis_a267213.cell 109 t i = (row t).1 := by
  induction t generalizing i with
  | zero => simp [OMA.S_oeis_a267213.cell, row, show i ≠ 0 by omega]
  | succ t ih =>
    simp only [OMA.S_oeis_a267213.cell]
    rw [ih (i - 1) (by omega), ih i (by omega), ih (i + 1) (by omega)]
    rfl

lemma scan_window (t : ℕ) (i : ℤ) (m : ℕ) :
    sweep (OMA.S_oeis_a267213.cell 109 t (i - 2)) (OMA.S_oeis_a267213.cell 109 t (i - 1)) (window t i m) =
      window (t + 1) (i - 1) m := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
    simp only [window, sweep, List.cons.injEq]
    constructor
    · simp only [OMA.S_oeis_a267213.cell, show i - 1 - 1 = i - 2 by ring, show i - 1 + 1 = i by ring]
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
      ∑ j ∈ Finset.range m, if OMA.S_oeis_a267213.cell 109 t ((j : ℤ) + i) then 1 else 0 := by
  induction m generalizing i with
  | zero => simp [window]
  | succ m ih =>
    rw [window, List.count_cons, ih, Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Int.zero_add, Nat.cast_zero,
      Int.add_right_comm _ 1 i, Int.add_assoc]
    cases OMA.S_oeis_a267213.cell 109 t i <;> simp

lemma row_on (t : ℕ) : ((row t).2).count true = OMA.S_oeis_a267213.onCount 109 t := by
  rw [row_window, window_count]
  simp only [OMA.S_oeis_a267213.onCount, sub_eq_add_neg]

lemma window_length (t m : ℕ) (i : ℤ) : (window t i m).length = m := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih => simp [window, ih]

lemma count_both (w : List Bool) : w.count true + w.count false = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [List.count_cons] <;> omega

lemma row_off (t : ℕ) : (((row t).2).count false : ℤ) = 2 * (t : ℤ) + 1 - OMA.S_oeis_a267213.onCount 109 t := by
  have h := count_both ((row t).2)
  rw [row_on, row_window, window_length] at h
  rw [row_window]
  omega

lemma sequence_eq (n : ℕ) : OMA.S_oeis_a267213.a n = (a n : ℤ) := by
  exact (row_off n).symm

end Ours_oeis_a267213

theorem OMA.solution : type_of% @OMA.S_oeis_a267213.main := by
  simp only [sequence_eq, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat] 
  exact ⟨by
    intro n h
    first | exact old_result.1 n h | exact_mod_cast old_result.1 n h, old_result.2⟩
