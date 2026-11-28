import OMAReductions.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1
import Mathlib
/-!
Of nine rows, five have the same permutation sign. Every relative
permutation within those five is an even derangement. Its cycle type is
one of (9), (5,2,2), (4,3,2), (3,3,3). The first three are the hypotheses.

If none of the first three types occurs in the chosen rows, normalize the
first pair to the identity and (012)(345)(678). Enumerating three more
compatible rows gives 825 unordered triples. Column and symbol relabelings
send every triple to one of four five-row rectangles. The four branch
certificates prove a transversal in every completion. The normalization
and both finite checks are verified here. The bitboard update invariant
adapts the order-seven proof by @tkaiman.
-/

namespace OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1_H2_R1
open LatinSquare

def H1 : Prop := ∀ L : LatinSquare 9, (∀ j, L.mat 0 j = j) →
  (∀ i, L.mat i 0 = i) → L.mat 1 = ![1, 2, 3, 4, 5, 6, 7, 8, 0] →
  ∃ σ, IsTransversal L σ

def H2 : Prop := ∀ L : LatinSquare 9, (∀ j, L.mat 0 j = j) →
  (∀ i, L.mat i 0 = i) → L.mat 1 = ![1, 2, 3, 4, 0, 6, 5, 8, 7] →
  ∃ σ, IsTransversal L σ

def H3 : Prop := ∀ L : LatinSquare 9, (∀ j, L.mat 0 j = j) →
  (∀ i, L.mat i 0 = i) → L.mat 1 = ![1, 2, 3, 0, 5, 6, 4, 8, 7] →
  ∃ σ, IsTransversal L σ

/-- Eight fixed entries forbid the ninth indicated bit in any square
without a transversal. The omitted row is arbitrary. -/
theorem forbidEight (L : LatinSquare 9) (bad : ¬ ∃ σ, IsTransversal L σ)
    (B : Fin 9 → Fin 9 → Nat) (valid : ∀ r c, (B r c).testBit (L.mat r c).val = true)
    (cols syms : Equiv.Perm (Fin 9)) (skip : Fin 9)
    (known : ∀ r, r ≠ skip → ∀ v : Fin 9,
      (B r (cols r)).testBit v.val = true → v = syms r) :
    L.mat skip (cols skip) ≠ syms skip := by
  intro last
  apply bad
  refine ⟨cols, cols.injective, ?_⟩
  have h : (fun r => L.mat r (cols r)) = syms := by
    funext r
    by_cases e : r = skip
    · simpa [e] using last
    · exact known r e _ (valid r (cols r))
  rw [h]
  exact syms.injective

/-- Any seven known cells on a transversal permutation create a binary clause. -/
theorem sevenClause (L : LatinSquare 9) (bad : ¬ ∃ σ, IsTransversal L σ)
    (c s : Equiv.Perm (Fin 9)) (a b : Fin 9)
    (known : ∀ r, r ≠ a → r ≠ b → L.mat r (c r) = s r) :
    ¬ (L.mat a (c a) = s a ∧ L.mat b (c b) = s b) := by
  rintro ⟨ha,hb⟩
  apply bad
  refine ⟨c, c.injective, ?_⟩
  have eq : (fun r => L.mat r (c r)) = s := by
    funext r
    by_cases h : r = a
    · exact h ▸ ha
    by_cases k : r = b
    · exact k ▸ hb
    exact known r h k
  rw [eq]
  exact s.injective


/-- The signed differences on a full transversal sum to zero modulo nine. -/
theorem deltaTotal (L : LatinSquare 9) (σ : Fin 9 → Fin 9) (h : IsTransversal L σ) :
    (∑ r : Fin 9, (((L.mat r (σ r)).val : ℤ) - r.val - (σ r).val)) = -36 := by
  let cols := Equiv.ofBijective σ ⟨h.1, Finite.surjective_of_injective h.1⟩
  let syms := Equiv.ofBijective (fun i => L.mat i (σ i)) ⟨h.2, Finite.surjective_of_injective h.2⟩
  have sumCols := Equiv.sum_comp cols (fun i : Fin 9 => (i.val : ℤ))
  have sumSyms := Equiv.sum_comp syms (fun i : Fin 9 => (i.val : ℤ))
  have sumRows : (∑ i : Fin 9, (i.val : ℤ)) = 36 := by decide +kernel
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  change (∑ i : Fin 9, ((syms i).val : ℤ)) - (∑ i : Fin 9, (i.val : ℤ)) -
    (∑ i : Fin 9, ((cols i).val : ℤ)) = -36
  rw [sumCols,sumSyms,sumRows]
  decide

/- Every completion of each of the four displayed five-row rectangles
has a transversal. Each branch of a rectangle certificate is checked on a
729-bit domain board. -/
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 60000 in
theorem closeRectangles (k : Fin 4) (L : LatinSquare 9) (side : ∀ r, L.mat r 0 = r)
    (known : ∀ row ∈ (![[![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![2, 0, 1, 5, 3, 4, 8, 6, 7],
    ![3, 4, 5, 6, 7, 8, 0, 1, 2],
    ![4, 5, 3, 7, 8, 6, 1, 2, 0]],
      [![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![2, 0, 1, 5, 3, 4, 8, 6, 7],
    ![3, 4, 5, 6, 7, 8, 0, 1, 2],
    ![6, 7, 8, 0, 1, 2, 3, 4, 5]],
      [![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![2, 0, 1, 5, 3, 4, 8, 6, 7],
    ![3, 4, 5, 6, 7, 8, 0, 1, 2],
    ![6, 7, 8, 1, 2, 0, 5, 3, 4]],
      [![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![2, 3, 6, 5, 8, 1, 0, 4, 7],
    ![3, 4, 5, 8, 6, 7, 1, 2, 0],
    ![4, 5, 3, 6, 7, 8, 2, 0, 1]]] : Fin 4 → List (Fin 9 → Fin 9)) k, L.mat (row 0) = row) : ∃ σ, IsTransversal L σ := by
  let ALL729 : Nat := 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  let ROW_BIT0 : Nat := 0x1008040201008040201
  let COL_BIT0 : Nat := 0x1000000000000000000008000000000000000000040000000000000000000200000000000000000001000000000000000000008000000000000000000040000000000000000000200000000000000000001

  let dom (B r c : Nat) : Nat :=
    Nat.land (Nat.shiftRight B ((r * 9 + c) * 9)) 511

  let rowMask (r v : Nat) : Nat := Nat.shiftLeft ROW_BIT0 (r * 81 + v)
  let colMask (c v : Nat) : Nat := Nat.shiftLeft COL_BIT0 (c * 9 + v)
  let cellBit (r c v : Nat) : Nat := Nat.shiftLeft 1 ((r * 9 + c) * 9 + v)
  let cellAll (r c : Nat) : Nat := Nat.shiftLeft 511 ((r * 9 + c) * 9)

  let clearCell (B r c v : Nat) : Nat :=
    let kill := Nat.xor (Nat.lor (Nat.lor (rowMask r v) (colMask c v)) (cellAll r c)) (cellBit r c v)
    Nat.land B (Nat.xor ALL729 kill)

  let ValidBoard (L : LatinSquare 9) (B : Nat) : Prop :=
    ∀ r c : Fin 9, B.testBit ((r.val * 9 + c.val) * 9 + (L.mat r c).val) = true

  have testBit_ALL729 {w : Nat} (hw : w < 729) : ALL729.testBit w = true := by
    have h1 : ALL729 = 2 ^ 400 * 2 ^ 329 - 1 := by decide +kernel
    have h : ALL729 = 2 ^ 729 - 1 := by rw [h1, ← pow_add]
    rw [h, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hw

  have testBit_shiftLeft_local (x s w : Nat) :
      (Nat.shiftLeft x s).testBit w = (decide (s ≤ w) && x.testBit (w - s)) := by
    change (x <<< s).testBit w = _
    rw [Nat.testBit_shiftLeft]

  have testBit_ROW_BIT0 (k : Nat) :
      ROW_BIT0.testBit k = decide (k < 81 ∧ k % 9 = 0) := by
    by_cases hk : k < 81
    · revert k
      decide
    · have hlt : ROW_BIT0 < 2 ^ 81 := by decide
      have hge : 81 ≤ k := by omega
      have hpow : ROW_BIT0 < 2 ^ k := lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hge)
      rw [Nat.testBit_lt_two_pow hpow]
      simp [hk]

  have testBit_COL_BIT0 (k : Nat) :
      COL_BIT0.testBit k = decide (k < 729 ∧ k % 81 = 0) := by
    by_cases h : k < 729
    · have hcheck : ∀ i : Fin 729, COL_BIT0.testBit i.val = decide (i.val < 729 ∧ i.val % 81 = 0) := by decide +kernel
      exact hcheck ⟨k, h⟩
    · have hlt : COL_BIT0 < 2 ^ 729 := by decide +kernel
      have high (x n u : Nat) (small : x < 2 ^ n) (le : n ≤ u) : x.testBit u = false :=
        @Nat.testBit_lt_two_pow x u (@Nat.lt_of_lt_of_le x (2 ^ n) (2 ^ u) small
          (@Nat.pow_le_pow_right 2 (by decide) n u le))
      rw [high COL_BIT0 729 k hlt (Nat.le_of_not_lt h)]
      simp [h]

  have testBit_cellBit (r c v w : Nat) :
      (cellBit r c v).testBit w = decide ((r * 9 + c) * 9 + v = w) := by
    unfold cellBit
    change (1 <<< ((r * 9 + c) * 9 + v)).testBit w = _
    rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

  have testBit_rowMask (r v r' c' v' : Fin 9) :
      (rowMask r.val v.val).testBit ((r'.val * 9 + c'.val) * 9 + v'.val) =
        decide (r' = r ∧ v' = v) := by
    unfold rowMask
    rw [testBit_shiftLeft_local, testBit_ROW_BIT0]
    have hr := r.isLt; have hv := v.isLt
    have hr' := r'.isLt; have hc' := c'.isLt; have hv' := v'.isLt
    by_cases h1 : r' = r ∧ v' = v
    · rcases h1 with ⟨rfl, rfl⟩
      simp only [and_self, decide_true, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, by omega, by omega⟩
    · simp only [decide_eq_false h1, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases hle : r.val * 81 + v.val ≤ (r'.val * 9 + c'.val) * 9 + v'.val
      · right
        intro ⟨hsub, hmod⟩
        apply h1
        have hre : r'.val = r.val := by omega
        have hve : v'.val = v.val := by omega
        exact ⟨Fin.ext hre, Fin.ext hve⟩
      · left; exact hle

  have testBit_colMask (c v r' c' v' : Fin 9) :
      (colMask c.val v.val).testBit ((r'.val * 9 + c'.val) * 9 + v'.val) =
        decide (c' = c ∧ v' = v) := by
    unfold colMask
    rw [testBit_shiftLeft_local, testBit_COL_BIT0]
    have hc := c.isLt; have hv := v.isLt
    have hr' := r'.isLt; have hc' := c'.isLt; have hv' := v'.isLt
    by_cases h1 : c' = c ∧ v' = v
    · rcases h1 with ⟨rfl, rfl⟩
      simp only [and_self, decide_true, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, by omega, by omega⟩
    · simp only [decide_eq_false h1, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases hle : c.val * 9 + v.val ≤ (r'.val * 9 + c'.val) * 9 + v'.val
      · right
        intro ⟨hsub, hmod⟩
        apply h1
        have hce : c'.val = c.val := by omega
        have hve : v'.val = v.val := by omega
        exact ⟨Fin.ext hce, Fin.ext hve⟩
      · left; exact hle

  have testBit_cellAll (r c r' c' v' : Fin 9) :
      (cellAll r.val c.val).testBit ((r'.val * 9 + c'.val) * 9 + v'.val) =
        decide (r' = r ∧ c' = c) := by
    unfold cellAll
    rw [testBit_shiftLeft_local]
    have hr := r.isLt; have hc := c.isLt
    have hr' := r'.isLt; have hc' := c'.isLt; have hv' := v'.isLt
    by_cases h1 : r' = r ∧ c' = c
    · rcases h1 with ⟨rfl, rfl⟩
      have h511 : (511 : Nat).testBit v'.val = true := by
        have : (511 : Nat) = 2 ^ 9 - 1 := rfl
        rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hv'
      simp only [and_self, decide_true, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, by simpa [show (r'.val * 9 + c'.val) * 9 + v'.val - (r'.val * 9 + c'.val) * 9 = v'.val by omega] using h511⟩
    · simp only [decide_eq_false h1, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases hle : (r.val * 9 + c.val) * 9 ≤ (r'.val * 9 + c'.val) * 9 + v'.val
      · right
        have hgt : 9 ≤ (r'.val * 9 + c'.val) * 9 + v'.val - (r.val * 9 + c.val) * 9 := by
          by_contra hlt
          have : r'.val = r.val ∧ c'.val = c.val := by omega
          exact h1 ⟨Fin.ext this.1, Fin.ext this.2⟩
        have hpow : (511 : Nat) < 2 ^ ((r'.val * 9 + c'.val) * 9 + v'.val - (r.val * 9 + c.val) * 9) :=
          lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by omega) hgt)
        rw [Nat.testBit_lt_two_pow hpow]
      · left; exact hle

  have testBit_dom (B : Nat) (r c v : Fin 9) :
      (dom B r.val c.val).testBit v.val = B.testBit ((r.val * 9 + c.val) * 9 + v.val) := by
    unfold dom
    change ((B >>> ((r.val * 9 + c.val) * 9)) &&& 511).testBit v.val = _
    rw [Nat.testBit_and, Nat.testBit_shiftRight]
    have h511 : (511 : Nat).testBit v.val = true := by
      have : (511 : Nat) = 2 ^ 9 - 1 := rfl
      rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true v.isLt
    rw [h511, Bool.and_true]

  have eq_of_dom_eq_bit {L : LatinSquare 9} {B : Nat} (hB : ValidBoard L B)
      {r c v : Fin 9} (h : dom B r.val c.val = Nat.shiftLeft 1 v.val) : L.mat r c = v := by
    have hbit : (dom B r.val c.val).testBit (L.mat r c).val = true := by
      rw [testBit_dom]; exact hB r c
    rw [h] at hbit
    change (1 <<< v.val).testBit (L.mat r c).val = true at hbit
    rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_true_eq] at hbit
    exact Fin.ext hbit.symm

  have clearCell_valid {L : LatinSquare 9} {B : Nat} (hB : ValidBoard L B)
      {r c v : Fin 9} (heq : L.mat r c = v) :
      ValidBoard L (clearCell B r.val c.val v.val) := by
    intro r' c'
    unfold clearCell
    set v' := L.mat r' c'
    set w := (r'.val * 9 + c'.val) * 9 + v'.val
    have hw : w < 729 := by have := r'.isLt; have := c'.isLt; have := v'.isLt; omega
    change (B &&& (ALL729 ^^^ (((rowMask r.val v.val ||| colMask c.val v.val) ||| cellAll r.val c.val) ^^^ cellBit r.val c.val v.val))).testBit w = true
    rw [Nat.testBit_and, hB r' c', Bool.true_and, Nat.testBit_xor, testBit_ALL729 hw,
        Nat.testBit_xor, Nat.testBit_or, Nat.testBit_or,
        testBit_rowMask, testBit_colMask, testBit_cellAll, testBit_cellBit]
    have hcb : ((r.val * 9 + c.val) * 9 + v.val = w) ↔ (r' = r ∧ c' = c ∧ v' = v) := by
      have hr := r.isLt; have hc := c.isLt; have hv := v.isLt
      have hr' := r'.isLt; have hc' := c'.isLt; have hv' := v'.isLt
      constructor
      · intro h
        exact ⟨Fin.ext (by omega), Fin.ext (by omega), Fin.ext (by omega)⟩
      · rintro ⟨rfl, rfl, rfl⟩; rfl
    by_cases hrr : r' = r
    · subst hrr
      by_cases hcc : c' = c
      · subst hcc
        have hvv : v' = v := heq
        simp [hcb, hvv]
      · have hvv : v' ≠ v := fun hv => hcc (L.row_injective r' (hv.trans heq.symm))
        simp [hcb, hcc, hvv]
    · by_cases hcc : c' = c
      · subst hcc
        have hvv : v' ≠ v := fun hv => hrr (L.col_injective c' (hv.trans heq.symm))
        simp [hcb, hrr, hvv]
      · simp [hcb, hrr, hcc]


  let digit (p r : Nat) : Nat := (p >>> (4*r)) &&& 15

  let witness (B p : Nat) : Bool :=
    let cs := (List.range 9).map (digit p)
    let ds := (List.range 9).map (fun r => dom B r (digit p r))
    cs.all (· < 9) && cs.Nodup && ds.Nodup &&
      ds.all (fun d => d != 0 && (d &&& (d-1)) == 0)

  have witness_sound {B p : Nat} {L : LatinSquare 9} (valid : ValidBoard L B)
      (checked : witness B p = true) : ∃ σ, IsTransversal L σ := by
    simp only [witness, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at checked
    obtain ⟨⟨⟨bounds, cols⟩, syms⟩, single⟩ := checked
    have hr (i : Fin 9) : i.val ∈ List.range 9 := List.mem_range.mpr i.isLt
    let c (i : Fin 9) : Fin 9 := ⟨digit p i.val, bounds _ (List.mem_map_of_mem (hr i))⟩
    have uniq {f : Nat → Nat} (h : ((List.range 9).map f).Nodup) :
        Function.Injective (fun i : Fin 9 => f i.val) := by
      intro i j eq
      apply Fin.ext
      exact (List.inj_on_of_nodup_map h) (hr i) (hr j) eq
    refine ⟨c, fun i j h => uniq cols (congrArg Fin.val h), ?_⟩
    have bitsEq (i : Fin 9) : dom B i.val (c i).val = 1 <<< (L.mat i (c i)).val := by
      let d := dom B i.val (c i).val
      have h := single _ (List.mem_map_of_mem (f := fun r => dom B r (digit p r)) (hr i))
      have hs : (d != 0 && (d &&& (d-1)) == 0) = true := by simpa only [Bool.and_eq_true] using h
      have lt : d < 512 := Nat.lt_succ_of_le Nat.and_le_right
      have table : ∀ n < 512, (n != 0 && (n &&& (n-1)) == 0) = true →
          ∃ s : Fin 9, n = 1 <<< s.val := by decide +kernel
      obtain ⟨s,eq⟩ := table d lt hs
      exact eq.trans (congrArg (fun x : Fin 9 => 1 <<< x.val) (eq_of_dom_eq_bit valid eq).symm)
    intro i j h
    apply uniq syms
    exact (bitsEq i).trans ((congrArg (fun s : Fin 9 => 1 <<< s.val) h).trans (bitsEq j).symm)

  let run : Nat → Nat → List Nat → Option (List Nat) := Nat.rec
    (fun _ _ => none) (fun _ next B xs => match xs with
    | [] => none
    | n::rest =>
      if n < 81 then
        (List.range 9).foldlM (fun st v =>
          if (dom B (n/9) (n%9)).testBit v then next (clearCell B (n/9) (n%9) v) st else some st) rest
      else if witness B (n-81) then some rest else none)

  have visit {α : Type} {f : α → Nat → Option α} {xs : List Nat} {start finish : α}
      (ok : xs.foldlM f start = some finish) {v : Nat} (mem : v ∈ xs) :
      ∃ a b, f a v = some b := by
    induction xs generalizing start with
    | nil => simp at mem
    | cons x xs ih =>
      cases eq : f start x with
      | none => simp [List.foldlM_cons, eq] at ok
      | some a =>
        rcases List.mem_cons.mp mem with rfl | tail
        · exact ⟨start,a,eq⟩
        · exact ih (by simpa [List.foldlM_cons, eq] using ok) tail

  have run_sound (dep : Nat) (L : LatinSquare 9) {B : Nat} {xs ys : List Nat}
      (valid : ValidBoard L B) (ok : run dep B xs = some ys) : ∃ σ, IsTransversal L σ := by
    induction dep generalizing B xs ys with
    | zero => simp [run] at ok
    | succ d ih =>
      cases xs with
      | nil => simp [run] at ok
      | cons n rest =>
        by_cases hn : n < 81
        · simp only [run, if_pos hn] at ok
          let r : Fin 9 := ⟨n/9, by omega⟩
          let c : Fin 9 := ⟨n%9, by omega⟩
          let v := L.mat r c
          have bit : (dom B r.val c.val).testBit v.val = true := (testBit_dom B r c v).trans (valid r c)
          obtain ⟨a,b,h⟩ := visit ok (List.mem_range.mpr v.isLt)
          apply ih (clearCell_valid valid (rfl : L.mat r c = v))
          simpa only [show (dom B (n/9) (n%9)).testBit v.val = true from bit, if_true] using h
        · simp only [run, if_neg hn] at ok
          split at ok
          · exact witness_sound valid ‹_›
          · contradiction

  let seeds (rows : List (Fin 9 → Fin 9)) : List (Fin 9 × Fin 9 × Fin 9) :=
    (List.finRange 9).map (fun r => (r,0,r)) ++ rows.flatMap (fun row =>
      (List.finRange 9).map (fun c => (row 0,c,row c)))

  let initial (rows : List (Fin 9 → Fin 9)) : Nat :=
    (seeds rows).foldl (fun B t => clearCell B t.1.val t.2.1.val t.2.2.val) ALL729

  have initial_valid (rows : List (Fin 9 → Fin 9)) (L : LatinSquare 9)
      (side : ∀ r, L.mat r 0 = r) (known : ∀ row ∈ rows, L.mat (row 0) = row) :
      ValidBoard L (initial rows) := by
    have agree (t : Fin 9 × Fin 9 × Fin 9) (ht : t ∈ seeds rows) : L.mat t.1 t.2.1 = t.2.2 := by
      rcases List.mem_append.mp ht with h | h
      · obtain ⟨r,_,rfl⟩ := List.mem_map.mp h
        exact side r
      · obtain ⟨row,hr,h⟩ := List.mem_flatMap.mp h
        obtain ⟨c,_,rfl⟩ := List.mem_map.mp h
        exact congrFun (known row hr) c
    have go (xs : List (Fin 9 × Fin 9 × Fin 9)) (B : Nat) (h : ValidBoard L B)
        (hh : ∀ t ∈ xs, L.mat t.1 t.2.1 = t.2.2) :
        ValidBoard L (xs.foldl (fun b t => clearCell b t.1.val t.2.1.val t.2.2.val) B) := by
      induction xs generalizing B with
      | nil => exact h
      | cons x xs ih =>
        exact ih _ (clearCell_valid h (hh x (by simp))) (fun t ht => hh t (by simp [ht]))
    apply go _ _ _ agree
    intro r c
    apply testBit_ALL729
    have := r.isLt
    have := c.isLt
    have := (L.mat r c).isLt
    omega

  let rect0 : List (Fin 9 → Fin 9) := [![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![2, 0, 1, 5, 3, 4, 8, 6, 7],
    ![3, 4, 5, 6, 7, 8, 0, 1, 2],
    ![4, 5, 3, 7, 8, 6, 1, 2, 0]]
  let stream0 : List Nat := List.flatten [
    [51, 60, 69, 78, 55, 73, 46, 64, 560493972, 64, 65, 56, 47, 74, 48, 4835411352, 5910004422, 74, 48, 4835411352, 50, 1632138147, 46, 64, 560493972, 64, 48, 75, 57, 66, 560493972, 12919989462, 14512649337, 26041927107, 64, 46, 73, 49, 58, 67, 76, 8658576297, 18807617652, 67, 5469919107, 17817941352, 58, 5973050052],
    [67, 76, 70, 74, 2182571412, 4838684052, 73, 50, 26043775107, 68, 5738100867, 59, 77, 9933715092, 23102452947, 65, 46, 4838684052, 73, 47, 308835732, 56, 74, 49, 5910004422, 4836518022, 308835732, 78, 55, 73, 46, 64, 49, 58, 67, 76, 8925963732, 17818997592, 26105706612, 58, 67, 76, 9764886402, 605455272, 26105706612, 64, 48, 75],
    [13254542787, 57, 66, 13423375542, 828909477, 5909267907, 74, 46, 8865215892, 64, 47, 4335367572, 56, 65, 48, 4332094662, 8862000537, 4335367572, 64, 46, 73, 8613557652, 73, 74, 56, 47, 65, 49, 26042663622, 8864039877, 65, 48, 26044023747, 8862000537, 46, 73, 8613557652, 73, 50, 5911115907, 68, 27128984787, 59, 77, 8613557652, 21844228227, 69, 78],
    [56, 74, 47, 65, 308835732, 65, 64, 55, 46, 73, 48, 10204174482, 8862991272, 73, 48, 8864098452, 50, 59, 677605797, 1382553492, 47, 65, 308835732, 65, 48, 75, 14529615717, 57, 8647087302, 9496450152, 26310366312, 65, 47, 74, 49, 58, 67, 76, 5472015192, 8925963732, 10268202882, 58, 67, 76, 5472015192, 17549326452, 10268202882, 74],
    [50, 26312148162, 68, 10033005762, 59, 8680207497, 77, 55, 5671253127, 64, 47, 8865215892, 74, 46, 560493972, 55, 73, 49, 8862991272, 10204971462, 560493972, 78, 56, 74, 47, 65, 49, 58, 26374321512, 67, 76, 4838684052, 306612102, 58, 67, 26877646722, 17551610712, 67, 1113683412, 17817634722, 65, 48, 75, 13522981992, 57, 66, 13256456337, 26609211237],
    [10204238952, 73, 47, 4838684052, 65, 46, 8613557652, 55, 64, 48, 4835411142, 8610342297, 8613557652, 65, 47, 74, 4335367572, 74, 73, 55, 46, 64, 49, 1631942787, 4836516777, 64, 48, 4835411142, 8610342297, 47, 74, 4335367572, 74, 50, 10206020802, 68, 59, 77, 5671126152, 1633175427, 27146078082, 69, 78, 64, 73, 46, 55, 50],
    [68, 59, 26122418292, 23120344017, 59, 359146632, 23102769027, 68, 27128984787, 59, 77, 8613557652, 307718292, 55, 48, 4399068627, 75, 14512584147, 57, 26088863907, 14530476177, 74, 46, 8613557652, 55, 47, 4838684052, 56, 8708851092, 65, 48, 4835411142, 8610342297, 55, 46, 73, 74, 65, 47, 56, 49, 641959842, 4836516777, 56, 48, 4835411142, 8610342297, 73],
    [8865215892, 46, 73, 8865215892, 73, 49, 58, 67, 76, 8925963732, 641959842, 26105706612, 4400371587, 78, 65, 74, 47, 56, 50, 68, 59, 77, 5989759092, 1361535957, 27146078082, 68, 59, 77, 5671126152, 23104615377, 27146078082, 56, 48, 8694040482, 75, 14529365922, 57, 593590437, 12904330647, 73, 47, 4335367572, 56, 46, 8865215892, 55, 655787412, 64],
    [48, 4332094662, 8862000537, 56, 47, 74, 73, 64, 46, 55, 49, 25807913922, 8864039877, 55, 48, 4332094662, 8862000537, 74, 4838684052, 47, 74, 4838684052, 74, 49, 58, 26374321512, 67, 76, 4838684052, 18824583012, 8695338852, 52, 53, 48, 49, 50, 46, 47, 55, 64, 4840711572, 56, 562521492, 46, 49, 50, 47, 56],
    [74, 65, 64, 4840711572, 65, 74, 73, 8867243412, 50, 49, 47, 55, 73, 8867243412, 56, 8615585172, 60, 69, 78, 70, 1988445042, 61, 79, 62, 32279581287, 1752515172, 79, 80, 27924845157, 78, 70, 1988445042, 61, 79, 62, 36306113127, 71, 35977908837, 36245295507, 79, 62, 71, 58, 36295754337, 2271560067, 69, 78, 61],
    [1736786802, 70, 79, 62, 34468016742, 80, 2255831652, 79, 36245295507, 78, 61, 70, 79, 62, 35977908837, 71, 35977908837, 36245295507, 70, 32218763667, 79, 62, 71, 56, 1651868802, 677855622, 2271560067, 69, 78, 61, 1736786802, 70, 31683990642, 79, 62, 2019901827, 25911636582, 78, 61, 2019901827, 70, 79, 62, 80, 56, 27691069782, 677855622, 80],
    [75, 23628902787, 27657458802, 53, 60, 69, 78, 71, 2255831922, 62, 80, 61, 31742710227, 70, 31683989907, 32218763877, 80, 32218763877, 78, 70, 61, 1736786307, 25895907747, 27657458067, 69, 78, 62, 1752515442, 71, 80, 61, 34483745382, 79, 55, 25812218277, 310863252, 80, 79, 61, 55, 4337395092, 32235668307, 78, 62, 71, 80, 61, 70],
    [79, 70, 36245295717, 79, 75, 19451302497, 71, 80, 70, 1736786307, 80, 61, 30174097827, 1736786307, 69, 78, 61, 70, 27657458067, 79, 35977909362, 62, 70, 79, 80, 68, 31010931297, 30205555302, 78, 61, 70, 27924845682, 31683989907, 62, 70, 79, 80, 27924845682, 30205555302, 52, 53, 48, 49, 50, 47, 46, 55, 73],
    [64, 56, 8867243412, 64, 73, 65, 8615585172, 47, 49, 50, 46, 55, 73, 64, 558396327, 64, 73, 8611460007, 50, 49, 46, 55, 73, 64, 74, 562521492, 64, 73, 56, 4840711572, 60, 69, 78, 70, 1988445042, 61, 79, 80, 71, 55, 46, 30167028372, 30442476177, 34383279222, 79, 62, 32279581287, 71],
    [32218763667, 80, 56, 2188784742, 678839652, 78, 70, 61, 30174098802, 79, 62, 71, 58, 36295754337, 1752515172, 1988445042, 69, 78, 61, 1736786802, 70, 79, 36245295507, 79, 62, 34468016742, 34483745187, 78, 61, 70, 79, 62, 30205555107, 71, 34468016742, 36245295507, 25895908722, 69, 78, 61, 70, 79, 62, 30205555107, 25911636582, 79, 62, 2255831652],
    [25911636582, 30205555107, 78, 61, 70, 79, 62, 30205555107, 80, 75, 19451302497, 79, 62, 35977908837, 71, 35977908837, 70, 79, 62, 2255831652, 53, 60, 69, 78, 71, 2255831922, 62, 80, 30205555302, 80, 61, 31742710227, 1736786307, 78, 70, 61, 79, 80, 71, 2019902052, 79, 34468017522, 27657458067, 69, 78, 62, 1752515442, 71],
    [80, 79, 25895907747, 80, 61, 34483745382, 25895907747, 78, 62, 71, 80, 61, 70, 79, 70, 79, 55, 1902477972, 36278907042, 79, 75, 17304146532, 25911637362, 69, 78, 61, 70, 27657458067, 30174097827, 62, 70, 79, 80, 68, 31010931297, 30205555302, 78, 61, 70, 2271560292, 31683989907, 62, 70, 79, 80, 55, 1902477972, 26079679317],
    [30205555302]]
  have close0 (L : LatinSquare 9) (side : ∀ r, L.mat r 0 = r)
      (known : ∀ row ∈ rect0, L.mat (row 0) = row) : ∃ σ, IsTransversal L σ :=
    run_sound 82 L (xs := stream0) (ys := []) (initial_valid rect0 L side known)
      (show run 82 (initial rect0) stream0 = some [] by decide +kernel)

  let rect1 : List (Fin 9 → Fin 9) := [![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![2, 0, 1, 5, 3, 4, 8, 6, 7],
    ![3, 4, 5, 6, 7, 8, 0, 1, 2],
    ![6, 7, 8, 0, 1, 2, 3, 4, 5]]
  let stream1 : List Nat := List.flatten [
    [38, 65, 47, 74, 44, 71, 53, 10822379412, 80, 43, 2166842772, 79, 30157190802, 75, 52, 14798046567, 10537173927, 53, 80, 43, 10805006727, 70, 52, 1969371282, 10537173927, 52, 10828658322, 79, 46, 37, 343422387, 80, 75, 66, 9496450917, 39, 48, 41, 22028715207, 50, 9501181842, 10794063762, 641222502, 71, 53, 80, 46, 37],
    [2267431842, 64, 73, 41, 50, 2270315367, 68, 77, 40, 4400371587, 34714448817, 21795735192, 2250601317, 4381500357, 80, 42, 2267431842, 51, 69, 37, 28001256132, 25821730707, 1669482342, 53, 80, 42, 51, 10292835522, 69, 78, 39, 66, 15049578357, 26644349352, 36056531352, 10292835522, 69, 25889886612, 78, 75, 39, 1747153317, 35249078727, 80, 42, 51, 69, 39],
    [48, 36007069602, 25821730707, 28001388402, 51, 69, 37, 46, 34428311427, 354968712, 25821730707, 1669482342, 74, 44, 71, 53, 80, 43, 34451109522, 52, 34451109522, 70, 31459411602, 10553411202, 80, 73, 37, 46, 64, 9463425222, 64, 40, 8908993977, 8950936497, 10821395592, 53, 80, 43, 52, 1971466677, 70, 79, 46, 643250322, 10572814482, 32298251922, 70, 52],
    [34446927762, 79, 17305843302, 1982346642, 80, 43, 52, 36291236967, 70, 79, 4370937462, 36291236967, 70, 52, 627524052, 79, 75, 76, 77, 1982346642, 71, 53, 80, 42, 51, 28003284162, 69, 27164443842, 78, 39, 15135168402, 48, 2167809957, 10275018852, 69, 78, 18624840642, 78, 37, 26399032257, 10250975397, 80, 73, 37, 46, 8942806152, 64, 41],
    [8925841032, 34948346007, 46, 8675419077, 2232578997, 53, 80, 42, 10788160962, 69, 27969738642, 78, 37, 27967702467, 10250975397, 80, 76, 42, 10788160962, 51, 69, 37, 17773430982, 17767168167, 1669482342, 47, 74, 44, 53, 661144482, 71, 35769169512, 80, 13539755682, 53, 71, 80, 42, 663110562, 51, 78, 75, 66, 9504315282, 64, 39, 13522917477, 8928651177],
    [34416514962, 80, 42, 34412582802, 51, 2204256102, 10291786137, 71, 80, 68, 77, 22129690212, 41, 50, 42, 2233939122, 34947417762, 50, 10040127897, 80, 42, 2204256102, 34446128322, 74, 44, 80, 53, 71, 43, 52, 70, 79, 78, 75, 39, 26424328617, 8682432402, 36291236967, 52, 70, 30686070402, 79, 26381146212, 2222076342, 71, 43, 52, 36291236967],
    [8681698962, 70, 68, 52, 1483878837, 31509721497, 1982346642, 53, 71, 43, 562521492, 8649135207, 71, 68, 50, 1482835842, 41, 77, 42, 34947352002, 8645936322, 34947298917, 80, 53, 71, 42, 8649070482, 69, 27248309442, 78, 37, 8675420052, 10259351382, 71, 42, 51, 78, 39, 48, 13539623337, 25856995797, 36056532882, 51, 25828677522, 78, 37, 36054319812, 8646653142],
    [53, 71, 42, 34947352002, 8682616002, 71, 68, 50, 41, 2250601317, 34947298917, 41, 77, 42, 34947352002, 35719165557, 34947298917, 65, 47, 74, 51, 42, 69, 78, 40, 660879462, 10251175842, 78, 40, 26390837442, 53, 10292835522, 80, 44, 10794305382, 13021505442, 69, 78, 37, 46, 73, 64, 26659080057, 10251957462, 46, 629557122, 64, 27716040867],
    [78, 75, 66, 39, 25907327397, 14579484537, 39, 660816342, 48, 37, 14579484537, 25822328022, 42, 69, 78, 41, 677726082, 52, 70, 30151160217, 1965441492, 79, 30205432962, 75, 70, 14864767077, 14512772307, 78, 41, 677726082, 52, 70, 79, 30151160217, 43, 44, 50, 660095847, 1633186947, 70, 27716114532, 79, 30205432962, 43, 10536636807, 69, 78, 37],
    [46, 10251961542, 64, 325220517, 10072634562, 10250979237, 78, 75, 66, 15149975202, 39, 660816342, 48, 37, 46, 13489957062, 64, 325220517, 73, 41, 26072155272, 10284971202, 13488973272, 74, 37, 46, 73, 64, 44, 8675423892, 71, 80, 53, 41, 8925841332, 34695636867, 53, 80, 50, 41, 8925841332, 34695636867, 80, 41, 34482501267, 8917446807, 64, 73],
    [44, 354972807, 8675420052, 73, 44, 71, 80, 53, 68, 41, 4890902727, 50, 34684814022, 77, 27248309442, 53, 8694290322, 80, 26096976582, 8675420052, 64, 73, 46, 42, 51, 4351751577, 69, 78, 41, 10336159572, 26375194497, 78, 41, 27247265652, 593856402, 8641737942, 46, 73, 42, 51, 4436939907, 69, 26660063097, 26090697942, 51, 78, 69, 40],
    [8730728292, 5956204707, 69, 5958042822, 78, 40, 26155956387, 76, 34695689592, 18841883352, 73, 42, 8641742022, 51, 4434834117, 69, 1663141797, 78, 36055302852, 46, 64, 73, 40, 76, 49, 67, 41, 8678564802, 50, 8731768482, 4887447192, 67, 41, 9999321012, 68, 9999321012, 22649337987, 17800722567, 73, 40, 67, 9714104487, 49, 8664482727, 76, 26090702022, 8641607382, 64],
    [73, 40, 49, 76, 67, 41, 8963569857, 390423252, 67, 5421168342, 76, 41, 5704418952, 17852364417, 49, 8964552897, 67, 19195323732, 17801704377, 47, 74, 46, 73, 37, 64, 42, 8909129637, 51, 69, 78, 40, 4435761027, 49, 4387533687, 4369581702, 69, 10251961542, 78, 14564741592, 64, 40, 354711687, 49, 8946480852, 67, 76, 39, 17232725442],
    [1210283367, 76, 39, 1193502822, 48, 4969486257, 4369581702, 37, 64, 44, 8942810247, 53, 8966911377, 71, 10822383252, 80, 41, 50, 8915023062, 68, 35199677622, 77, 13292827767, 50, 8966911377, 21533652627, 64, 40, 49, 17287971462, 67, 76, 41, 21810546312, 1210410882, 17767168167, 49, 343042182, 67, 2166646662, 76, 39, 1193502822, 48, 8945428377, 13237381317, 37, 64],
    [73, 44, 53, 360866952, 71, 10251957462, 80, 13524027222, 4381500357, 73, 44, 354972597, 53, 8932844457, 71, 80, 68, 41, 34964059752, 34948346007, 80, 41, 35819505252, 68, 1462256487, 35819505252, 64, 73, 42, 51, 4436939907, 69, 10251957462, 78, 18876479682, 4347819417, 73, 42, 321291672, 51, 8915027142, 69, 5704418952, 78, 13222570182, 74, 73, 37],
    [46, 64, 44, 71, 9463425222, 53, 80, 50, 41, 1445491557, 68, 9463425222, 21844477827, 34714183572, 8675419077, 64, 44, 71, 80, 53, 68, 41, 4890902727, 50, 8928651462, 34415408787, 53, 8928651462, 80, 40, 8908993977, 8950936497, 71, 5689607367, 53, 80, 41, 8925841032, 50, 6479505237, 34415408787, 34714187412, 46, 64, 40, 67, 76, 49],
    [41, 9714342087, 68, 18622806147, 9982543797, 49, 17287971462, 17767168167, 8908993977, 64, 40, 49, 76, 67, 41, 4937038017, 50, 21797808327, 4399068627, 67, 76, 41, 17856295092, 9799300737, 17500763862, 49, 4938021057, 67, 9748640697, 76, 31274919252, 46, 37, 64, 42, 51, 4436939907, 69, 26660063097, 26090697942, 51, 69, 78, 40, 8942549127, 76, 34712216712, 18841883352],
    [69, 5958042822, 78, 40, 8942549127, 76, 34444964727, 18841883352, 64, 40, 17767168167, 17534318292, 37, 64, 44, 354972807, 71, 6528464532, 53, 80, 41, 50, 23659046802, 373831032, 50, 8711066007, 34415408787, 80, 17768646582, 64, 42, 51, 623994072, 69, 78, 41, 44, 26375305377, 77, 17498797497, 23220733812, 78, 17852412072, 51, 325223832, 69, 5958042822, 78],
    [40, 17498797497, 76, 23136859347, 17498797497, 47, 65, 74, 46, 73, 37, 64, 42, 51, 10275018852, 69, 78, 66, 39, 75, 48, 41, 13220931027, 27131933907, 25856012757, 78, 18876479682, 8909125797, 64, 39, 66, 75, 48, 69, 42, 8727720357, 51, 9503266962, 78, 18875427012, 48, 4386399957, 75, 17820649302, 337864152, 37, 64, 44],
    [53, 8682300357, 71, 9513223842, 80, 41, 50, 23673730707, 77, 18564084657, 68, 9999320712, 9513223842, 8942806152, 64, 39, 8942479557, 66, 10855073442, 48, 75, 40, 17767168167, 67, 10821395592, 17585690547, 13505750232, 73, 37, 64, 42, 321291672, 51, 69, 78, 39, 48, 10275018852, 13222570182, 26124449937, 69, 9999620292, 78, 39, 48, 26175624312, 13222570182, 4368598902],
    [64, 41, 68, 10267990212, 50, 77, 40, 22113711057, 4434716547, 77, 40, 391406292, 67, 18622869897, 5402622087, 321226677, 37, 64, 44, 354972597, 53, 71, 34434266742, 71, 80, 68, 41, 34964059752, 50, 10073753217, 34683778707, 80, 17768646582, 64, 41, 8925841032, 68, 77, 50, 71, 44, 53, 80, 39, 13276186257, 8908993977, 22063640727, 50],
    [1483891842, 77, 18622869897, 74, 46, 73, 37, 64, 42, 8641742022, 51, 78, 69, 39, 4915947717, 25856012757, 69, 26644337112, 26088736677, 64, 39, 4915947717, 337864152, 37, 64, 44, 8675423892, 53, 611412102, 71, 1093166982, 34712220807, 64, 39, 66, 75, 48, 41, 14344611027, 925198482, 48, 8664482727, 75, 78, 42, 674656677, 51, 13529798802],
    [5173839777, 66, 9479218392, 48, 75, 40, 9714104487, 8694038982, 75, 26357102757, 64, 37, 73, 42, 51, 4436939907, 69, 78, 39, 48, 26125289337, 75, 66, 5454721977, 25856012757, 78, 18876479682, 8641737942, 73, 41, 68, 50, 77, 40, 408183432, 49, 410333877, 5491557972, 77, 40, 18540954567, 67, 17482217607, 22649401737, 68, 50, 77, 39],
    [8729617602, 66, 22399780497, 14076176547, 77, 39, 21864023697, 48, 5220157137, 5107779237, 37, 73, 44, 53, 80, 71, 41, 321226677, 2217042792, 71, 80, 68, 41, 321226677, 327513267, 80, 41, 321226677, 327513267, 8675420052, 73, 41, 4899309192, 321226677, 65, 74, 51, 42, 69, 78, 73, 46, 37, 8909125797, 5989681017, 37, 64, 39],
    [5989681017, 10267885992, 593593752, 78, 39, 66, 10569865317, 64, 48, 75, 46, 10275018852, 37, 26122666692, 607217112, 13293868152, 48, 9513091497, 66, 9513091497, 75, 70, 43, 10275199137, 52, 31745659347, 31683925122, 69, 78, 53, 629557122, 44, 80, 41, 26357352297, 2204443752, 34446128322, 78, 76, 53, 629557122, 44, 71, 41, 77, 50, 14327906757, 19412297652],
    [18824394852, 2237798292, 42, 69, 78, 73, 46, 588678552, 37, 64, 39, 48, 66, 75, 41, 13254361797, 25822594242, 26125300857, 10267885992, 5973031107, 78, 39, 26374001112, 8730669477, 69, 78, 52, 43, 70, 79, 64, 31446808722, 30406621302, 10251360357, 43, 8730924162, 70, 27162477762, 79, 18908074452, 78, 52, 43, 70, 79, 5980180692, 25856258457, 43],
    [8730924162, 70, 10795107942, 79, 76, 75, 77, 74, 51, 42, 69, 78, 73, 46, 4421210772, 37, 593593752, 64, 39, 48, 66, 75, 41, 13489366377, 25822594242, 12954199977, 4418929782, 78, 39, 66, 75, 48, 41, 9513027282, 26592244857, 26122340217, 26374013352, 69, 78, 53, 80, 44, 37, 10827678657, 34980586632, 44, 80, 41],
    [68, 26894043042, 2204443752, 34446128322, 78, 53, 44, 71, 39, 10267873752, 34986983832, 26357548482, 44, 71, 68, 41, 10251224937, 643330917, 2237798292, 42, 69, 78, 4347823302, 78, 39, 66, 10049767122, 64, 48, 75, 46, 14580479097, 37, 593590437, 26105690307, 75, 35014264482, 26374013352, 69, 78, 68, 41, 8730784197, 50, 77, 37, 27179169987, 22152311937],
    [22152233412, 78, 52, 8664790377, 43, 70, 79, 73, 46, 30121480917, 31725868242, 70, 31446811092, 79, 34947417762, 65, 74, 46, 73, 37, 64, 41, 8925841332, 50, 611412102, 68, 77, 39, 21844162677, 48, 66, 14327841477, 5107779237, 22078916232, 64, 39, 8675092377, 66, 9479218392, 48, 75, 40, 9714104487, 8694038982, 75, 78, 42, 389448822],
    [624325077, 37, 64, 42, 51, 4436939907, 69, 26660063097, 78, 17566152867, 51, 78, 69, 39, 4915947717, 4418929782, 69, 78, 66, 39, 8942478552, 4922243217, 26088736677, 64, 39, 4915947717, 66, 9479218392, 48, 75, 40, 8945666247, 8694038982, 75, 40, 13539498087, 13020456387, 64, 37, 73, 44, 71, 80, 53, 41, 50, 6547329912, 77],
    [19446977457, 327513267, 53, 80, 41, 50, 8644556502, 21600745107, 50, 8644556502, 8727651522, 34445812677, 8675420052, 73, 41, 50, 68, 77, 40, 8964552897, 4434716547, 68, 5689607832, 77, 80, 44, 8675420052, 341337987, 50, 5775718017, 68, 10571036817, 22078916232, 37, 73, 44, 71, 80, 53, 68, 41, 4890902727, 612721512, 53, 80, 41, 5746340037, 50],
    [8644556502, 8727651522, 34445812677, 8675420052, 73, 42, 51, 8678110932, 69, 1663137957, 78, 39, 48, 26175624312, 389448822, 25906344357, 8641737942, 74, 46, 73, 37, 64, 41, 50, 68, 77, 40, 21860999892, 49, 1483891842, 5474629827, 68, 9513027282, 77, 40, 1477730952, 21610391427, 8909064117, 64, 39, 8942479557, 66, 10049767122, 48, 75, 40, 5203330392, 67],
    [9747658887, 18087966822, 13505750232, 37, 64, 42, 51, 4436939907, 69, 26660063097, 78, 17566152867, 51, 69, 78, 39, 5240804472, 25838192502, 69, 78, 66, 39, 75, 48, 41, 13220931027, 27180153027, 48, 5142246582, 13020583797, 26088736677, 64, 39, 66, 9462441432, 48, 376653267, 75, 18087966822, 66, 75, 48, 69, 42, 4415980662, 8677388757, 48, 75],
    [40, 17767168167, 389310627, 13505750232, 73, 37, 64, 44, 71, 80, 53, 68, 41, 4890902727, 612721512, 53, 80, 41, 5746340037, 50, 675639732, 8928651462, 34445812677, 71, 2233562037, 53, 8980550577, 80, 30140348022, 64, 41, 50, 68, 77, 40, 21879879297, 49, 5758944852, 389382807, 68, 77, 71, 44, 80, 53, 39, 4907554737, 9513027282],
    [53, 5673870552, 34998661272, 21795735192, 50, 4937038017, 68, 9999320712, 77, 30703696017, 37, 64, 44, 71, 1730692002, 53, 80, 41, 50, 1480680072, 21600745107, 50, 675639732, 372602997, 34445812677, 354968712, 64, 42, 321291672, 51, 69, 78, 39, 26122340217, 26124449937, 69, 2267431842, 78, 39, 48, 10270822872, 13222570182, 66, 2267431842, 27650065812]]
  have close1 (L : LatinSquare 9) (side : ∀ r, L.mat r 0 = r)
      (known : ∀ row ∈ rect1, L.mat (row 0) = row) : ∃ σ, IsTransversal L σ :=
    run_sound 82 L (xs := stream1) (ys := []) (initial_valid rect1 L side known)
      (show run 82 (initial rect1) stream1 = some [] by decide +kernel)

  let rect2 : List (Fin 9 → Fin 9) := [![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![2, 0, 1, 5, 3, 4, 8, 6, 7],
    ![3, 4, 5, 6, 7, 8, 0, 1, 2],
    ![6, 7, 8, 1, 2, 0, 5, 3, 4]]
  let stream2 : List Nat := List.flatten [
    [38, 65, 47, 74, 42, 69, 51, 78, 46, 37, 594036582, 10284528777, 78, 44, 1630041492, 80, 34479690597, 34433282502, 51, 78, 44, 10268202882, 71, 2217087912, 53, 2222076342, 28002365592, 78, 75, 66, 9513095637, 39, 48, 41, 10251239877, 50, 9517957527, 13444188057, 657867222, 69, 51, 10285516692, 78, 43, 1629980052, 52, 1969371282, 2015773602],
    [51, 78, 43, 52, 10542404052, 70, 79, 39, 66, 14529545682, 26594477142, 27735034002, 10542404052, 70, 2015773602, 79, 12975216537, 78, 43, 25839473577, 52, 1969371282, 2015773602, 74, 42, 69, 51, 78, 44, 25845445062, 53, 8716178277, 25845445062, 78, 73, 37, 46, 8942683272, 10285512852, 46, 8675296197, 64, 40, 17800726452, 4385440452, 51, 78, 44],
    [8647087302, 71, 53, 25845445062, 36039569862, 53, 25857001362, 80, 17320522182, 78, 44, 53, 28003284162, 71, 80, 4352137107, 36039569862, 71, 2204256102, 53, 8731906452, 80, 75, 76, 77, 69, 51, 78, 43, 1747399782, 70, 1931875542, 1478914452, 78, 73, 37, 46, 64, 41, 605381592, 26088933237, 354841557, 10284532872, 51, 78, 43, 10268137602, 70],
    [1931875542, 31744611282, 78, 76, 43, 17237677782, 52, 1969371282, 17237677782, 47, 74, 42, 51, 561415572, 69, 78, 68, 77, 14294325447, 41, 50, 43, 21516280962, 26357552232, 50, 10040128617, 78, 13539629157, 51, 69, 78, 43, 560432532, 52, 25844405202, 79, 14847985362, 78, 43, 25839490002, 52, 678839202, 1701984402, 69, 78, 68, 77, 22146335172],
    [41, 676753812, 50, 10057954962, 78, 43, 1701984402, 25839489492, 74, 42, 78, 51, 69, 44, 53, 71, 80, 32214766437, 28003284162, 53, 612766632, 71, 34964132232, 80, 30693934692, 69, 44, 53, 28003284162, 8665838022, 71, 2204256102, 68, 53, 1451378562, 35821467282, 51, 69, 44, 560493972, 8680649922, 69, 68, 50, 1450326117, 41, 77, 43],
    [628496532, 1730688402, 26357367237, 78, 51, 69, 43, 8663815122, 70, 1931875542, 31509722217, 69, 43, 52, 79, 39, 48, 26326631622, 30135182802, 26326631622, 52, 678839202, 30138323922, 51, 69, 43, 26374264962, 8663814612, 69, 68, 50, 8713023897, 41, 77, 43, 26374264962, 27146078082, 26357367237, 65, 47, 74, 52, 43, 70, 79, 41, 645216357, 53],
    [71, 36306237042, 2233939122, 80, 14797858002, 36322821732, 79, 41, 30669091257, 53, 71, 80, 34446194322, 44, 42, 50, 676737432, 30103994772, 71, 80, 611857842, 44, 10804942722, 2255635812, 70, 79, 37, 46, 4352804517, 10520388822, 46, 1904371092, 64, 73, 40, 30652258407, 4381246407, 79, 75, 66, 9503266002, 39, 645088722, 48, 37, 12954203862, 30117291222, 43],
    [70, 79, 40, 678703542, 10519609767, 79, 40, 678703542, 51, 10542404052, 78, 25911513492, 12987959202, 70, 79, 37, 46, 73, 8916067542, 64, 32296289892, 73, 42, 30400731252, 8942679177, 46, 627521637, 326264997, 79, 75, 66, 9503266002, 39, 645088722, 48, 37, 46, 326264997, 13506738327, 46, 30138246612, 326264997, 74, 37, 46, 73, 64, 42],
    [69, 9463793862, 51, 4385305737, 78, 30099801492, 69, 78, 51, 41, 8645601177, 26088933237, 51, 8645601177, 26124257172, 64, 73, 42, 8675297172, 69, 2267428242, 51, 358777992, 78, 17768155062, 73, 42, 8675297172, 69, 78, 51, 68, 41, 4905580737, 50, 21548331897, 22079890392, 51, 78, 41, 8925833412, 392528757, 78, 41, 8925833412, 68, 10051008657, 27246346692],
    [64, 73, 46, 43, 52, 4352796057, 70, 10034299092, 79, 27718078932, 8641799382, 46, 73, 43, 52, 79, 70, 40, 8942553012, 6224636067, 70, 79, 66, 48, 30688691922, 4399268517, 30385661142, 52, 4337395092, 70, 79, 66, 48, 30425494707, 39, 8925706407, 13288030887, 79, 17808044217, 73, 43, 52, 4352796057, 70, 5169510102, 30385661142, 52, 79],
    [70, 41, 4436866707, 50, 4334248917, 6244427862, 70, 79, 66, 48, 4399256277, 39, 8925706407, 13288030887, 79, 41, 30467765427, 611673042, 46, 64, 73, 40, 76, 49, 67, 39, 5503148712, 66, 9462446247, 14076249522, 67, 39, 8644952487, 48, 8699271012, 17568913527, 4916020872, 73, 40, 8908998312, 8675165127, 64, 73, 40, 49, 8914208967, 67, 5454726087],
    [76, 26979955617, 49, 76, 67, 41, 8913225927, 390431367, 67, 19446980742, 76, 41, 4433736567, 17818808457, 47, 74, 46, 73, 37, 64, 43, 588743862, 52, 8867243412, 70, 30956078802, 79, 13239351447, 64, 40, 49, 4370626182, 67, 5452760712, 17800726452, 49, 76, 67, 53, 71, 5205152472, 44, 80, 39, 13539498087, 19378017912, 80, 13191116967],
    [67, 10553136852, 76, 14092952232, 37, 64, 42, 51, 4385305737, 69, 9462749097, 78, 13287966627, 622229652, 64, 40, 8908998087, 49, 4370621892, 67, 76, 41, 17316537282, 1176864642, 76, 14092952232, 37, 64, 73, 42, 4381377477, 51, 358777992, 69, 10285516692, 78, 17835636822, 73, 42, 51, 4385305737, 69, 9999312777, 78, 13540671702, 8942679177, 64, 73],
    [43, 52, 70, 79, 40, 17232397767, 6226740657, 70, 10285516692, 79, 23423103417, 4347880857, 73, 43, 8909194917, 52, 377963892, 70, 79, 41, 5687634117, 68, 1361535957, 5687634117, 79, 14849951442, 74, 73, 37, 46, 64, 42, 8675296197, 622229652, 64, 42, 69, 10000294872, 51, 5975855832, 78, 40, 26425440342, 26174845857, 8675292117, 46, 64, 40],
    [588548022, 8942552712, 64, 40, 49, 4887677127, 67, 18926891937, 17534321607, 49, 76, 67, 41, 4886694087, 50, 21795727257, 4432619427, 67, 76, 41, 4904597697, 9765744777, 76, 35553108102, 46, 37, 64, 43, 52, 70, 79, 40, 8865998982, 76, 17505986727, 26175026262, 70, 9469778007, 30385661142, 52, 4337395092, 70, 79, 66, 48, 30425494707, 39, 30670018647],
    [13288030887, 79, 17315608182, 64, 40, 17800726452, 76, 49, 67, 41, 8728699842, 50, 17487136692, 17571001017, 67, 41, 17733875412, 68, 22062130392, 22666111107, 37, 64, 42, 69, 1696691157, 51, 406210467, 78, 40, 4882466472, 5989759107, 8675292117, 64, 43, 8641807767, 52, 10556032722, 70, 79, 41, 4899301572, 77, 23488251492, 21793761477, 79, 17534321607, 47, 65],
    [74, 46, 73, 37, 64, 43, 588743862, 8909187237, 64, 39, 66, 5184321237, 48, 8945431737, 75, 40, 13438838697, 67, 10519406757, 5503145907, 66, 10519406757, 48, 4404238197, 13488978087, 37, 64, 42, 8942683272, 622229652, 64, 39, 8925705657, 4381177557, 73, 37, 64, 43, 52, 70, 79, 39, 48, 10561275492, 13261357737, 30402635862, 70, 31476167097],
    [79, 39, 48, 30437032617, 372736677, 4369638102, 52, 377963892, 70, 10520396982, 30383703717, 64, 41, 68, 10603546212, 50, 77, 40, 22113716052, 4434719607, 77, 40, 22028777172, 67, 5419206087, 17767171752, 68, 5704411017, 50, 8930748612, 22078908612, 37, 64, 42, 51, 69, 78, 41, 5777798337, 50, 609313752, 4332095397, 69, 10285512852, 26122286217, 51, 394674822, 69],
    [9982535877, 78, 17835636822, 64, 41, 4364527497, 8909056197, 74, 46, 73, 37, 64, 43, 52, 594634917, 70, 31476167097, 79, 27717032052, 52, 30425494707, 70, 30956078802, 79, 39, 5184321237, 30166712997, 64, 39, 4899173817, 66, 9462446247, 48, 4404238197, 75, 41, 9982534872, 50, 4337137047, 5704411017, 37, 64, 42, 51, 78, 69, 41, 8909055192],
    [1663402392, 69, 9463793862, 78, 31726786707, 51, 562460052, 69, 9715452102, 78, 39, 8925706407, 4385371347, 64, 39, 66, 9949119687, 48, 4918899897, 13237384917, 4381177557, 64, 37, 73, 43, 52, 594634917, 70, 31476167097, 79, 39, 48, 344090502, 6244295337, 66, 6509716932, 10034299092, 8641799382, 73, 41, 4364527497, 9999313092, 37, 73, 42, 8675297172, 51, 4337333652],
    [69, 78, 68, 41, 77, 50, 39, 26592249717, 5134252197, 342194292, 78, 17834596482, 73, 41, 68, 50, 77, 40, 22116598212, 49, 5691680967, 5674918872, 77, 40, 5670992007, 67, 9714108072, 18624821442, 5704411017, 65, 74, 52, 43, 70, 79, 73, 46, 37, 8916075702, 4364400342, 37, 8647706277, 4436866707, 79, 39, 66, 75, 10539264162],
    [64, 48, 75, 46, 10561275492, 37, 30400731252, 8647706277, 13261357737, 48, 9529935522, 66, 15116408007, 12988142802, 70, 79, 53, 1988243877, 44, 71, 31457436777, 80, 19193280162, 71, 9470767542, 34429417122, 79, 53, 44, 71, 80, 6249658017, 30151292562, 44, 71, 10292839362, 80, 76, 75, 77, 10553411172, 43, 70, 79, 73, 46, 37, 64],
    [39, 874608807, 10536315042, 64, 39, 66, 10855076277, 48, 75, 40, 4381246407, 9513035877, 8930748612, 37, 321356982, 64, 39, 4336214997, 10536315042, 79, 39, 30685742802, 48, 9529935522, 66, 15116408007, 9529935522, 70, 79, 51, 2019701862, 42, 8731906452, 25839489492, 79, 76, 51, 627521637, 42, 8731906452, 10519724457, 74, 52, 43, 70, 79, 73, 46],
    [30693934692, 37, 6241540212, 326272407, 79, 39, 66, 9999423687, 326272407, 30668974242, 70, 79, 68, 41, 8731834002, 50, 77, 37, 1411474392, 8647706007, 77, 25839489492, 79, 53, 8682681957, 44, 71, 35742823602, 80, 26357552232, 645416292, 43, 70, 79, 73, 46, 4335306132, 8641807767, 79, 39, 66, 75, 48, 41, 9462683847, 30903993522, 354646167, 30668974242],
    [70, 79, 51, 2019701862, 42, 628496532, 25839489492, 79, 51, 42, 69, 39, 48, 31747871577, 8660674002, 25861235922, 30669166722, 42, 628496532, 69, 31446808722, 65, 74, 46, 73, 37, 64, 41, 50, 68, 77, 40, 21861008007, 8712905682, 68, 9412379847, 22062131397, 8909055192, 64, 39, 8658319062, 8942482617, 37, 64, 43, 52, 79, 70],
    [39, 946946727, 48, 931218807, 8712847767, 70, 1931569317, 79, 39, 66, 6509716932, 4906510422, 52, 4337395092, 70, 6224512677, 30385669302, 64, 39, 4899173817, 66, 9462446247, 48, 8715981207, 75, 18104739942, 64, 37, 73, 42, 8675297172, 69, 27984549762, 51, 8711984082, 25855886277, 73, 41, 50, 68, 77, 40, 8914208967, 4434719607, 68, 77, 40, 21865072257],
    [5740198017, 22062131397, 50, 5742162057, 68, 9999313092, 22079890392, 37, 73, 42, 8675297172, 4381373577, 73, 43, 52, 79, 70, 39, 8942482617, 6243444822, 70, 1931569317, 79, 25838429652, 8641799382, 74, 46, 73, 37, 64, 41, 605381592, 50, 4337267847, 68, 5706377412, 22078908612, 64, 39, 8925705657, 622033047, 37, 64, 43, 52, 70, 79, 39],
    [4915950777, 30133150422, 70, 1931569317, 79, 39, 4915950777, 66, 9469778007, 48, 5226120822, 6244295337, 52, 4337395092, 70, 6224512677, 30385669302, 64, 39, 66, 6224512677, 48, 75, 40, 17500767912, 406086312, 13239350457, 4915950777, 73, 37, 64, 42, 69, 10000294872, 51, 78, 41, 8909056197, 50, 591497142, 4332095397, 26122286217, 8675292117, 64, 41, 50, 68, 77],
    [40, 21846323337, 49, 406153107, 5421172392, 68, 9982535877, 77, 40, 21781046232, 21846325377, 50, 4886694087, 68, 10000294872, 22078908612, 37, 64, 42, 354845832, 8675292117, 64, 43, 8641807767, 52, 625051572, 70, 6224512677, 30117299877]]
  have close2 (L : LatinSquare 9) (side : ∀ r, L.mat r 0 = r)
      (known : ∀ row ∈ rect2, L.mat (row 0) = row) : ∃ σ, IsTransversal L σ :=
    run_sound 82 L (xs := stream2) (ys := []) (initial_valid rect2 L side known)
      (show run 82 (initial rect2) stream2 = some [] by decide +kernel)

  let rect3 : List (Fin 9 → Fin 9) := [![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![2, 3, 6, 5, 8, 1, 0, 4, 7],
    ![3, 4, 5, 8, 6, 7, 1, 2, 0],
    ![4, 5, 3, 6, 7, 8, 2, 0, 1]]
  let stream3 : List Nat := List.flatten [
    [51, 78, 60, 69, 52, 61, 70, 79, 49, 25891517907, 53, 30205359477, 26155955667, 61, 70, 79, 53, 31684040052, 62, 27783287922, 34483672182, 79, 53, 62, 71, 65, 10855204452, 71, 49, 36092007012, 35975025027, 62, 71, 50, 25892635497, 2270434167, 2255754612, 70, 645170532, 79, 10318218597, 69, 52, 61, 70, 79, 49, 25891517907],
    [53, 58, 30140674722, 1686590052, 70, 79, 49, 30170157987, 53, 27924714612, 79, 49, 76, 74, 58, 67, 47, 26852013432, 30134076807, 9764571042, 18798155892, 53, 62, 27921560952, 1749243762, 70, 61, 79, 53, 27657327732, 62, 1752438132, 71, 28034946162, 36339667317, 79, 53, 27657327732, 62, 1752438132, 71, 30971008467, 61, 79, 53, 1736659317, 71, 80],
    [50, 30171218307, 35975870322, 79, 10569876837, 60, 69, 52, 61, 79, 70, 49, 1984451172, 30170165622, 70, 79, 49, 67, 65, 58, 25908572802, 30736135842, 26851219572, 30170165622, 30434145747, 79, 61, 70, 53, 71, 80, 10318218597, 80, 65, 56, 32246154852, 47, 26312208777, 10477647522, 62, 31809818997, 71, 80, 50, 25893024357, 34466116242, 80, 50],
    [25893024357, 1971610212, 70, 53, 62, 80, 10744182117, 62, 31809818997, 36339668082, 61, 70, 53, 30174167922, 34483672182, 70, 65, 74, 47, 56, 46, 392463747, 30166713747, 31709168997, 10475635557, 69, 52, 61, 79, 70, 49, 30170157987, 25891799682, 70, 79, 49, 30170157987, 53, 62, 35974624632, 30203520642, 79, 49, 1732792932, 53, 35977778292, 79, 61],
    [70, 53, 31683859572, 62, 30205482102, 71, 32313135477, 36088009842, 70, 53, 31683859572, 62, 30205482102, 80, 50, 59, 25861194882, 34450387602, 59, 1365799797, 34450387602, 61, 70, 53, 71, 80, 49, 36343861587, 34464821622, 34483672182, 70, 65, 53, 80, 62, 74, 8699462022, 10475635557, 36339667317, 78, 60, 69, 53, 62, 25895834742, 80, 71, 50],
    [2253681282, 59, 68, 77, 52, 30155485587, 25892586627, 643073892, 68, 77, 64, 73, 6548633427, 5990008692, 643073892, 62, 71, 34903381092, 80, 52, 25911563382, 25911440757, 71, 80, 52, 2255704437, 32218633332, 80, 52, 34483815282, 61, 36088009077, 36245165172, 69, 53, 71, 62, 80, 50, 59, 68, 77, 31507907172, 23454843492, 59, 55, 1649706852, 68],
    [77, 52, 2238976887, 1702134402, 23723274882, 80, 50, 59, 77, 68, 48, 25856934597, 57, 1367827092, 34482827922, 25862550162, 77, 23723274882, 59, 1367827092, 25862550162, 80, 62, 50, 1750364802, 68, 59, 77, 52, 21583069587, 1702134402, 21615817362, 59, 77, 55, 46, 21577101972, 35703252852, 25862550162, 71, 62, 80, 52, 32313185652, 32218633332, 80, 52, 61],
    [70, 47, 8713897062, 65, 10745091732, 26448450657, 61, 70, 50, 30171218307, 59, 1633175412, 2187805602, 70, 35265999522, 62, 80, 52, 25911563382, 25911440757, 80, 52, 34483815282, 61, 70, 50, 30171218307, 59, 1633175412, 34451109522, 36339667317, 60, 69, 53, 62, 80, 71, 50, 34450387602, 59, 36054528642, 34450387602, 61, 71, 80, 52, 30173902197, 79],
    [50, 59, 30138250707, 28008788082, 80, 30173902197, 80, 62, 71, 52, 34467943542, 34467820917, 36088009077, 62, 71, 52, 70, 31809869172, 30205625202, 61, 30138250707, 70, 30205625202, 31809818997, 71, 61, 52, 79, 50, 2270372277, 34466116242, 69, 53, 71, 80, 62, 50, 1750364802, 68, 35802870402, 59, 1633186677, 77, 52, 30157190802, 21598716777, 62, 80],
    [50, 59, 77, 68, 48, 27115422147, 57, 1367827092, 25825527657, 68, 77, 48, 2234991027, 35806184082, 27654240357, 77, 59, 68, 52, 27253813857, 61, 31474594227, 36093309042, 68, 52, 1484002167, 61, 35819630967, 36093309042, 21615817362, 80, 50, 34450387602, 1750365042, 80, 62, 71, 52, 36339717492, 36245165172, 71, 52, 34483815282, 61, 79, 50, 36344955522, 59],
    [2169987732, 25862304882, 34483815282, 62, 71, 52, 70, 30205625202, 70, 30205625202, 71, 52, 61, 32313185652, 61, 79, 50, 1733380227, 59, 23645856852, 25862304882, 32313135477, 60, 69, 78, 61, 52, 79, 70, 53, 30173902197, 62, 30138700707, 71, 80, 47, 30167892837, 1982039397, 36245345652, 79, 70, 46, 55, 73, 64, 561415077, 64, 6023251107],
    [55, 31692436947, 64, 73, 47, 26425393317, 26079670437, 73, 47, 5908035732, 4397954457, 65, 47, 74, 56, 70, 52, 31709234532, 30167762022, 52, 79, 53, 62, 80, 662918757, 31683859572, 74, 56, 70, 52, 31709234532, 27650446467, 52, 8698168422, 25810928997, 62, 53, 80, 52, 79, 31809819762, 70, 47, 32315290977, 10326594657, 79, 10603546242, 31809819762],
    [80, 47, 36090106977, 1747403682, 53, 80, 79, 31683859572, 30173902197, 80, 52, 35977778292, 34467820917, 78, 61, 52, 70, 79, 53, 1736659317, 62, 25844331987, 71, 32218813812, 80, 47, 36341634177, 10209416292, 70, 79, 46, 55, 73, 64, 50, 1633175412, 1733591652, 64, 73, 8692003797, 55, 25844789622, 64, 73, 47, 26040694932, 56, 8614478757],
    [73, 47, 4398085077, 4397954457, 74, 47, 65, 56, 79, 52, 70, 30367167957, 8698299237, 52, 70, 53, 30173902197, 62, 27783287922, 27924714612, 27657327732, 65, 56, 79, 52, 27682702692, 31676978307, 52, 70, 27924714612, 70, 46, 8692003797, 55, 30434166147, 5913465987, 56, 8730919302, 47, 65, 56, 52, 70, 30167892837, 27682702692, 70, 79, 46],
    [561415572, 1629714597, 10744173972, 56, 62, 25855882452, 65, 56, 70, 52, 79, 4397954457, 30167762022, 27682702692, 56, 53, 62, 71, 70, 10603546212, 8992998852, 10209408357, 69, 78, 59, 55, 46, 73, 64, 77, 23087031432, 50, 68, 48, 25856984937, 5993144517, 1633186677, 73, 64, 50, 5911356552, 68, 77, 47, 1445167512, 5908231302, 77, 47],
    [1361479572, 5908231302, 64, 46, 73, 50, 25792366452, 68, 22381101507, 5738361972, 73, 77, 50, 23087645832, 27113583732, 50, 25792366452, 68, 5469845667, 46, 73, 68, 50, 77, 47, 21494138772, 26077331652, 77, 8612382612, 50, 25792366452, 23087031432, 73, 68, 50, 21494138772, 77, 47, 25861567077, 27131332692, 27113583732, 62, 53, 80, 71, 77, 21584036802, 50],
    [68, 46, 2232706932, 27113583732, 25909490802, 80, 71, 50, 34465792962, 68, 77, 46, 55, 1633186677, 27137438292, 27114369417, 77, 46, 55, 1633186677, 64, 6258046677, 27113583732, 71, 53, 80, 77, 50, 1451520882, 21582988137, 50, 1750364802, 68, 22381101507, 80, 50, 1750364802, 68, 1180117092, 35708498802, 53, 80, 68, 50, 77, 32296415607, 77, 46],
    [55, 1633186677, 21500486292, 2232902292, 50, 1750364802, 21584036802, 80, 68, 50, 77, 47, 27114369417, 1696827282, 27119466597, 1451520882, 78, 59, 55, 46, 73, 64, 77, 50, 68, 47, 1361479572, 1697138532, 68, 559318932, 50, 1633175412, 27113563272, 25855276947, 64, 46, 25855276947, 73, 77, 50, 68, 47, 56, 10286022852, 25792377717, 23087051892, 46, 73],
    [68, 27113563272, 50, 77, 48, 5640451737, 27132457617, 25792377717, 73, 68, 50, 27114177672, 23087051892, 50, 77, 47, 1379430807, 5645820867, 25792377717, 62, 53, 71, 80, 68, 50, 77, 32296415607, 77, 46, 28002427992, 27113568147, 50, 1750364802, 21584036802, 25862550162, 80, 53, 71, 68, 50, 25909490802, 77, 52, 61, 1971594882, 1451520882, 25862550162, 53],
    [71, 77, 21584036802, 50, 68, 46, 64, 34712347332, 34901947572, 25856934597, 25909490802, 71, 77, 50, 25909490802, 23092934757, 50, 68, 46, 21616792692, 5645820867, 25909490802, 69, 78, 61, 52, 70, 79, 53, 71, 62, 49, 2017874562, 30169989507, 71, 62, 47, 10744173972, 35972920677, 79, 53, 1988367732, 62, 25911706482, 80, 47, 27919864932, 74],
    [56, 36272617122, 27682702692, 70, 79, 46, 55, 73, 64, 50, 77, 59, 27129312372, 4401427572, 64, 73, 10470439077, 55, 73, 64, 47, 645170532, 30603117702, 64, 73, 47, 26040694932, 371488212, 6023366787, 52, 70, 79, 47, 65, 10208248677, 56, 10208248677, 74, 53, 25895977842, 62, 8730919302, 2267240082, 74, 56, 8730919302, 65, 28034946162],
    [79, 47, 1982104932, 74, 56, 8730919302, 27682702692, 70, 79, 46, 31676978307, 55, 73, 64, 30608229732, 64, 5218068597, 73, 47, 25889571942, 56, 74, 50, 25792377492, 5911356552, 8982397062, 79, 74, 47, 25889571942, 56, 65, 46, 10202150022, 30603117477, 65, 46, 26308081812, 30084055977, 78, 61, 52, 70, 79, 53, 25895834742, 62, 71],
    [47, 35972928612, 1747403682, 71, 47, 35972928612, 56, 34400060772, 31709234532, 79, 53, 1988367732, 80, 62, 47, 31811916897, 27919856997, 79, 70, 46, 55, 73, 64, 30603098277, 64, 6023251107, 55, 73, 64, 65, 25788904857, 64, 26156025987, 73, 47, 5908035732, 4414915497, 52, 70, 79, 47, 65, 74, 5939426772, 56, 74, 6023296467, 74],
    [53, 1653031842, 2255704437, 65, 10475570532, 56, 10475570532, 1747403682, 79, 47, 1982104932, 65, 74, 36088009842, 26040890502, 70, 79, 65, 46, 64, 73, 74, 10201954452, 36088009842, 1729332627, 79, 46, 27650446467, 1729332627]]
  have close3 (L : LatinSquare 9) (side : ∀ r, L.mat r 0 = r)
      (known : ∀ row ∈ rect3, L.mat (row 0) = row) : ∃ σ, IsTransversal L σ :=
    run_sound 82 L (xs := stream3) (ys := []) (initial_valid rect3 L side known)
      (show run 82 (initial rect3) stream3 = some [] by decide +kernel)



  fin_cases k
  · exact close0 L side known
  · exact close1 L side known
  · exact close2 L side known
  · exact close3 L side known

/- Once the first two selected rows are normalized, five rows whose
pair differences consist of three 3-cycles force a transversal. The
remaining four rows need no additional assumptions. -/
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 60000 in
theorem closeFive (M : LatinSquare 9) (atRow : Fin 5 → Fin 9)
    (inj : Function.Injective atRow) (ra : atRow 0 = 0) (rb : atRow 1 = 1)
    (top : ∀ c, M.mat 0 c = c) (second : M.mat 1 = ![1,2,0,4,5,3,7,8,6])
    (relative :
      let p (i : Fin 5) : Equiv.Perm (Fin 9) := Equiv.ofBijective (M.mat (atRow i))
        ⟨M.row_injective _, Finite.surjective_of_injective (M.row_injective _)⟩
      ∀ i j, i ≠ j → ((p i)⁻¹ * p j)^3 = 1) : ∃ σ, IsTransversal M σ := by
  let cycles : Nat → List (Fin 9) → List (Fin 9 → Fin 9) := Nat.rec
    (fun _ => [id]) (fun _ next l => match l with
    | [] => []
    | x::xs => xs.flatMap fun y => (xs.erase y).flatMap fun z =>
        (next ((xs.erase y).erase z)).map fun q i =>
          if i = x then y else if i = y then z else if i = z then x else q i)

  have cycles_cover (f : (Fin 9 → Fin 9)) (fixed : ∀ i, f i ≠ i) (cube : ∀ i, f (f (f i)) = i)
      (n : Nat) (xs : List (Fin 9)) (hxs : xs.Nodup) (len : xs.length = 3*n)
      (closed : ∀ i ∈ xs, f i ∈ xs) :
      ∃ q ∈ cycles n xs, ∀ i ∈ xs, q i = f i := by
    induction n generalizing xs with
    | zero =>
      have : xs = [] := List.length_eq_zero_iff.mp (by simpa using len)
      subst xs
      exact ⟨id, by simp [cycles], by simp⟩
    | succ n ih =>
      cases xs with
      | nil => simp at len
      | cons x xs =>
        let y := f x
        let z := f y
        have yx : y ≠ x := fixed x
        have zy : z ≠ y := fixed y
        have zx : z ≠ x := by
          intro e
          have h := congrArg f e
          change f (f (f x)) = f x at h
          exact yx ((cube x).symm.trans h).symm
        have hz : f z = x := cube x
        have hy : y ∈ xs := (List.mem_cons.mp (closed x (by simp))).resolve_left yx
        have hzs : z ∈ xs := (List.mem_cons.mp (closed y (by simp [hy]))).resolve_left zx
        have nd := (List.nodup_cons.mp hxs).2
        have hz' : z ∈ xs.erase y := (List.Nodup.mem_erase_iff nd).mpr ⟨zy,hzs⟩
        let rest := (xs.erase y).erase z
        have restMem {i : (Fin 9)} : i ∈ rest ↔ i ≠ z ∧ i ≠ y ∧ i ∈ xs := by
          simp only [rest, List.Nodup.mem_erase_iff (nd.erase _), List.Nodup.mem_erase_iff nd]
        have restLen : rest.length = 3*n := by
          simp only [rest, List.length_erase_of_mem hz', List.length_erase_of_mem hy]
          simp only [List.length_cons] at len
          omega
        have fi : Function.Injective f := by
          intro i j e
          exact (cube i).symm.trans ((congrArg (fun k => f (f k)) e).trans (cube j))
        obtain ⟨q,hq,agree⟩ := ih rest ((nd.erase _).erase _) restLen (by
          intro i hi
          obtain ⟨iz,iy,ix⟩ := restMem.mp hi
          have ne : i ≠ x := fun e => (List.nodup_cons.mp hxs).1 (e ▸ ix)
          apply restMem.mpr
          exact ⟨fun e => iy (fi e), fun e => ne (fi e),
            (List.mem_cons.mp (closed i (List.mem_cons_of_mem _ ix))).resolve_left
              (fun e => iz (fi (e.trans hz.symm)))⟩)
        refine ⟨_,List.mem_flatMap.mpr ⟨y, hy, List.mem_flatMap.mpr ⟨z, hz',
          List.mem_map.mpr ⟨q,hq,rfl⟩⟩⟩, ?_⟩
        intro i hi
        by_cases hx : i = x
        · simp [hx,y]
        by_cases hy' : i = y
        · simp [hy',yx,z]
        by_cases hz'' : i = z
        · simp [hz'',zx,zy,hz]
        simp [hx,hy',hz'', agree _ (restMem.mpr ⟨hz'',hy',(List.mem_cons.mp hi).resolve_left hx⟩)]

  let decode (p : Nat) (i : (Fin 9)) : (Fin 9) := ⟨((p >>> (4*i.val)) &&& 15)%9, Nat.mod_lt _ (by decide)⟩
  let canonical : (Fin 9 → Fin 9) := ![1,2,0,4,5,3,7,8,6]
  let invCanonical : (Fin 9 → Fin 9) := ![2,0,1,5,3,4,8,6,7]
  let qualifies (p : (Fin 9 → Fin 9)) : Bool := (List.finRange 9).all fun i =>
    let f := fun x => invCanonical (p x)
    decide (p i ≠ canonical i ∧ f (f (f i)) = i)


  let codes : Array Nat := #[31814013186, 18127147266, 14571491586, 31195681026, 31482667266, 14365974786, 22689313026, 23140528386,
    18881937666, 30958584066, 31810671666, 31140107826, 17315551026, 1679251506, 31809803586, 31415539266,
    21615548226, 1702041666, 31813862226, 30874371666, 13023405906, 1665235026, 5776016226, 5241853026,
    5503153506, 4433598306, 23106945906, 14520702066, 18807489906, 1631803506, 30421681026, 30389851266,
    30400537986, 30337619586, 31813932291, 10070988291, 23123728131, 30690121731, 31809753411, 8867243331,
    4335367491, 561415491, 31172612451, 17851371891, 10268135811, 31811785476, 9536886276, 14537545476,
    30658353156, 31811895636, 4337394516, 560493396, 8866136916, 31449088356, 22152413556, 10291970436,
    31810855941, 9799169541, 18825316101, 30670022661, 31813804341, 562521141, 8865215541, 4336288821,
    30907859301, 13560209781, 10255102341, 31157932806, 31432320006, 30891214086, 30622832646, 1481056566,
    947016006, 1210282326, 675500406, 22601074806, 18069198966, 14295246966, 17585033991, 21883986951,
    13291906311, 8997000711, 23090176311, 14504055111, 18792808791, 10204959111, 18071225991, 14294324871,
    22599968391, 5975266056, 5997011976, 5960267016, 5943547656, 30153253176, 30121546056, 30134198616,
    30102737256, 14296352616, 22599047016, 18070120296]
  let inverses : Array Nat := #[28038217761, 27182788641, 22669590561, 19414868001, 23680401441, 26901577761, 26667860001, 18111356961,
    14351351841, 15106142241, 28038008916, 19364515926, 26377457751, 9784660056, 28036907061, 23663296566,
    26399031351, 10055925816, 28036112451, 15067344966, 26358415431, 9514082376, 26867998851, 27132063876,
    26594459781, 26326941831, 17574469731, 21864022116, 13273415781, 8979300456, 6516187251, 6529638516,
    6495289461, 6479495286, 28037153841, 26884769841, 17842898481, 10811148081, 28037940261, 22601074806,
    18071225991, 14296352616, 19347736101, 26109019941, 5489690661, 28037883201, 27148712001, 22132328001,
    10824476481, 28035794211, 22599968391, 18070120296, 14295246966, 23646455331, 26130532131, 5760895011,
    28034876241, 26609141841, 13539755601, 10788161361, 28035060516, 22599047016, 18069198966, 14294324871,
    15049520676, 26088933156, 5218068516, 19330966881, 23629808481, 15034840161, 10740909921, 26851218216,
    27115222056, 26576635176, 26041730856, 8867243331, 8865215541, 8866136916, 25840592241, 25862226801,
    25822594161, 25806850161, 17306030886, 21595522086, 13003932966, 4415899686, 4335367491, 4336288821,
    4337394516, 1194730881, 1466057601, 925197441, 657802881, 2221216551, 2234606631, 2199274791,
    2167752231, 561415491, 562521141, 560493396]
  let tickets : Array (List (Nat × Nat)) := #[
    [(4150, 7707644069229477546048), (3951, 9990428648369153951808), (4052, 8745273423360540330048), (4061, 7707086748775586023488), (5261, 9990124655394298333248), (4162, 9989871327915262429248), (5062, 8744969430385684711488), (3963, 8744716102906648807488), (5163, 7707340076254621927488), (3975, 9990428648369153951809), (4075, 4967380912418116982030), (4175, 6214379911245878626370), (5075, 9989506761470442214670), (5175, 9990124519296519194689), (5275, 9990124655394298333250), (6175, 2437409213061783904730), (6275, 2436487400325179826650), (6375, 8883049790836696745089), (3976, 9990428648369153951810), (4076, 8744351462244785607950), (4176, 9990428512271363016769), (5076, 8883607111290580157569), (5176, 2436851892589777412570), (5276, 2435930079871288304090), (6176, 6213822590773872134210), (6276, 9989871327915262429249), (6376, 3929751484021704627470), (3977, 2436183407350324208090), (4077, 8883353783811536143489), (4177, 2437105220053717508570), (5077, 6212536001310836495630), (5177, 6214075918237812230210), (5277, 9990124655394298333249), (6177, 9989871191817484027969), (6277, 9989871327915262429250), (6377, 7706722046266197447950), (3986, 4969224686270475782210), (4086, 8745273423360540330049), (4186, 3929751558271958390030), (5086, 8744969430385684711490), (5186, 8744351536461828592910), (5286, 8744969294336223955009), (6186, 9920679145000978416769), (6286, 2436851966806820397530), (6386, 2435929943788604973530), (7786, 6214075918237812230208), (3987, 8745273287311067777089), (4087, 8745273423360540330050), (4187, 7706722108113722823950), (5087, 2436183271267640877530), (5187, 9921236465454861829249), (5287, 2437105294270760493530), (6187, 6212536063143266063630), (6287, 4968667365798469290050), (6387, 8744716102906648807489), (7587, 6214379911245878626368), (3988, 2437409287278826889690), (4088, 2436487264242496496090), (4188, 9920983137975817815169), (5088, 8744969430385684711489), (5188, 4967380776335433651470), (5288, 4968920693262409386050), (6188, 9989506625405873853710), (6288, 8744715966857188788289), (6388, 8744716102906648807490), (7688, 6213822590773872134208), (3997, 6212536137393519826190), (4097, 3931595332124317190210), (4197, 7707644069229477546049), (5097, 7707339940208181069889), (5197, 7707340076254621927490), (5297, 7706722182330765808910), (6197, 2436183333100070445530), (6297, 7637894565894520898689), (6397, 2437105158206192132570), (7697, 3931595332124317190208), (8897, 4968920693262409386048), (3998, 9989506687253399229710), (4098, 7707643933183024891969), (4198, 7707644069229477546050), (5098, 2437409151214258528730), (5198, 2436487326074926064090), (5298, 7638451886348404311169), (6198, 7707086748775586023489), (6298, 4967380838167863219470), (6398, 3931038011652310698050), (7798, 3931038011652310698048), (8698, 4969224686270475782208), (3999, 7638198558869360297089), (4099, 2436851830742252036570), (4199, 2435930005621034541530), (5099, 3931291339116250794050), (5199, 7707340076254621927489), (5299, 3929751422189275059470), (6199, 7707086748775586023490), (6299, 8744351400397260231950), (6399, 7707086612729145903169), (7599, 3931291339116250794048), (8799, 4968667365798469290048)],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [(4150, 9990428648369153951811), (4166, 8708165953220860794891), (5066, 5345899994935430283591), (4176, 8559727661298812207451), (5076, 4907251660375518435590), (6676, 6511816841822235136131), (4179, 7491396987561277758471), (5079, 177343103283732715551), (6679, 9814864896038231874890), (7679, 9764794864123175343111), (4197, 2976628713545064800450), (5097, 3649042042317659521311), (6697, 5276352386656221811731), (7697, 5107305046688260818051), (7997, 6131316527419855323531)],
    [(3951, 8745273423360540330051), (3964, 7117134276880457620491), (5164, 9980644443469987774791), (3975, 9824982450926919899330), (5175, 1712133914578215321891), (6475, 8873467481047837463571), (3987, 4755086696094069965151), (5187, 2970343532601656040710), (6487, 9763055484814617579651), (7587, 6144934400834427520131), (3990, 6522942923691525791751), (5190, 2806004133787209604131), (6490, 5941048640559284756810), (7590, 3641006077469057483211), (8790, 5130050415604723733511)],
    [(4052, 7707644069229477546051), (4065, 545481700587137228811), (5265, 8597138637960024490311), (4068, 9912532147235656177671), (5268, 7094872130924747464731), (6568, 614551289275723028810), (4086, 6089516775966380154050), (5286, 8491312361666546843931), (6586, 9772746254656210752531), (6886, 1565747369176737088011), (4098, 535393989234083250531), (5298, 9749521979707095605510), (6598, 5128311036296165970051), (6898, 6513556221130792899591), (8698, 3862149821712874194051)],
    [],
    [(4451, 8709263705631106324491), (4463, 5346406649893513674951), (5163, 9990124655394298333251), (4475, 6513556357195352642691), (5175, 8561686727153902436571), (6375, 4908906733239650801990), (4480, 9814375129595935464650), (5180, 7489404144743404903431), (6380, 176549343816122931231), (7580, 9764963749126448712711), (4499, 5275879508695415016471), (5199, 2975716734618375053570), (6399, 3648569164357859328351), (7599, 5107558374185419801731), (8099, 6130218774977398030731)],
    [(4252, 7118232029290703150091), (4261, 9981151098428071166151), (5261, 8744969430385684711491), (4277, 8872994603087030668311), (5277, 9824070472000230152450), (6177, 1711661036618415128931), (4286, 9764795000187735086211), (5286, 4757045761949160194271), (6186, 2971998605465788407110), (7786, 6145187728331586503811), (4291, 5940558874116988346570), (5291, 6520950080873652936711), (6191, 2805210374319599819811), (7791, 3639908325026600190411), (8691, 5130219300607997103111)],
    [(4350, 546579452997382758411), (4362, 8597645292918107881671), (5062, 7707340076254621927491), (4369, 614061522833426618570), (5069, 9910539304417783322631), (6269, 7094078371457137680411), (4388, 9772273376695403957271), (5088, 6088604797039690407170), (6288, 8490839483706746650971), (6988, 1564649616734279795211), (4397, 5130050551669283476611), (5097, 537353055089173479651), (6297, 9751177052571227971910), (6997, 6513725106134066269191), (8897, 3862403149210033177731)],
    [],
    [(4055, 5345292008985743638791), (4061, 9989871327915262429251), (5561, 8708385503701621872651), (4077, 4907724538338539804870), (5577, 6513725242198626012291), (6177, 8560757859696401727771), (4078, 177680873237532416031), (5578, 9815759986446992416010), (6178, 7489792580176977173511), (7778, 9763055348750057836551), (4098, 3650224237221991743711), (5598, 5277534581558540783631), (6198, 2974956752182329499970), (7798, 5107001053746632197251), (7898, 6131096976922988364171)],
    [(4153, 9980036457520301129991), (4162, 8744716102906648807491), (5362, 7117353827361218698251), (4176, 1713316109482547544291), (5376, 8874649675950156435471), (6276, 9823310489564184598850), (4188, 2970816410564677409990), (5388, 9764963885191008455811), (6288, 4756116894491659485471), (7688, 6144630407892798899331), (4189, 2806341903741009304611), (5389, 5941943730968045297930), (6289, 6521338516307225206791), (7689, 3640786526972190523851), (8889, 5128310900231606226951)],
    [(3954, 8596530652010337845511), (3963, 7707086748775586023491), (5463, 545701251067898306571), (3967, 7095209900878547165211), (5467, 615446379684483569930), (6367, 9910927739851355592711), (3987, 8492494556570879066331), (5487, 9773928449558529724431), (6387, 6087844814603644853570), (6787, 1565527818679870128651), (3999, 9749994857670116974790), (5499, 5130219436672556846211), (6399, 536424187631672770851), (6799, 6511816705757675393031), (8799, 3861845828771245573251)],
    [(4147, 7602442168585558482951), (4162, 8883353783811536143491), (4762, 9773659021105835081931), (4176, 1796035967477502460431), (4776, 9833852075115353575491), (6276, 2695263663240840536330), (4188, 9616645919775864691010), (4788, 8596225879756808686611), (6288, 1434892300886479520031), (7688, 6214379911245878626371), (4195, 6382700835417429253131), (4795, 6493910551432271240390), (6295, 2390141752407800176671), (7695, 5337846506533823319051), (8895, 3916626358139312259591)],
    [(3951, 8883607111290580157571), (3958, 9773051035156131692811), (5158, 7601310639180254879751), (3975, 2693574813378429133130), (5175, 1795107100052210074131), (5875, 9832247667713810207811), (3987, 1435534063831232348511), (5187, 9617405902214057466050), (5887, 8596867642703574765591), (7587, 6214075918237812230211), (3993, 2391019954353390510111), (5193, 6384609235776577346571), (5893, 6494535425897748241670), (7593, 5337458071083008266251), (8793, 3917757887560721744391)],
    [(3652, 9772544380198056673611), (3661, 7601648409150160461831), (5261, 8883049790836696745091), (3677, 9834240510566168628291), (5277, 2694216576326403186890), (6177, 1794076901638522290711), (3686, 8597914729617005515791), (5286, 1436581150745669746911), (6186, 9615733940853469387010), (7786, 6213822590773872134211), (3694, 6495312296799110176070), (5294, 2391239504850257469471), (6194, 6382869720386217057291), (7794, 5335853663681464898571), (8694, 3917420117606922043911)],
    [],
    [(3948, 8294195071366913644551), (3963, 9920983137975817815171), (4863, 5277265153105846141131), (3973, 7697031350669235036171), (4873, 9468448033317806416070), (6373, 453233624668364363811), (3987, 9820369639558341476751), (4887, 6236736980739843805251), (6387, 5323924693761631770890), (7387, 9834240374501600496651), (3999, 2768292182428365135170), (4899, 5344987236732214479891), (6399, 4063553331389960601891), (7399, 5991885066431641026951), (8799, 4969224686270475782211)],
    [(4052, 9921236465454861829251), (4059, 5276657167156142752011), (5259, 8293063541961610041351), (4071, 454111826613954697251), (5271, 7698939751028383129611), (5971, 9469072907783283417350), (4086, 5322235843899220367690), (5286, 9819440772133049090451), (5986, 6235132573338300437571), (7186, 9833851939050785443851), (4098, 4064195094334713430371), (5298, 2769052164866557910210), (5998, 5345628999678980558871), (7198, 5993016595853050511751), (8698, 4968920693262409386051)],
    [(3750, 5276150512198067732811), (3762, 8293401311931515623431), (5062, 9920679145000978416771), (3772, 9469849778684645351750), (5072, 454331377110821656611), (6272, 7697200235638022840331), (3788, 6237125416190658858051), (5088, 5322877606847194421450), (6288, 9818410573719361307031), (7288, 9832247531649242076171), (3797, 5346676086592411309071), (5097, 4065242181249150828771), (6297, 2767380203505969831170), (7297, 5992678825899250811271), (8897, 4968667365798469290051)],
    [],
    [(4046, 477387270098198518791), (4061, 7638198558869360297091), (4661, 8874380247497461792971), (4077, 6503757857320193794370), (4677, 9979731685266771971091), (6177, 8352421328527502655771), (4084, 9841465349237970688011), (4684, 406485007108060485830), (6184, 7232412071756691692571), (7784, 1426315908188531163591), (4098, 6015728674321390911951), (4698, 5337458207147576397891), (6198, 9612792690916281867530), (7798, 3931595332124317190211), (8498, 6237125280126090726411)],
    [(4150, 7638451886348404311171), (4157, 8873772261547758403851), (5057, 476255740692894915591), (4176, 8353063091472255484251), (5076, 6504517839758386569410), (5776, 9980373448213538050071), (4182, 7233290273702282026011), (5082, 9843373749597118781451), (5782, 407109881573537487110), (7682, 1427447437609940648391), (4197, 9611103841053870464330), (5097, 6014799806896098525651), (5797, 5335853799746033030211), (7697, 3931291339116250794051), (8297, 6236736844675275673611)],
    [(3551, 8873265606589683384651), (3563, 476593510662800497671), (5163, 7637894565894520898691), (3575, 9981420535126968800271), (5175, 8354110178386692882651), (6375, 6502845878397798490370), (3583, 407886752474899421510), (5183, 7233509824199148985371), (6383, 9841634234206758492171), (7583, 1427109667656140947911), (3599, 5337846642598391450691), (5199, 9611745604001844518090), (6399, 6013769608482410742231), (7599, 3931038011652310698051), (8399, 6235132437273732305931)],
    [],
    [],
    [(5163, 8883353647746972207111), (5175, 7108647732095079192591), (6375, 9616645511582239955270), (5183, 9773659425176425399491), (6383, 5129080304091545583951), (7583, 5993017008169843820931), (5199, 2695264017833411797250), (6399, 4755336795097858626591), (7599, 6214379837028843749511), (8399, 3695263685943686414811)],
    [(5261, 9920983001911253878791), (5277, 5323925048354203031810), (6177, 535644088237871911971), (5286, 398644575300409138191), (6186, 2768291774234740399430), (7786, 4969224612053440905351), (5294, 5277265557176436458691), (6194, 6512586109617614750031), (7794, 3846561061305116295651), (8694, 1427447849926733957571)],
    [(5062, 7638198422804796360711), (5072, 8874380651568052110531), (6272, 9763824752609997193551), (5088, 9612793045508853128450), (6288, 8559977760302600868891), (7288, 1412479106822125207971), (5097, 6347719539037380059151), (6297, 6503757449126569058630), (7297, 3917758299877515053571), (8897, 3931595257907282313351)],
    [],
    [(5158, 9920679008936414480391), (4863, 7638451750283840374791), (5163, 9989506761415506888768), (5463, 8744969294321120773131), (5164, 9989871191850698490891), (5467, 9981151510744864475331), (6367, 9990428574152119074951), (4873, 8339138124549359943951), (6373, 8883049728989167681611), (5175, 9824982450926919899328), (5875, 5322877961439765682370), (6375, 8634880494654392703169), (6475, 2974956343988570562890), (5176, 8644102740471188576451), (6376, 4823971583355317699031), (5177, 9460627722558853745691), (6377, 1504418951128711496151), (5186, 8436526191758326143171), (6386, 259824349352840238111), (7786, 9667272101187353428251), (4887, 8561075512711839550491), (5187, 9617405902214057466048), (5487, 7454557968738992019471), (5887, 397597488386974194711), (6387, 6087844814603644853568), (6487, 6014327003151318963651), (6787, 9750924203349811252611), (7387, 7316531576389501311171), (7587, 8496546806678054885568), (5188, 9668204271271716178971), (6388, 6083215254857758563651), (7688, 7177353512938631107971), (5190, 7707340002037587050631), (6490, 107008369799914094871), (7590, 6088604574388451581190), (8790, 3717150120495794756631), (5193, 7638198497021831233611), (5893, 5276150916268658050371), (7593, 9612793090863766494470), (8793, 2694774370897505654211), (5197, 7385669716916777582991), (6397, 3579376981528107422751), (7697, 6430999958181995175951), (8897, 258621963292113731871), (5198, 7178093168203915149711), (6398, 2763662622634160463171), (7798, 2900898438634547765271), (8698, 4825934087884713774531), (4899, 6504517431564761833670), (5199, 540763546330204823809), (5499, 2971998931196238159170), (6399, 2768292182428365135168), (6799, 4907252076815606176010), (7399, 9615733755310815074570), (7599, 7390029262705183018369), (8799, 2616376900695504821568)],
    [(5259, 7637894429829956962311), (4661, 8883606975226016221191), (5261, 8744351536440104044608), (5561, 7707339940190057989131), (5265, 8744715966842084869131), (5268, 9990124581177263456391), (6568, 1698040046123074486551), (5271, 8883353721964007080011), (5971, 8873266010660273702211), (5275, 4826183976689443340751), (6175, 604839499659622061091), (5276, 1505719365538294612431), (6176, 6429953007281790558531), (4677, 9617405494020432730310), (5277, 8634272508670337964289), (5577, 9751177378301677723970), (6177, 6503757857320193794368), (5578, 8597645705234901190851), (6178, 8745273349143505453191), (7778, 2970343949041743781130), (4684, 1214083226044757197071), (6184, 9920679083153449353291), (7784, 2767380017963315518730), (5286, 6089516775966380154048), (5986, 9611745958594415779010), (6186, 5937044173874236824769), (6586, 9823310081370425661770), (6886, 2975716511967136227590), (7186, 2695264063188325163270), (7786, 4899718812720033828289), (5287, 6084617000241845001411), (6187, 1641908230640486629911), (7587, 8437083376198986848271), (5288, 260314115813394713631), (6188, 5170709335778350924311), (7688, 8642447531577723639831), (5297, 2764152389093704375491), (6197, 4133640604797486355491), (7697, 1643870735169882705411), (8897, 3579846556828841672991), (4698, 4756434547507097308191), (5298, 2769052164866557910208), (5598, 5932701582623594535951), (5998, 6346672452123945115671), (6198, 2974956752182329499968), (6598, 1794634296307430512131), (6898, 2817871346902521192471), (7198, 5323435401398969292291), (7798, 4069057996497984545088), (7898, 4908653883998906486211), (8498, 3719416482016004545731), (8698, 3723451777603560938688), (5299, 3580778726913204423711), (6199, 2901151902143926264131), (7599, 4132438218736759849251), (8799, 1504979710273010570691)],
    [(5057, 8883049654772132808711), (4762, 9921236329390297892871), (5062, 7706722182293945452608), (5362, 9990124519329734394891), (5066, 7707086612711022085131), (5075, 6430442773741334470851), (6275, 9460137956098299270171), (4776, 536741840647110593571), (5076, 6504517839758386569408), (5376, 467853650804319215631), (5776, 7107600645181644249111), (6276, 9823310489564184598848), (6676, 9818967968388269528451), (5077, 606241245044719062051), (6277, 8642700995087102138691), (5079, 8744969356168649834631), (6679, 8269692622399152095511), (7679, 7314265214869291522071), (5082, 9920983076128288751691), (5782, 9772544784268646991171), (7682, 9612303398537513801091), (5086, 1644120623974612271631), (6286, 9666802525886619178011), (7786, 9458935570037572763931), (5087, 5172009750187934040591), (6287, 8436036425298782230851), (7587, 7385419828112048016771), (4788, 2769051756672933174470), (5088, 5936436187890182085889), (5388, 4908907058970100554050), (6288, 9616645919775864691008), (7688, 8427101283912939870528), (5389, 5346407062210306984131), (6289, 7707643995012442669191), (7689, 2971745756260477275651), (8889, 9749522396147183345930), (4795, 522330323297887600911), (6295, 7637894504046991835211), (7695, 2820137708422730981571), (8895, 6502845692855144177930), (5097, 2976628713545064800448), (5797, 2694216930918974447810), (6297, 541371532314259562689), (6697, 6087844406409885916490), (7697, 2893348294287704826048), (7997, 9824070249348991326470), (8297, 5323925093709116397830), (8897, 2824460104444889107969), (5098, 2902553647528012701891), (6298, 7383457323582651941271), (7798, 5171270094922649998851), (8698, 2764709573534365080591), (5099, 4134130371258040831011), (6299, 7176792753794332033431), (7599, 605309074960356311331), (8799, 6082961791348380064791)],
    [(5261, 9990428512304590013451), (5277, 2976628305351305863370), (6177, 466198577941189255191), (5286, 6015424755560557645251), (6186, 4907251986105968187650), (7786, 5107304984840731754571), (5291, 6235344541278586126551), (6191, 5345900407252223592771), (7791, 1565528222750460446211), (8691, 3709831772529205199391)],
    [(5062, 8745273287295976391691), (5069, 5336065767686318719191), (6269, 9980644855786781083971), (5088, 9824982042733160962250), (6288, 7452902895875862059031), (6988, 6131097380993578681731), (5097, 1795732048716669193731), (6297, 2970343858332105792770), (6997, 3627169234855941947931), (8897, 6144934338986898456651)],
    [(5163, 7707643933164913607691), (5175, 9820065720797508210051), (6375, 9749522305437545357570), (5180, 9832459635654095896791), (6380, 8597139050276817799491), (7580, 4954986997506747417051), (5199, 6089516367772621216970), (6399, 5931046509760464575511), (7599, 3862149759865345130571), (8099, 3640786931042780841411)],
    [],
    [(6177, 7106958882234873976851), (6184, 9773051439226722010371), (7784, 5992679238216044120451), (6198, 2693575167971000394050), (7798, 6214075844020777353351), (8498, 3696361438353931944411)],
    [(6276, 5322236198491791628610), (6288, 396955725440203922451), (7688, 4968920619045374509191), (6295, 5276657571226733069571), (7695, 3848165468689416880611), (8895, 1427110079972934257091)],
    [(6373, 8873772665618348721411), (6387, 9611104195646441725250), (7387, 1413576859232370737571), (6399, 6346030689177174843411), (7399, 3917420529923715353091), (8799, 3931291264899215917191)],
    [],
    [(6269, 9989871253698227552391), (6272, 8883607049443051094091), (6275, 1503473195241323413971), (5776, 9615733532659844651270), (6276, 8633765853729438619969), (6676, 9749995183400566726850), (6277, 4824697788778051355091), (6679, 8596531064327131154691), (7679, 2971999021905876147530), (5782, 1213779233067762205011), (7682, 2768291996885710822730), (6286, 6083992125793413389571), (7786, 8434837205902015649811), (6287, 258929258929043640351), (7587, 8644659924911849281551), (6288, 6088604797039690407168), (6988, 2974956529531090673990), (7288, 2693575213325913760070), (7688, 4899060161274396938689), (5797, 4755556345579625861151), (6297, 2767380203505969831168), (6697, 5931519387721279757331), (6997, 2819830412741501362191), (7297, 5323621174900778454531), (7697, 4069260658481287520448), (7997, 4908282336995288945091), (8297, 3718487614558503836931), (8897, 3723097119132775488768), (6298, 3580153852462763479071), (7798, 4133333309162565779811), (8698, 1505469476733565046211), (6299, 2762767532208354532611), (7599, 1643245860719441760771), (8799, 3579069685893186847071)],
    [(5875, 535863638719639146531), (6375, 6502845878397798490368), (6475, 466671455902004437011), (6376, 605616370594278117411), (6377, 6429057916855984627971), (6380, 8744716028689613930631), (7580, 7316224280708271691791), (6383, 9921236403607332765771), (7583, 9612489172039322963331), (6386, 5169763579890962842131), (7786, 7384794953661607072131), (5887, 2767379795312345095430), (6387, 5935929532949282741569), (6487, 4907724864068989556930), (7587, 8427303945896242845888), (6388, 1642634436063220285971), (7688, 9459830660463378694491), (6490, 5345292421302536947971), (7590, 2971374209256859734531), (8790, 9751177469011315712330), (5893, 522026330320892608851), (7593, 2819208840965230272771), (8793, 6503757671777539481930), (6397, 2901928773079581090051), (7697, 5171759861383204474371), (8897, 2762463403237393882131), (6398, 4132745514373689757731), (7798, 604532204024701485411), (8698, 6085174184682505706511), (6399, 2975716734618375053568), (7599, 2892993635816919376128), (8099, 9823310266912945772870), (8399, 5322236243846704994630), (8799, 2823801452999252218369)],
    [(6568, 9980036869837094439171), (5971, 8338834131572364951891), (6175, 8643477866022756964611), (6176, 9459242865674502672411), (6177, 9824070472000230152448), (5986, 8560197310784368103451), (6186, 9615733940853469387008), (6586, 7453375773836677240851), (6886, 9750552656346193711491), (7186, 7315602708932000602371), (7786, 8496192148207269435648), (6187, 9667579396821275234331), (7587, 7177843279399185583491), (6188, 8435141334872976300291), (7688, 9666495230251698602331), (6191, 7707086674558551146631), (7791, 6087844591952406027590), (8691, 3719109186334774926351), (6194, 7638451824500875247691), (7794, 9611104241001355091270), (8694, 2694960144399314816451), (6197, 7175846997906943951251), (7697, 2903110831968673406991), (8897, 4825309213434272829891), (5998, 6502845470204173754630), (6198, 540256891389305479489), (6598, 2970816736295127162050), (6898, 4908907149679738542410), (7198, 9616645734233210378570), (7798, 7389370611259546128769), (8698, 2616579562678807796928), (6199, 7384183529005385597331), (7599, 6428753787885023977491), (8799, 259517053717919662431)],
    [(6276, 2975716326424616116490), (6288, 6014546553633086198211), (7688, 5107558312337890738251), (6289, 6235901861732477419791), (7689, 1565747773247327405571), (8889, 3708092257138844910111)],
    [(6367, 5336623088140210012431), (6387, 9824070063806471215370), (6787, 6131316931490445641091), (6399, 1794853846789197746691), (6799, 3626037705450638344731), (8799, 6145187666484057440331)],
    [(6177, 9819187518870036763011), (6178, 9833016956107987190031), (7778, 4953247482116387127771), (6198, 6088604388845931470090), (7798, 3862403087362504114251), (7898, 3641006481539647800771)],
    [],
    [(7682, 5991885478748434336131), (7697, 6213822516556837257351), (8297, 3695483236424447492571)],
    [(7587, 4968667291581434413191), (7593, 3846172625871544025571), (8793, 1426316320505324472771)],
    [(7186, 1412698657302886285731), (7198, 3916626770456105568771), (8698, 3931037937435275821191)],
    [],
    [(7778, 7315295413282979305491), (7784, 9610850987692046291331), (7786, 8425935977509487778048), (7587, 9460320426922922606811), (7688, 7384018082726951015811), (7791, 2970040017884430571011), (8691, 9749995274110204715210), (7794, 2818178642567640752451), (8694, 6504517654215732256970), (7697, 605933949408787923171), (8897, 6083687996771113720851), (7798, 2891929660405011816768), (7898, 9824982228275681073350), (8498, 5322878006794679048390), (8698, 2822484150108312933889), (7599, 5170375004498853401091), (8799, 2763409159124781964311)],
    [(7786, 7176458422514834510211), (7587, 9667896975635785040091), (6988, 9749218464973764547971), (7288, 7314572510534411082051), (7688, 8495128172795361876288), (7689, 6089516553315141328070), (8889, 3718180318909482540051), (7695, 9611746003949329145030), (8895, 2693321960052038144451), (6997, 4907724954778627545290), (7297, 9617405716671403153610), (7697, 7388053308368606844289), (8897, 2615211594292052729088), (7798, 6429699543772412059671), (8698, 260006820177463574751), (7599, 2901624644057281421331), (8799, 4824532342499616773571)],
    [(7580, 2970816827004765150410), (7583, 2769051979323903597770), (7786, 8643173737000457295891), (6787, 2976628490893825974470), (7387, 2694216976273887813830), (7587, 4897742858383457654209), (7688, 8435782961789403731991), (7697, 4133823075622109692131), (8897, 1504084619849213972931), (7798, 1642468989784785704451), (8698, 3580471431277273284831), (6799, 2818901545316208975891), (7399, 5321982990553501782531), (7599, 4067892690094532452608), (8099, 4906948145622859781571), (8399, 3717457416160914316611), (8799, 3722033143720867929408)],
    [(7587, 5107000991899103133771), (7590, 1564650020804870112771), (8790, 3707923372170057105951)],
    [(6886, 6130219179047988348291), (6898, 3626375475420543926811), (8698, 6144630346045269835851)],
    [(7679, 4953078597147599323611), (7697, 3861845766923716509771), (7997, 3639908729097190507971)],
    [(8799, 5107304910623696881671)],
    [(8698, 5107558238120855865351)],
    [(8897, 5107000917682068260871)],
    [],
    [(8698, 6214379775181314688011)],
    [(8897, 6214075782173248291851)],
    [(8799, 6213822454709308195851)],
    [],
    [(8790, 3862403013145469241351), (8793, 3931595196059753251851), (8099, 6144630271828234962951), (8399, 4968920557197845447691), (8799, 2437409287333802461248)],
    [(8889, 3862149685648310257671), (8895, 3931037875587746759691), (7997, 6145187592267022567431), (8297, 4969224550205911843851), (8897, 2436851966879910938688)],
    [(8691, 3861845692706681636871), (8694, 3931291203051686855691), (7898, 6144934264769863583751), (8498, 4968667229733905351691), (8698, 2437105294358946842688)],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    []]

  let pool (i : (Fin 100)) : (Fin 9 → Fin 9) := decode (codes[i.val]?.getD 0)
  let back (i : (Fin 100)) : (Fin 9 → Fin 9) := decode (inverses[i.val]?.getD 0)
  let allIndices := List.finRange 100

  have pool_checked : (cycles 3 (List.finRange 9)).all (fun q => !qualifies q ||
      allIndices.any (fun i => (List.finRange 9).all fun c => q c == pool i c)) = true := by
    decide +kernel

  have pool_cover (q : (Fin 9 → Fin 9)) (h0 : ∀ i, q i ≠ i) (h3 : ∀ i, q (q (q i)) = i)
      (hq : qualifies q = true) : ∃ i, q = pool i := by
    obtain ⟨f,hf,h⟩ := cycles_cover q h0 h3 3 (List.finRange 9) (List.nodup_finRange 9)
      (by decide) (fun _ _ => List.mem_finRange _)
    have eq : f = q := funext fun j => h j (List.mem_finRange _)
    subst f
    have a := List.all_eq_true.mp pool_checked q hf
    simp only [hq, Bool.not_true, Bool.false_or] at a
    obtain ⟨i,_,ok⟩ := List.any_eq_true.mp a
    exact ⟨i, funext fun c => beq_iff_eq.mp (List.all_eq_true.mp ok c (List.mem_finRange _))⟩

  let compatible (i j : (Fin 100)) : Bool := (List.finRange 9).all fun c =>
    let f := fun x => back i (pool j x)
    decide (pool i c ≠ pool j c ∧ f (f (f c)) = c)

  have inverse_pool : ∀ i : (Fin 100), ∀ c : (Fin 9), back i (pool i c) = c := by decide +kernel

  let representatives := (![[![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![2, 0, 1, 5, 3, 4, 8, 6, 7],
    ![3, 4, 5, 6, 7, 8, 0, 1, 2],
    ![4, 5, 3, 7, 8, 6, 1, 2, 0]],
      [![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![2, 0, 1, 5, 3, 4, 8, 6, 7],
    ![3, 4, 5, 6, 7, 8, 0, 1, 2],
    ![6, 7, 8, 0, 1, 2, 3, 4, 5]],
      [![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![2, 0, 1, 5, 3, 4, 8, 6, 7],
    ![3, 4, 5, 6, 7, 8, 0, 1, 2],
    ![6, 7, 8, 1, 2, 0, 5, 3, 4]],
      [![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![2, 3, 6, 5, 8, 1, 0, 4, 7],
    ![3, 4, 5, 8, 6, 7, 1, 2, 0],
    ![4, 5, 3, 6, 7, 8, 2, 0, 1]]] : Fin 4 → List (Fin 9 → Fin 9))

  let ticket (i j k : (Fin 100)) := (((tickets[i.val]?.getD []).lookup (j.val*100 + k.val)).getD 0)
  let repId (t : Nat) : Fin 4 := ⟨t%4, Nat.mod_lt _ (by decide)⟩
  let srcCol (t : Nat) := decode ((t >>> 2) &&& 68719476735)
  let dstSym (t : Nat) := decode (t >>> 38)
  let source (i j k : (Fin 100)) : List (Fin 9 → Fin 9) := [id,canonical,pool i,pool j,pool k]

  let verifyMap (i j k : (Fin 100)) : Bool :=
    let t := ticket i j k
    let u := srcCol t
    let v := dstSym t
    decide (((List.finRange 9).map u).Nodup ∧ ((List.finRange 9).map v).Nodup) &&
      (representatives (repId t)).all fun q =>
        (source i j k).any fun p => (List.finRange 9).all fun c => v (p (u c)) == q c

  have allMaps : ∀ i j : (Fin 100), i < j → compatible i j = true →
      ∀ k : (Fin 100), j < k → compatible i k = true → compatible j k = true → verifyMap i j k = true := by
    decide +kernel

  have transport (L : LatinSquare 9) (i j k : (Fin 100)) (ok : verifyMap i j k = true)
      (present : ∀ p ∈ source i j k, ∃ r, L.mat r = p) : ∃ σ, IsTransversal L σ := by
    let t := ticket i j k
    simp only [verifyMap, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨iu,iv⟩,forms⟩ := ok
    have inj {f : (Fin 9) → (Fin 9)} (h : ((List.finRange 9).map f).Nodup) : Function.Injective f :=
      fun x y eq => List.inj_on_of_nodup_map h (List.mem_finRange x) (List.mem_finRange y) eq
    let u := Equiv.ofBijective (srcCol t) ⟨inj iu, Finite.surjective_of_injective (inj iu)⟩
    let v := Equiv.ofBijective (dstSym t) ⟨inj iv, Finite.surjective_of_injective (inj iv)⟩
    let row := Equiv.ofBijective (fun i => v (L.mat i (u 0)))
      ⟨v.injective.comp (L.col_injective _), Finite.surjective_of_injective (v.injective.comp (L.col_injective _))⟩
    let M : LatinSquare 9 := {
      mat := fun i j => v (L.mat (row.symm i) (u j))
      row_injective := fun i => v.injective.comp ((L.row_injective _).comp u.injective)
      col_injective := fun j => v.injective.comp ((L.col_injective _).comp row.symm.injective) }
    have side : ∀ r, M.mat r 0 = r := row.apply_symm_apply
    have rowMatches (q) (hq : q ∈ representatives (repId t)) : M.mat (q 0) = q := by
      obtain ⟨p,hp,h⟩ := List.any_eq_true.mp (List.all_eq_true.mp forms _ hq)
      obtain ⟨r,hr⟩ := present _ hp
      have agreement (c : (Fin 9)) : v (p (u c)) = q c := beq_iff_eq.mp (List.all_eq_true.mp h c (List.mem_finRange _))
      have rid : row r = q 0 := by change v (L.mat r (u 0)) = q 0; rw [hr]; exact agreement 0
      funext c
      change v (L.mat (row.symm (q 0)) (u c)) = q c
      rw [← rid, row.symm_apply_apply, hr]
      exact agreement c
    have solved := closeRectangles (repId t) M side rowMatches
    obtain ⟨g,gc,gs⟩ := solved
    refine ⟨fun i => u (g (row i)), u.injective.comp (gc.comp row.injective), ?_⟩
    intro a b eq
    apply row.injective
    apply gs
    change v (L.mat (row.symm (row a)) _) = v (L.mat (row.symm (row b)) _)
    simpa using congrArg v eq


  let permRow (L : LatinSquare 9) (r : (Fin 9)) : Equiv.Perm (Fin 9) := Equiv.ofBijective (L.mat r)
    ⟨L.row_injective r, Finite.surjective_of_injective (L.row_injective r)⟩
  let p (i : Fin 5) := permRow M (atRow i)
  by_contra badM
  have diff (i j : Fin 5) (ne : i ≠ j) (c : (Fin 9)) : p i c ≠ p j c :=
    fun eq => ne (inj (M.col_injective c eq))
  have cube (i j : Fin 5) (ne : i ≠ j) (x : (Fin 9)) :
      let q := fun c => (p i).symm (p j c)
      q (q (q x)) = x := by
    have h := DFunLike.congr_fun (relative i j ne) x
    simpa only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
      Equiv.Perm.one_apply] using h
  have p0 : p 0 = 1 := by apply Equiv.ext; intro c; change M.mat (atRow 0) c = c; rw [ra,top]
  have p1 (c : (Fin 9)) : p 1 c = canonical c := by
    change M.mat (atRow 1) c = _
    rw [rb,second]
  have inv1 (c : (Fin 9)) : (p 1).symm c = invCanonical c := by
    apply (p 1).injective
    rw [(p 1).apply_symm_apply,p1]
    exact (show ∀ u : (Fin 9), canonical (invCanonical u) = u by decide) c |>.symm
  have index (j : Fin 5) (j0 : j ≠ 0) (j1 : j ≠ 1) : ∃ i, ⇑(p j) = pool i := by
    apply pool_cover
    · intro c
      simpa only [p0, Equiv.Perm.one_apply] using diff j 0 j0 c
    · intro c
      simpa only [p0, show (1 : Equiv.Perm (Fin 9)).symm = 1 from rfl, Equiv.Perm.one_apply] using cube 0 j j0.symm c
    · apply List.all_eq_true.mpr
      intro c _
      apply decide_eq_true
      exact ⟨by simpa only [← p1] using diff j 1 j1 c,
        by simpa only [inv1] using cube 1 j j1.symm c⟩
  obtain ⟨i,hi⟩ := index 2 (by decide) (by decide)
  obtain ⟨j,hj⟩ := index 3 (by decide) (by decide)
  obtain ⟨k,hk⟩ := index 4 (by decide) (by decide)
  have comp (a b : Fin 5) (ne : a ≠ b) (u v : (Fin 100))
      (hu : ⇑(p a) = pool u) (hv : ⇑(p b) = pool v) :
      compatible u v = true := by
    have back (z : (Fin 9)) : back u z = (p a).symm z := by
      rcases (p a).surjective z with ⟨x,rfl⟩
      rw [(p a).symm_apply_apply]
      exact (congrArg (back u) (congrFun hu x)).trans (inverse_pool u x)
    apply List.all_eq_true.mpr
    intro c _
    apply decide_eq_true
    simp only [back, ← hu, ← hv]
    exact ⟨diff a b ne c,cube a b ne c⟩
  have apart (a b : Fin 5) (ne : a ≠ b) (u v : (Fin 100))
      (hu : ⇑(p a) = pool u) (hv : ⇑(p b) = pool v) : u ≠ v := by
    rintro rfl
    exact diff a b ne 0 (congrFun (hu.trans hv.symm) 0)
  have dispatch (a b c : Fin 5) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
      (u v w : (Fin 100)) (hu : ⇑(p a) = pool u) (hv : ⇑(p b) = pool v)
      (hw : ⇑(p c) = pool w) (uv : u < v) (vw : v < w) : False := by
    apply badM
    apply transport M u v w (allMaps u v uv (comp a b ab u v hu hv)
      w vw (comp a c ac u w hu hw) (comp b c bc v w hv hw))
    intro f hf
    simp only [source,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0,funext top⟩
    · exact ⟨1,second⟩
    · exact ⟨atRow a,hu⟩
    · exact ⟨atRow b,hv⟩
    · exact ⟨atRow c,hw⟩
  have ij := apart 2 3 (by decide) i j hi hj
  have ik := apart 2 4 (by decide) i k hi hk
  have jk := apart 3 4 (by decide) j k hj hk
  rcases lt_or_gt_of_ne ij with a | a <;> rcases lt_or_gt_of_ne ik with b | b <;> rcases lt_or_gt_of_ne jk with c | c <;> first
    | exact dispatch 2 3 4 (by decide) (by decide) (by decide) i j k hi hj hk (by omega) (by omega)
    | exact dispatch 2 4 3 (by decide) (by decide) (by decide) i k j hi hk hj (by omega) (by omega)
    | exact dispatch 3 2 4 (by decide) (by decide) (by decide) j i k hj hi hk (by omega) (by omega)
    | exact dispatch 3 4 2 (by decide) (by decide) (by decide) j k i hj hk hi (by omega) (by omega)
    | exact dispatch 4 2 3 (by decide) (by decide) (by decide) k i j hk hi hj (by omega) (by omega)
    | exact dispatch 4 3 2 (by decide) (by decide) (by decide) k j i hk hj hi (by omega) (by omega)


/-- Put an ordered pair of rows into canonical form and transport a
transversal back. Column zero determines the new row labels. -/
theorem putPairFirst (L : LatinSquare 9) (p : Fin 9 → Equiv.Perm (Fin 9))
    (hp : ∀ r c, p r c = L.mat r c) (a b : Fin 9) (q : Equiv.Perm (Fin 9))
    (q0 : q 0 = 1) (conj : IsConj ((p a)⁻¹ * p b) q) :
    ∃ (M : LatinSquare 9) (row S e : Equiv.Perm (Fin 9)),
      row a = 0 ∧ row b = 1 ∧ (∀ j, M.mat 0 j = j) ∧ (∀ i, M.mat i 0 = i) ∧
      M.mat 1 = q ∧ (∀ i j, M.mat (row i) j = S (L.mat i (e.symm j))) ∧
      ((∃ σ, IsTransversal M σ) → ∃ σ, IsTransversal L σ) := by
  obtain ⟨e,he⟩ := isConj_iff.mp conj
  let S := (p a).symm.trans e
  let row := Equiv.ofBijective (fun i => S (L.mat i (e.symm 0)))
    ⟨S.injective.comp (L.col_injective _),
      Finite.surjective_of_injective (S.injective.comp (L.col_injective _))⟩
  let M : LatinSquare 9 := {
    mat := fun i j => S (L.mat (row.symm i) (e.symm j))
    row_injective := fun i => S.injective.comp ((L.row_injective _).comp e.symm.injective)
    col_injective := fun j => S.injective.comp ((L.col_injective _).comp row.symm.injective) }
  have image (i j) : M.mat (row i) j = S (L.mat i (e.symm j)) := by
    change S (L.mat (row.symm (row i)) _) = _
    rw [row.symm_apply_apply]
  have first (j : Fin 9) : S (L.mat a (e.symm j)) = j := by
    rw [← hp]
    change e ((p a).symm (p a (e.symm j))) = j
    simp
  have second (j : Fin 9) : S (L.mat b (e.symm j)) = q j := by
    rw [← hp]
    exact DFunLike.congr_fun he j
  have ra : row a = 0 := first 0
  have rb : row b = 1 := (second 0).trans q0
  refine ⟨M,row,S,e,ra,rb,?_,row.apply_symm_apply,?_,image,?_⟩
  · intro j
    rw [← ra,image,first]
  · funext j
    rw [← rb,image,second]
  · rintro ⟨g,cols,syms⟩
    refine ⟨fun i => e.symm (g (row i)),e.symm.injective.comp (cols.comp row.injective),?_⟩
    intro i j eq
    apply row.injective
    apply syms
    change M.mat (row i) (g (row i)) = M.mat (row j) (g (row j))
    rw [image,image]
    exact congrArg S eq

/-- An arbitrary order-nine square has a transversal if it contains
five rows with pairwise relative permutations of order three. -/
theorem fiveRowsTransversal (L : LatinSquare 9) (g : Fin 5 ↪ Fin 9)
    (relative :
      let p (i : Fin 5) : Equiv.Perm (Fin 9) := Equiv.ofBijective (L.mat (g i))
        ⟨L.row_injective _, Finite.surjective_of_injective (L.row_injective _)⟩
      ∀ i j, i ≠ j → ((p i)⁻¹ * p j)^3 = 1) : ∃ σ, IsTransversal L σ := by
  let p (r : Fin 9) : Equiv.Perm (Fin 9) := Equiv.ofBijective (L.mat r)
    ⟨L.row_injective _, Finite.surjective_of_injective (L.row_injective _)⟩
  let f := (p (g 0))⁻¹ * p (g 1)
  have fixed (j : Fin 9) : f j ≠ j := by
    intro h
    have eq := (p (g 0)).symm_apply_eq.mp h
    exact (by decide : (0 : Fin 5) ≠ 1) (g.injective (L.col_injective j eq.symm))
  have supp : f.support = Finset.univ :=
    Finset.eq_univ_of_forall fun j => Equiv.Perm.mem_support.mpr (fixed j)
  have size : f.cycleType.sum = 9 := by rw [f.sum_cycleType,supp]; simp
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have eq := Equiv.Perm.cycleType_of_pow_prime_eq_one (σ := f) (relative 0 1 (by decide))
  have card : f.cycleType.card = 3 := by
    have h : f.cycleType.card * 3 = 9 := calc
      _ = (Multiset.replicate f.cycleType.card (3 : Nat)).sum := by simp
      _ = f.cycleType.sum := congrArg Multiset.sum eq.symm
      _ = 9 := size
    omega
  let q : Equiv.Perm (Fin 9) := ⟨![1,2,0,4,5,3,7,8,6],![2,0,1,5,3,4,8,6,7],by decide,by decide⟩
  have qt : q.cycleType = Multiset.replicate 3 3 := by decide +kernel
  have conj : IsConj f q := Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [eq,card,qt])
  obtain ⟨M,row,S,e,ra,rb,top,_,second,image,back⟩ :=
    putPairFirst L p (fun _ _ => rfl) (g 0) (g 1) q (by decide) conj
  apply back
  apply closeFive M (fun i => row (g i)) (row.injective.comp g.injective) ra rb top second
  let pm (i : Fin 5) : Equiv.Perm (Fin 9) := Equiv.ofBijective (M.mat (row (g i)))
    ⟨M.row_injective _, Finite.surjective_of_injective (M.row_injective _)⟩
  change ∀ i j, i ≠ j → ((pm i)⁻¹ * pm j)^3 = 1
  have im (i) : pm i = S * p (g i) * e⁻¹ := Equiv.ext fun c => image (g i) c
  intro i j ne
  have rel : (pm i)⁻¹ * pm j = e * ((p (g i))⁻¹ * p (g j)) * e⁻¹ := by
    rw [im,im]
    group
  rw [rel,conj_pow,show ((p (g i))⁻¹ * p (g j))^3 = 1 from relative i j ne]
  simp

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 60000 in
theorem main : H1 → H2 → H3 → OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1.H2 := by
  let permRow (L : LatinSquare 9) (r : (Fin 9)) : Equiv.Perm (Fin 9) := Equiv.ofBijective (L.mat r)
    ⟨L.row_injective r, Finite.surjective_of_injective (L.row_injective r)⟩

  have five (s : (Fin 9) → ℤˣ) : ∃ g : Fin 5 ↪ (Fin 9), ∀ i j, s (g i) = s (g j) := by
    classical
    let A := Finset.univ.filter (fun i : (Fin 9) => s i = 1)
    let B := Finset.univ.filter (fun i : (Fin 9) => s i ≠ 1)
    have size : A.card + B.card = 9 := by simpa [A,B] using (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : (Fin 9) => s i = 1))
    have choose (X : Finset (Fin 9)) (h : 5 ≤ X.card) (const : ∀ x ∈ X, ∀ y ∈ X, s x = s y) :
        ∃ g : Fin 5 ↪ (Fin 9), ∀ i j, s (g i) = s (g j) := by
      obtain ⟨e⟩ : Nonempty (Fin 5 ↪ X) := Function.Embedding.nonempty_iff_card_le.mpr (by simpa using h)
      exact ⟨e.trans (Function.Embedding.subtype _), fun i j => const _ (e i).property _ (e j).property⟩
    by_cases h : 5 ≤ A.card
    · apply choose A h
      intro x hx y hy
      exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    · apply choose B (by omega)
      intro x hx y hy
      have sx := (Int.units_eq_one_or (s x)).resolve_left (Finset.mem_filter.mp hx).2
      have sy := (Int.units_eq_one_or (s y)).resolve_left (Finset.mem_filter.mp hy).2
      exact sx.trans sy.symm

  have normalize (h1 : H1) (h2 : H2) (h3 : H3) (L : LatinSquare 9)
      (bad : ¬ ∃ σ, IsTransversal L σ) (a b : (Fin 9)) (distinct : a ≠ b)
      (equalSign : Equiv.Perm.sign (permRow L a) = Equiv.Perm.sign (permRow L b)) :
      ((permRow L a)⁻¹ * permRow L b)^3 = 1 := by
    let p := permRow L
    change Equiv.Perm.sign (p a) = Equiv.Perm.sign (p b) at equalSign
    let rows : Fin 8 → Fin 9 → Fin 9 := ![![1, 2, 3, 4, 5, 6, 7, 8, 0],
      ![1, 2, 3, 4, 5, 6, 0, 8, 7],
      ![1, 2, 3, 4, 5, 0, 7, 8, 6],
      ![1, 2, 3, 4, 0, 6, 7, 8, 5],
      ![1, 2, 3, 4, 0, 6, 5, 8, 7],
      ![1, 2, 3, 0, 5, 6, 4, 8, 7],
      ![1, 2, 0, 4, 5, 3, 7, 8, 6],
      ![1, 2, 0, 4, 3, 6, 5, 8, 7]]
    let inv : Fin 8 → Fin 9 → Fin 9 := ![![8, 0, 1, 2, 3, 4, 5, 6, 7],
      ![6, 0, 1, 2, 3, 4, 5, 8, 7],
      ![5, 0, 1, 2, 3, 4, 8, 6, 7],
      ![4, 0, 1, 2, 3, 8, 5, 6, 7],
      ![4, 0, 1, 2, 3, 6, 5, 8, 7],
      ![3, 0, 1, 2, 6, 4, 5, 8, 7],
      ![2, 0, 1, 5, 3, 4, 8, 6, 7],
      ![2, 0, 1, 4, 3, 6, 5, 8, 7]]
    let kinds : Fin 8 → Multiset ℕ := ![({9} : Multiset ℕ), ({7, 2} : Multiset ℕ), ({6, 3} : Multiset ℕ), ({5, 4} : Multiset ℕ), ({5, 2, 2} : Multiset ℕ), ({4, 3, 2} : Multiset ℕ), ({3, 3, 3} : Multiset ℕ), ({3, 2, 2, 2} : Multiset ℕ)]
    let left : ∀ i j, inv i (rows i j)=j := by decide
    let right : ∀ i j, rows i (inv i j)=j := by decide
    let perms (i : Fin 8) : Equiv.Perm (Fin 9) := ⟨rows i, inv i, left i, right i⟩
    have ct : ∀ i, (perms i).cycleType = kinds i := by decide +kernel
    have partCheck : ∀ a b c d : Fin 10, a.val≠1 → b.val≠1 → c.val≠1 → d.val≠1 →
        a.val+b.val+c.val+d.val=9 →
        ∃ i, (([a.val,b.val,c.val,d.val].filter (· != 0) : List ℕ) : Multiset ℕ) = kinds i := by decide +kernel

    let f := (p a)⁻¹ * p b
    have even : Equiv.Perm.sign f = 1 := by simp [f,equalSign]
    have fixed (j : Fin 9) : f j ≠ j := by
      intro h
      change (p a).symm (p b j) = j at h
      have eq := (p a).symm_apply_eq.mp h
      exact distinct (L.col_injective j eq.symm)
    have supp : f.support = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro j
      exact Equiv.Perm.mem_support.mpr (fixed j)
    have total : f.cycleType.sum = 9 := by rw [f.sum_cycleType,supp]; simp
    obtain ⟨k,typeEq⟩ := OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1.fourSlots f.cycleType total (fun _ h =>
      Equiv.Perm.two_le_of_mem_cycleType h) kinds partCheck
    have conj : IsConj f (perms k) := Equiv.Perm.isConj_iff_cycleType_eq.mpr (typeEq.trans (ct k).symm)

    have good : k = 0 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by
      rw [Equiv.Perm.sign_of_cycleType, typeEq] at even
      fin_cases k <;> first | decide | exact absurd even (by decide)
    have q0 : perms k 0 = 1 := by fin_cases k <;> rfl
    obtain ⟨M,_,_,_,_,_,top,side,marked,_,back⟩ :=
      putPairFirst L p (fun _ _ => rfl) a b (perms k) q0 conj
    have badM : ¬ ∃ σ, IsTransversal M σ := fun ht => bad (back ht)
    have six : k = 6 := by
      rcases good with rfl | rfl | rfl | rfl
      · exact (badM (h1 M top side marked)).elim
      · exact (badM (h2 M top side marked)).elim
      · exact (badM (h3 M top side marked)).elim
      · rfl
    subst k
    change f^3 = 1
    rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType, typeEq]
    decide

  intro h1 h2 h3 L _ _ _ _ _
  by_contra bad
  obtain ⟨g,same⟩ := five fun i => Equiv.Perm.sign (permRow L i)
  apply bad
  apply fiveRowsTransversal L g
  change ∀ i j : Fin 5, i ≠ j → ((permRow L (g i))⁻¹ * permRow L (g j))^3 = 1
  intro i j ne
  exact normalize h1 h2 h3 L bad (g i) (g j) (g.injective.ne ne) (same i j)

end OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1_H2_R1
