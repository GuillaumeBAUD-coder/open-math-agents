import OMAStatements.S_oeis_a001969
import Mathlib.Algebra.BigOperators.Fin

namespace OMA.S_oeis_a001969

private theorem width_le_of_lt {n w : ℕ} (hw : 0 < w) (hn : n < 2 ^ w) :
    width n ≤ w := by
  by_cases hz : n = 0
  · subst n
    exact hw
  · exact (Nat.log2_lt hz).2 hn

private theorem ones_eq_sum {n w : ℕ} (hw : 0 < w) (hn : n < 2 ^ w) :
    ones n = ∑ i : Fin w, (n.testBit i).toNat := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (n.testBit i).toNat)]
  apply Finset.sum_subset (Finset.range_mono (width_le_of_lt hw hn))
  intro i _ hi
  have hwi : width n ≤ i := Nat.le_of_not_gt (fun h => hi (Finset.mem_range.mpr h))
  have hp : 2 ^ width n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hwi
  rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self hp)]
  rfl

private def nextIndex {w : ℕ} (i : Fin w) : Fin w :=
  ⟨if i.val + 1 < w then i.val + 1 else 0, by have := i.isLt; split <;> omega⟩

private def prevIndex {w : ℕ} (i : Fin w) : Fin w :=
  ⟨if i.val = 0 then w - 1 else i.val - 1, by have := i.isLt; split <;> omega⟩

private def cycle (w : ℕ) : Equiv.Perm (Fin w) where
  toFun := nextIndex
  invFun := prevIndex
  left_inv i := by
    have hi := i.isLt
    apply Fin.ext
    simp only [nextIndex, prevIndex]
    split <;> split <;> omega
  right_inv i := by
    have hi := i.isLt
    apply Fin.ext
    simp only [nextIndex, prevIndex]
    split <;> split <;> omega

private theorem cycle_val {w : ℕ} (i : Fin w) :
    (cycle w i).val = (i.val + 1) % w := by
  have hi := i.isLt
  change (if i.val + 1 < w then i.val + 1 else 0) = _
  split
  · exact (Nat.mod_eq_of_lt (by omega)).symm
  · have he : i.val + 1 = w := by omega
    rw [he, Nat.mod_self]

private theorem right_bit {w : ℕ} (x : BitVec w) (i : Fin w) :
    (x.rotateRight 1).getLsbD i = x.getLsbD (cycle w i) := by
  have hi := i.isLt
  rw [BitVec.getLsbD_rotateRight]
  change _ = x.getLsbD (nextIndex i).val
  by_cases hw : w = 1
  · have h0 : i.val = 0 := by omega
    simp [nextIndex, hw, h0]
  · rw [Nat.mod_eq_of_lt (show 1 < w by omega)]
    by_cases h : i.val + 1 < w
    · have h' : i.val < w - 1 := by omega
      simp [nextIndex, h, h', Nat.add_comm]
    · have h' : ¬ i.val < w - 1 := by omega
      have h0 : i.val - (w - 1) = 0 := by omega
      simp [nextIndex, h, h', h0, hi]

private theorem left_bit {w : ℕ} (x : BitVec w) (i : Fin w) :
    (x.rotateLeft 1).getLsbD i = x.getLsbD ((cycle w).symm i) := by
  have hi := i.isLt
  rw [BitVec.getLsbD_rotateLeft]
  change _ = x.getLsbD (prevIndex i).val
  by_cases hw : w = 1
  · have h0 : i.val = 0 := by omega
    simp [prevIndex, hw, h0]
  · rw [Nat.mod_eq_of_lt (show 1 < w by omega)]
    by_cases h : i.val = 0
    · simp [prevIndex, h]
    · have h' : ¬ i.val < 1 := by omega
      simp [prevIndex, h, h', hi]

private def bitCount {w : ℕ} (x : BitVec w) : ℕ :=
  ∑ i : Fin w, (x.getLsbD i).toNat

private theorem count_right {w : ℕ} (x : BitVec w) : bitCount (x.rotateRight 1) = bitCount x := by
  unfold bitCount
  simp only [right_bit]
  exact Equiv.sum_comp (cycle w) (fun i : Fin w => (x.getLsbD i).toNat)

private theorem count_left {w : ℕ} (x : BitVec w) : bitCount (x.rotateLeft 1) = bitCount x := by
  unfold bitCount
  simp only [left_bit]
  exact Equiv.sum_comp (cycle w).symm (fun i : Fin w => (x.getLsbD i).toNat)

private theorem count_xor {w : ℕ} (x y : BitVec w) :
    bitCount (x ^^^ y) + 2 * (∑ i : Fin w, (x.getLsbD i && y.getLsbD i).toNat) =
      bitCount x + bitCount y := by
  unfold bitCount
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [BitVec.getLsbD_xor]
  cases x.getLsbD i <;> cases y.getLsbD i <;> decide

private theorem even_rotatedXor (x : ℕ) : Even (ones (rotatedXor x)) := by
  let word := BitVec.ofNat (width x) x
  let result := word.rotateRight 1 ^^^ word.rotateLeft 1
  change Even (ones result.toNat)
  rw [ones_eq_sum (show 0 < width x by exact Nat.succ_pos _) result.isLt]
  change Even (bitCount result)
  have h := count_xor (word.rotateRight 1) (word.rotateLeft 1)
  rw [count_right, count_left] at h
  change bitCount result + _ = _ at h
  rw [Nat.even_iff]
  omega

-- At odd width, doubling modulo the width visits each bit index once.
private def doubleIndex {w : ℕ} (i : Fin w) : Fin w :=
  ⟨(2 * i.val) % w, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

private theorem doubleIndex_injective {w : ℕ} (hw : w % 2 = 1) :
    Function.Injective (doubleIndex : Fin w → Fin w) := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  have he := congrArg Fin.val h
  change (2 * i.val) % w = (2 * j.val) % w at he
  have hmod (k : Fin w) : (2 * k.val) % w = if 2 * k.val < w then 2 * k.val else 2 * k.val - w := by
    have hk := k.isLt
    split
    · exact Nat.mod_eq_of_lt (by omega)
    · obtain ⟨t, ht⟩ : ∃ t, 2 * k.val = w + t ∧ t < w := ⟨2 * k.val - w, by omega⟩
      rw [ht.1, Nat.add_mod_left, Nat.mod_eq_of_lt ht.2]
      omega
  rw [hmod i, hmod j] at he
  apply Fin.ext
  split at he <;> split at he <;> omega

private noncomputable def doublePerm {w : ℕ} (hw : w % 2 = 1) : Equiv.Perm (Fin w) :=
  Equiv.ofBijective doubleIndex (Finite.injective_iff_bijective.mp (doubleIndex_injective hw))

private theorem double_cycle {w : ℕ} (hw : w % 2 = 1) (j : Fin w) :
    doublePerm hw (cycle w j) = cycle w (cycle w (doublePerm hw j)) := by
  apply Fin.ext
  simp only [cycle_val, doublePerm, Equiv.ofBijective_apply, doubleIndex,
    Nat.mul_mod_mod, Nat.mod_add_mod]
  congr 1

private def pack {w : ℕ} (f : Fin w → Bool) : BitVec w :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

private theorem pack_bit {w : ℕ} (f : Fin w → Bool) (i : Fin w) :
    (pack f).getLsbD i = f i := by
  have hi : i.val < (List.ofFn f).length := by simp
  simp only [pack, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.getElem_ofFn]

private theorem width_of_top_bit {w : ℕ} (hw : 0 < w) (x : BitVec w)
    (hx : x.getLsbD (w - 1) = true) : width x.toNat = w := by
  have ht := Nat.ge_two_pow_of_testBit hx
  have hnz : x.toNat ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) ht)
  have hl := (Nat.le_log2 hnz).2 ht
  have hu := width_le_of_lt hw x.isLt
  unfold width at *
  omega

-- The seed is true so the first position in the cycle can be the highest bit.
private def prefixParity (f : ℕ → Bool) (j : ℕ) : Bool :=
  decide ((∑ i ∈ Finset.range j, (f i).toNat) % 2 = 0)

private theorem prefix_step (f : ℕ → Bool) (j : ℕ) :
    (prefixParity f (j + 1) ^^ prefixParity f j) = f j := by
  unfold prefixParity
  rw [Finset.sum_range_succ]
  generalize (∑ i ∈ Finset.range j, (f i).toNat) = s
  cases f j
  · simp
  · by_cases h : s % 2 = 0
    · have h' : (s + 1) % 2 ≠ 0 := by omega
      simp [h, h']
    · have h' : (s + 1) % 2 = 0 := by omega
      simp [h, h']

private theorem exists_rotatedXor (n : ℕ) (hn : Even (ones n)) :
    ∃ x : ℕ, rotatedXor x = n := by
  let w := 2 * (width n / 2) + 1
  have hw : 0 < w := by dsimp [w]; omega
  have hodd : w % 2 = 1 := by dsimp [w]; omega
  have hnlt : n < 2 ^ w := by
    have hpow : 2 ^ width n ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by dsimp [w]; omega)
    exact Nat.lt_of_lt_of_le Nat.lt_log2_self hpow
  let d := doublePerm hodd
  let p := d.trans (cycle w).symm
  let f : ℕ → Bool := fun j => n.testBit ((2 * j) % w)
  let x : BitVec w := pack (fun i => prefixParity f (p.symm i).val)
  have hsum : (∑ j ∈ Finset.range w, (f j).toNat) = ones n := by
    rw [← Fin.sum_univ_eq_sum_range, ones_eq_sum hw hnlt]
    exact Equiv.sum_comp d (fun i : Fin w => (n.testBit i).toNat)
  have hclose : prefixParity f w = true := by
    simp [prefixParity, hsum, Nat.even_iff.mp hn]
  have hwrap (j : Fin w) : prefixParity f (cycle w j).val = prefixParity f (j.val + 1) := by
    have hj := j.isLt
    change prefixParity f (if j.val + 1 < w then j.val + 1 else 0) = _
    split
    · rfl
    · rw [show j.val + 1 = w by omega, hclose]
      simp [prefixParity]
  have hp (j : Fin w) : x.getLsbD (p j) = prefixParity f j.val := by
    simp only [x, pack_bit, Equiv.symm_apply_apply]
  let zero : Fin w := ⟨0, hw⟩
  have htop : (p zero).val = w - 1 := by
    change (if (2 * 0) % w = 0 then w - 1 else (2 * 0) % w - 1) = _
    simp
  have hx : width x.toNat = w := by
    apply width_of_top_bit hw
    rw [← htop, hp]
    simp [zero, prefixParity]
  have hbits : x.rotateRight 1 ^^^ x.rotateLeft 1 = BitVec.ofNat w n := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    let k : Fin w := ⟨i, hi⟩
    let j := d.symm k
    have hd : d j = k := d.apply_symm_apply k
    have hright : p (cycle w j) = cycle w k := by
      change (cycle w).symm (d (cycle w j)) = _
      rw [show d (cycle w j) = cycle w (cycle w (d j)) from double_cycle hodd j,
        Equiv.symm_apply_apply, hd]
    have hleft : p j = (cycle w).symm k := congrArg (cycle w).symm hd
    change (x.rotateRight 1 ^^^ x.rotateLeft 1).getLsbD k = (BitVec.ofNat w n).getLsbD k
    rw [BitVec.getLsbD_xor, right_bit, left_bit, ← hright, ← hleft, hp, hp,
      hwrap, prefix_step, BitVec.getLsbD_ofNat]
    have hfk : f j.val = n.testBit k.val := congrArg (fun i : Fin w => n.testBit i.val) hd
    simp only [hfk, k.isLt, decide_true, Bool.true_and]
  refine ⟨x.toNat, ?_⟩
  unfold rotatedXor
  rw [hx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  change (x.rotateRight 1 ^^^ x.rotateLeft 1).toNat = n
  rw [hbits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnlt]

end OMA.S_oeis_a001969

theorem OMA.solution : type_of% @OMA.S_oeis_a001969.main := by
  intro n
  constructor
  · exact OMA.S_oeis_a001969.exists_rotatedXor n
  · rintro ⟨x, rfl⟩
    exact OMA.S_oeis_a001969.even_rotatedXor x
