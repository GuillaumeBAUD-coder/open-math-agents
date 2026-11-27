import OMAStatements.S_oeis_a084043
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Order.Preorder.Finite

-- Credit: @yuka30240

open OMA.S_oeis_a084043

private def copies (ds : List ℕ) (k : ℕ) := (List.replicate k ds).flatten

private lemma copies_succ (ds : List ℕ) (k : ℕ) :
    copies ds (k + 1) = ds ++ copies ds k := by
  simp [copies, List.replicate_succ]

private lemma reverse_copies (ds : List ℕ) (k : ℕ) :
    (copies ds k).reverse = copies ds.reverse k := by
  simp [copies, List.reverse_flatten]

private lemma dvd_copies {n : ℕ} {ds : List ℕ} (h : n ∣ Nat.ofDigits 10 ds) (k : ℕ) :
    n ∣ Nat.ofDigits 10 (copies ds k) := by
  induction k with
  | zero => simp [copies]
  | succ k ih =>
    rw [copies_succ, Nat.ofDigits_append]
    exact dvd_add h (dvd_mul_of_dvd_right ih _)

-- Two repeated strings have the same residue. Removing the common low digits
-- leaves a nonempty run of blocks, shifted by a power of ten, divisible by n.
private lemma shifted_copies (n : ℕ) (hn : 0 < n) (ds : List ℕ) :
    ∃ k z : ℕ, n ∣ 10 ^ z * Nat.ofDigits 10 (copies ds (k + 1)) := by
  let residue (i : ℕ) : Fin n :=
    ⟨Nat.ofDigits 10 (copies ds i) % n, Nat.mod_lt _ hn⟩
  obtain ⟨i, j, hij, heq⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := residue) (fun _ => Set.mem_univ _)
  obtain ⟨k, hk⟩ : ∃ k, j = i + (k + 1) := ⟨j - i - 1, by omega⟩
  subst j
  have hc : copies ds (i + (k + 1)) = copies ds i ++ copies ds (k + 1) := by
    simp [copies, List.replicate_add]
  have hmod : Nat.ofDigits 10 (copies ds i) ≡
      Nat.ofDigits 10 (copies ds (i + (k + 1))) [MOD n] := congrArg Fin.val heq
  rw [hc, Nat.ofDigits_append] at hmod
  refine ⟨k, (copies ds i).length, (Nat.modEq_zero_iff_dvd).mp ?_⟩
  apply Nat.ModEq.add_left_cancel' (Nat.ofDigits 10 (copies ds i))
  simpa using hmod.symm

private lemma head_digit (m : ℕ) (h : Nat.digits 10 m ≠ []) :
    (Nat.digits 10 m).head h = m % 10 := by
  have hh := Nat.head!_digits (n := m) (b := 10) (by decide)
  generalize Nat.digits 10 m = ds at *
  cases ds with
  | nil => exact (h rfl).elim
  | cons d ds => exact hh

private lemma witness {n : ℕ} (hn : 0 < n) (h10 : ¬ 10 ∣ n) : ∃ m, admissible n m := by
  let ds := Nat.digits 10 n
  have hds : ds ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne'
  -- A second copy places the digits of n strictly inside the palindrome.
  let block := ds ++ ds
  obtain ⟨k, z, hshift⟩ := shifted_copies n hn block.reverse
  let half := copies block (k + 1)
  let zeros := List.replicate z 0
  -- The low half is a multiple of n. The zeros give the reflected half
  -- the shift obtained from the residue collision.
  let word := half ++ (zeros ++ half.reverse)
  have hhalf : half = ds ++ (ds ++ copies block k) := by
    simp [half, block, copies_succ, List.append_assoc]
  have hne : half ≠ [] := by simp [hhalf, hds]
  have hpal : word.reverse = word := by simp [word, zeros, List.append_assoc]
  have hhead : half.head hne ≠ 0 := by
    simpa [hhalf, List.head_append_of_ne_nil hds, ds, head_digit] using
      (Nat.dvd_iff_mod_eq_zero.not.mp h10)
  have hbase : ∀ d ∈ half, d < 10 := by
    intro d hd
    obtain ⟨l, hl, hd⟩ := List.mem_flatten.mp hd
    have hl' : l = block := List.eq_of_mem_replicate hl
    subst l
    exact Nat.digits_lt_base (by decide : 1 < 10) (by simpa [block] using hd)
  have hdigits : Nat.digits 10 (Nat.ofDigits 10 word) = word := by
    apply Nat.digits_ofDigits 10 (by decide)
    · intro d hd
      simp only [word, List.mem_append, zeros, List.mem_reverse] at hd
      rcases hd with hd | hz | hd
      · exact hbase d hd
      · have := List.eq_of_mem_replicate hz
        omega
      · exact hbase d hd
    · intro hw
      rw [List.getLast_eq_head_reverse]
      simpa [hpal, word, List.head_append_of_ne_nil hne] using hhead
  have hblock : n ∣ Nat.ofDigits 10 block := by
    simp only [block, ds, Nat.ofDigits_append, Nat.ofDigits_digits]
    exact dvd_add (dvd_refl _) (dvd_mul_left _ _)
  refine ⟨Nat.ofDigits 10 word, ?_, ?_, ?_⟩
  · by_contra! hz
    rw [show Nat.ofDigits 10 word = 0 by omega, Nat.digits_zero] at hdigits
    simp [word, hne] at hdigits
  · rw [show word = half ++ (zeros ++ half.reverse) from rfl, Nat.ofDigits_append,
        Nat.ofDigits_append]
    simp only [zeros, Nat.ofDigits_replicate_zero, List.length_replicate, zero_add]
    exact dvd_add (dvd_copies hblock _) (dvd_mul_of_dvd_right (by
      simpa only [half, reverse_copies] using hshift) _)
  · rw [hdigits]
    refine ⟨hpal, ds, copies block k ++ (zeros ++ half.reverse), hds, ?_, ?_⟩
    · simp [hne]
    · simp [word, hhalf, ds, List.append_assoc]

theorem OMA.solution : type_of% @OMA.S_oeis_a084043.main := by
  intro n hn
  classical
  unfold a
  split
  · rename_i h
    obtain ⟨hm, hdvd, hpal, _⟩ := Nat.find_spec h
    have hlast := Nat.getLast_digit_ne_zero 10 hm.ne'
    rw [List.getLast_eq_head_reverse] at hlast
    simp only [hpal, head_digit] at hlast
    exact iff_of_false hm.ne' (fun h10 => hlast (Nat.mod_eq_zero_of_dvd (h10.trans hdvd)))
  · rename_i h
    exact iff_of_true rfl (by by_contra h10; exact h (witness hn h10))
