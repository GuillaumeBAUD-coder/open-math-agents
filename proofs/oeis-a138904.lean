import OMAStatements.S_oeis_a138904
import Mathlib

/-!
# OEIS A138904: rotational symmetries of binary expansions

`a m` counts the rotations `r < L` fixing the list of binary digits of `m`, where `L` is its
length. We show that over the numbers with `n` binary digits, the values of `a` are exactly the
divisors of `n`.

* **Every value divides `n`.** The rotations fixing a list `l` of length `n`, read modulo `n`,
  form a subgroup of `ZMod n`; by Lagrange its order divides `n`. This holds for any list.
* **Every divisor occurs.** Write `n = p * d` and take the word of length `n` with a `1` exactly
  at the positions `i` with `p ∣ i + 1` (so the block `0 … 0 1` of length `p`, repeated `d`
  times). Its last digit is `1`, so it is the digit list of a number. A rotation by `r` fixes it
  iff `p ∣ r`, and there are exactly `d` such `r` below `n`.
-/

open OMA.S_oeis_a138904

namespace OMA.A138904

/-! ### Every value divides the length -/

/-- For any list, the number of rotations `r < length` fixing it divides its length. -/
lemma card_rotate_fixed_dvd (l : List ℕ) :
    ((Finset.range l.length).filter (fun r => l.rotate r = l)).card ∣ l.length := by
  rcases Nat.eq_zero_or_pos l.length with h0 | hpos
  · simp [h0]
  have : NeZero l.length := ⟨hpos.ne'⟩
  -- the stabiliser of `l`, as a subgroup of `ZMod n`
  let H : AddSubgroup (ZMod l.length) :=
    { carrier := {x | l.rotate x.val = l}
      zero_mem' := by simp
      add_mem' := by
        intro x y (hx : l.rotate x.val = l) (hy : l.rotate y.val = l)
        show l.rotate (x + y).val = l
        rw [ZMod.val_add, List.rotate_mod, ← List.rotate_rotate, hx, hy]
      neg_mem' := by
        intro x (hx : l.rotate x.val = l)
        show l.rotate (-x).val = l
        have h0 : (x.val + (-x).val) % l.length = 0 := by
          rw [← ZMod.val_add, add_neg_cancel, ZMod.val_zero]
        have h : l.rotate (x.val + (-x).val) = l := by
          rw [← List.rotate_mod, h0, List.rotate_zero]
        rwa [← List.rotate_rotate, hx] at h }
  -- the fixing rotations below `n` are the values of the elements of `H`
  have hset : (((Finset.range l.length).filter (fun r => l.rotate r = l) : Finset ℕ) : Set ℕ)
      = ZMod.val '' (H : Set (ZMod l.length)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_image,
      SetLike.mem_coe]
    constructor
    · rintro ⟨hr, hfix⟩
      refine ⟨(r : ZMod l.length), ?_, ZMod.val_natCast_of_lt hr⟩
      show l.rotate ((r : ZMod l.length)).val = l
      rwa [ZMod.val_natCast_of_lt hr]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ZMod.val_lt x, hx⟩
  have hcard : ((Finset.range l.length).filter (fun r => l.rotate r = l)).card = Nat.card H :=
    calc ((Finset.range l.length).filter (fun r => l.rotate r = l)).card
        = (((Finset.range l.length).filter (fun r => l.rotate r = l) : Finset ℕ) : Set ℕ).ncard :=
          (Set.ncard_coe_finset _).symm
      _ = (ZMod.val '' (H : Set (ZMod l.length))).ncard := by rw [hset]
      _ = (H : Set (ZMod l.length)).ncard :=
          Set.ncard_image_of_injective _ (ZMod.val_injective l.length)
      _ = Nat.card H := (Nat.card_coe_set_eq _).symm
  -- Lagrange
  have hdvd := AddSubgroup.card_addSubgroup_dvd_card H
  rwa [Nat.card_zmod, ← hcard] at hdvd

/-! ### Every divisor occurs -/

/-- The word of length `n` with a `1` exactly at the positions `i` with `p ∣ i + 1`. -/
def word (p n : ℕ) : List ℕ := (List.range n).map (fun i => if p ∣ i + 1 then 1 else 0)

lemma word_length (p n : ℕ) : (word p n).length = n := by simp [word]

lemma word_getElem (p n i : ℕ) (h : i < (word p n).length) :
    (word p n)[i] = if p ∣ i + 1 then 1 else 0 := by simp [word]

/-- The word is the list of binary digits of a number, because its last digit is `1`. -/
lemma digits_word {p n : ℕ} (hn : 0 < n) (hpn : p ∣ n) :
    Nat.digits 2 (Nat.ofDigits 2 (word p n)) = word p n := by
  apply Nat.digits_ofDigits 2 (by norm_num)
  · intro x hx
    simp only [word, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    split_ifs <;> norm_num
  · intro hne
    rw [List.getLast_eq_getElem, word_getElem, word_length, Nat.sub_add_cancel hn, if_pos hpn]
    norm_num

/-- Reducing modulo a multiple of `p` does not change divisibility of the successor by `p`. -/
lemma dvd_mod_succ_iff {p n : ℕ} (hpn : p ∣ n) (x : ℕ) : p ∣ x % n + 1 ↔ p ∣ x + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_mod_of_dvd _ hpn,
    ← Nat.add_mod]

/-- A rotation fixes the word exactly when it is a multiple of the block length `p`. -/
lemma rotate_word_iff {p n : ℕ} (hp : 0 < p) (hpn : p ∣ n) (hple : p ≤ n) (r : ℕ) :
    (word p n).rotate r = word p n ↔ p ∣ r := by
  constructor
  · -- compare the entries at position `p - 1`, where the word has a `1`
    intro h
    have hlt : p - 1 < ((word p n).rotate r).length := by
      rw [List.length_rotate, word_length]; omega
    have hlt' : p - 1 < (word p n).length := by rw [word_length]; omega
    have hentry : ((word p n).rotate r)[p - 1] = (word p n)[p - 1] := by simp only [h]
    have hpp : p ∣ p - 1 + 1 := by
      have e : p - 1 + 1 = p := by omega
      rw [e]
    rw [List.getElem_rotate, word_getElem, word_getElem, word_length, if_pos hpp] at hentry
    have h1 : p ∣ (p - 1 + r) % n + 1 := by
      by_contra hcon
      rw [if_neg hcon] at hentry
      omega
    rw [dvd_mod_succ_iff hpn] at h1
    have h2 : p - 1 + r + 1 = p + r := by omega
    rw [h2] at h1
    exact (Nat.dvd_add_right (dvd_refl p)).1 h1
  · -- all entries agree, since shifting a position by a multiple of `p` changes nothing
    intro h
    apply List.ext_getElem (by rw [List.length_rotate])
    intro k h1 h2
    have hiff : p ∣ k + r + 1 ↔ p ∣ k + 1 := by
      rw [show k + r + 1 = k + 1 + r by omega]
      exact (Nat.dvd_add_iff_left h).symm
    rw [List.getElem_rotate, word_getElem, word_getElem, word_length]
    simp only [dvd_mod_succ_iff hpn, hiff]

/-- There are exactly `d` multiples of `p` below `p * d`. -/
lemma card_multiples_range {p : ℕ} (hp : 0 < p) (d : ℕ) :
    ((Finset.range (p * d)).filter (fun r => p ∣ r)).card = d := by
  have himage : (Finset.range (p * d)).filter (fun r => p ∣ r)
      = (Finset.range d).image (fun j => p * j) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hr, j, rfl⟩
      exact ⟨j, lt_of_mul_lt_mul_left hr (Nat.zero_le p), rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(Nat.mul_lt_mul_left hp).2 hj, Dvd.intro j rfl⟩
  rw [himage, Finset.card_image_of_injective _ (fun x y h => Nat.eq_of_mul_eq_mul_left hp h),
    Finset.card_range]

/-- Every divisor `d` of `n ≥ 1` is the number of symmetries of some `n`-digit number. -/
lemma exists_of_dvd {n d : ℕ} (hn : 1 ≤ n) (hd : d ∣ n) :
    ∃ m : ℕ, (Nat.digits 2 m).length = n ∧ a m = d := by
  obtain ⟨p, rfl⟩ := hd
  have hp : 0 < p := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hpn : p ∣ d * p := Dvd.intro_left d rfl
  have hple : p ≤ d * p := Nat.le_mul_of_pos_left p hd0
  refine ⟨Nat.ofDigits 2 (word p (d * p)), ?_, ?_⟩
  · rw [digits_word hn hpn, word_length]
  · unfold a
    rw [digits_word hn hpn, word_length,
      Finset.filter_congr (fun r _ => rotate_word_iff hp hpn hple r), Nat.mul_comm d p,
      card_multiples_range hp d]

end OMA.A138904

open OMA.A138904 in
theorem OMA.solution : type_of% @OMA.S_oeis_a138904.main := by
  intro n hn
  ext s
  constructor
  · rintro ⟨m, hlen, rfl⟩
    show a m ∣ n
    rw [← hlen]
    exact card_rotate_fixed_dvd (Nat.digits 2 m)
  · intro (hs : s ∣ n)
    exact exists_of_dvd hn hs
