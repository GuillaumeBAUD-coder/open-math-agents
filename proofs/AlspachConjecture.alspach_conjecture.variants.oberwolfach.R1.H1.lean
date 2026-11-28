import OMAReductions.R_AlspachConjecture_alspach_conjecture_variants_oberwolfach_R1

-- Step AlspachConjecture.alspach_conjecture.variants.oberwolfach.R1.H1: hypothesis H1 of reduction
-- AlspachConjecture.alspach_conjecture.variants.oberwolfach.R1
-- Credit: @marcusbuffett
--
-- Walecki's theorem (1892): for odd n = 2m + 1 at least 3, K_n is the edge-disjoint union of m
-- Hamilton cycles. Label the vertices 0, ..., 2m - 1 (read mod 2m) and a point at infinity 2m.
-- The i-th factor joins two finite vertices whose sum mod 2m is 2i or 2i + 1, and joins infinity
-- to i and i + m; every edge gets exactly one colour. The factor is a Hamilton cycle: the rotated
-- zigzag infinity, i, i + 1, i - 1, i + 2, i - 2, ..., i + m, infinity labels it as C_n. All the
-- modular arithmetic is unfolded into linear cases closed by omega. Written for this step.

open SimpleGraph

namespace OMA.S_AlspachConjecture_alspach_conjecture_variants_oberwolfach_R1_H1

theorem cyc_iff (m : ℕ) (hm : 1 ≤ m) (j k : Fin (2 * m + 1)) :
    (cycleGraph (2 * m + 1)).Adj j k ↔
      (j.val + 1 = k.val ∨ k.val + 1 = j.val ∨ (j.val = 0 ∧ k.val = 2 * m) ∨
        (k.val = 0 ∧ j.val = 2 * m)) := by
  rw [cycleGraph_adj', Fin.sub_def, Fin.sub_def]
  simp only
  have hj := j.isLt
  have hk := k.isLt
  constructor
  · intro h
    rcases h with h | h
    · rcases Nat.lt_or_ge (2 * m + 1 - k.val + j.val) (2 * m + 1) with h' | h'
      · rw [Nat.mod_eq_of_lt h'] at h; omega
      · rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)] at h; omega
    · rcases Nat.lt_or_ge (2 * m + 1 - j.val + k.val) (2 * m + 1) with h' | h'
      · rw [Nat.mod_eq_of_lt h'] at h; omega
      · rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)] at h; omega
  · intro h
    rcases h with h | h | h | h
    · right; rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · left; rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · left; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · right; rw [Nat.mod_eq_of_lt (by omega)]; omega


/-- Walecki's zigzag `0, 1, -1, 2, -2, …, m` on `ℤ/2m`, written with values in `[0, 2m)`. -/
def zz (m j : ℕ) : ℕ :=
  if j % 2 = 0 then (if j = 0 then 0 else 2 * m - j / 2) else j / 2 + 1

/-- The `i`-th rotated Hamilton cycle, as a labelling of `Fin (2m+1)`: position `2m` is the
point at infinity, the others run along the zigzag shifted by `i`. -/
def pos (m i j : ℕ) : ℕ :=
  if j = 2 * m then 2 * m else (if zz m j + i < 2 * m then zz m j + i else zz m j + i - 2 * m)

/-- The colour of the edge `uv` of `K_{2m+1}`: `⌊((u + v) mod 2m)/2⌋` between finite points,
`v mod m` between infinity and `v`. -/
def key (m u v : ℕ) : ℕ :=
  if u = 2 * m then (if v < m then v else v - m)
  else if v = 2 * m then (if u < m then u else u - m)
  else (if u + v < 2 * m then u + v else u + v - 2 * m) / 2

/-- The `i`-th factor of Walecki's decomposition. -/
def W (m i : ℕ) : SimpleGraph (Fin (2 * m + 1)) where
  Adj u v := u.val ≠ v.val ∧ key m u.val v.val = i
  symm := ⟨by
    intro u v ⟨h, hk⟩
    have hu := u.isLt
    have hv := v.isLt
    refine ⟨Ne.symm h, ?_⟩
    unfold key at *
    split_ifs at * <;> omega⟩
  loopless := ⟨fun u h => h.1 rfl⟩

theorem key_lt (m u v : ℕ) (hm : 1 ≤ m) (hu : u < 2 * m + 1) (hv : v < 2 * m + 1)
    (huv : u ≠ v) : key m u v < m := by
  unfold key
  split_ifs <;> omega

theorem pos_lt (m i j : ℕ) (hm : 1 ≤ m) (hi : i < m) (hj : j < 2 * m + 1) :
    pos m i j < 2 * m + 1 := by
  unfold pos zz
  split_ifs <;> omega

theorem pos_inj (m i j k : ℕ) (hm : 1 ≤ m) (hi : i < m) (hj : j < 2 * m + 1)
    (hk : k < 2 * m + 1) (h : pos m i j = pos m i k) : j = k := by
  unfold pos zz at h
  split_ifs at h <;> omega

theorem zz_cases (m j : ℕ) :
    (j % 2 = 0 ∧ j = 0 ∧ zz m j = 0) ∨ (j % 2 = 0 ∧ j ≠ 0 ∧ zz m j = 2 * m - j / 2) ∨
      (j % 2 = 1 ∧ zz m j = j / 2 + 1) := by
  unfold zz; split_ifs <;> omega

theorem pos_cases (m i j : ℕ) :
    (j = 2 * m ∧ pos m i j = 2 * m) ∨
      (j ≠ 2 * m ∧ zz m j + i < 2 * m ∧ pos m i j = zz m j + i) ∨
      (j ≠ 2 * m ∧ 2 * m ≤ zz m j + i ∧ pos m i j = zz m j + i - 2 * m) := by
  unfold pos; split_ifs <;> omega

theorem key_cases (m u v : ℕ) :
    (u = 2 * m ∧ v < m ∧ key m u v = v) ∨ (u = 2 * m ∧ m ≤ v ∧ key m u v = v - m) ∨
      (u ≠ 2 * m ∧ v = 2 * m ∧ u < m ∧ key m u v = u) ∨
      (u ≠ 2 * m ∧ v = 2 * m ∧ m ≤ u ∧ key m u v = u - m) ∨
      (u ≠ 2 * m ∧ v ≠ 2 * m ∧ u + v < 2 * m ∧ key m u v = (u + v) / 2) ∨
      (u ≠ 2 * m ∧ v ≠ 2 * m ∧ 2 * m ≤ u + v ∧ key m u v = (u + v - 2 * m) / 2) := by
  unfold key; split_ifs <;> omega

set_option maxHeartbeats 4000000 in
theorem pos_adj (m i j k : ℕ) (hm : 1 ≤ m) (hi : i < m) (hj : j < 2 * m + 1)
    (hk : k < 2 * m + 1) :
    (pos m i j ≠ pos m i k ∧ key m (pos m i j) (pos m i k) = i) ↔
      (j + 1 = k ∨ k + 1 = j ∨ (j = 0 ∧ k = 2 * m) ∨ (k = 0 ∧ j = 2 * m)) := by
  have h1 := zz_cases m j
  have h2 := zz_cases m k
  have h3 := pos_cases m i j
  have h4 := pos_cases m i k
  have h5 := key_cases m (pos m i j) (pos m i k)
  generalize zz m j = a at *
  generalize zz m k = b at *
  generalize pos m i j = u at *
  generalize pos m i k = v at *
  generalize key m u v = w at *
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4 <;> omega


/-- Each factor `W m i` is a Hamilton cycle: Walecki's zigzag labels it as `C_{2m+1}`. -/
theorem W_iso (m i : ℕ) (hm : 1 ≤ m) (hi : i < m) :
    Nonempty (cycleGraph (2 * m + 1) ≃g W m i) := by
  let f : Fin (2 * m + 1) → Fin (2 * m + 1) := fun j => ⟨pos m i j.val, pos_lt m i j.val hm hi j.isLt⟩
  have hf : Function.Injective f := fun a b h =>
    Fin.ext (pos_inj m i a.val b.val hm hi a.isLt b.isLt (congrArg Fin.val h))
  refine ⟨⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), ?_⟩⟩
  intro a b
  show (pos m i a.val ≠ pos m i b.val ∧ key m (pos m i a.val) (pos m i b.val) = i) ↔ _
  rw [cyc_iff m hm]
  exact pos_adj m i a.val b.val hm hi a.isLt b.isLt


end OMA.S_AlspachConjecture_alspach_conjecture_variants_oberwolfach_R1_H1

open OMA.S_AlspachConjecture_alspach_conjecture_variants_oberwolfach_R1_H1 in
theorem OMA.solution :
    OMA.R_AlspachConjecture_alspach_conjecture_variants_oberwolfach_R1.H1 := by
  intro n hn h3
  obtain ⟨m, rfl⟩ := hn
  have hm : 1 ≤ m := by omega
  refine ⟨fun i => W m i.val, fun i => ?_, fun u v => ?_⟩
  · obtain ⟨e⟩ := W_iso m i.val hm (by have := i.isLt; omega)
    exact ⟨e.symm⟩
  · simp only [completeGraph, top_adj]
    constructor
    · intro huv
      have huv' : u.val ≠ v.val := Fin.val_ne_of_ne huv
      refine ⟨⟨key m u.val v.val, by
        have := key_lt m u.val v.val hm u.isLt v.isLt huv'; omega⟩, ⟨huv', rfl⟩, ?_⟩
      intro j hj
      exact Fin.ext hj.2.symm
    · rintro ⟨i, hi, -⟩ h
      exact hi.1 (congrArg Fin.val h)
