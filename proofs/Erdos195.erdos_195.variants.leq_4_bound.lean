import FormalConjectures.ErdosProblems.«195»
import Mathlib.Order.OrderIsoNat

/-! Adenwalla's construction of a permutation of the integers with no monotone
five-term arithmetic progression (arXiv:2211.04451, Theorem 1). -/

namespace OMA

-- Shells use half-open boxes so Euclidean division by eight strips one digit.
private def box (i : ℕ) (z : ℤ) : Prop := -(8 : ℤ) ^ i ≤ z ∧ z < (8 : ℤ) ^ i

private instance (i : ℕ) (z : ℤ) : Decidable (box i z) := by
  unfold box
  infer_instance

private lemma exists_box (z : ℤ) : ∃ i, box i z := by
  have hn : z.natAbs < (8 : ℕ) ^ z.natAbs :=
    Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left (by decide) _)
  have hz : (z.natAbs : ℤ) < (8 : ℤ) ^ z.natAbs := by exact_mod_cast hn
  rw [Int.natCast_natAbs] at hz
  have h₁ := neg_abs_le z
  have h₂ := le_abs_self z
  exact ⟨z.natAbs, by unfold box; omega⟩

private def shell (z : ℤ) : ℕ := Nat.find (exists_box z)

private lemma box_shell (z : ℤ) : box (shell z) z := Nat.find_spec (exists_box z)

private lemma box_mono {i j : ℕ} {z : ℤ} (h : i ≤ j) (hz : box i z) : box j z := by
  have hp : (8 : ℤ) ^ i ≤ (8 : ℤ) ^ j := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide) h : (8 : ℕ) ^ i ≤ 8 ^ j)
  unfold box at *
  omega

private lemma shell_le_iff {i : ℕ} {z : ℤ} : shell z ≤ i ↔ box i z :=
  ⟨fun h => box_mono h (box_shell z), Nat.find_min' (exists_box z)⟩

private lemma shell_zero_iff {z : ℤ} : shell z = 0 ↔ z = 0 ∨ z = -1 := by
  rw [← Nat.le_zero, shell_le_iff]
  norm_num [box]
  omega

private lemma box_succ_iff (i : ℕ) (z : ℤ) : box (i + 1) z ↔ box i (z / 8) := by
  unfold box
  rw [pow_succ]
  omega

private lemma shell_div {n : ℕ} {z : ℤ} (hs : shell z = n + 2) :
    shell (z / 8) = n + 1 := by
  have h₁ : shell z ≤ (n + 1) + 1 := by omega
  have h₂ : ¬ shell z ≤ n + 1 := by omega
  rw [shell_le_iff, box_succ_iff, ← shell_le_iff] at h₁
  rw [shell_le_iff, box_succ_iff, ← shell_le_iff] at h₂
  omega

private def baseRank (z : ℤ) : ℕ :=
  ([-8, -4, 4, -6, 2, -2, 6, -7, 1, -3, 5, -5, 3, 7] : List ℤ).idxOf z

private def digit (i : ℕ) (r : ℤ) : ℕ :=
  let reversed := (4 * (r % 2) + 2 * (r / 2 % 2) + r / 4 % 2).toNat
  if i % 2 = 0 then 7 - reversed else reversed

private lemma digit_lt (i : ℕ) (r : ℤ) : digit i r < 8 := by
  unfold digit
  dsimp
  split <;> omega

private lemma digit_eq_of_parity {i j : ℕ} (h : i % 2 = j % 2) : digit i = digit j := by
  funext r
  simp [digit, h]

private def capacity (i : ℕ) : ℕ := 2 * 8 ^ i

private lemma capacity_pos (i : ℕ) : 0 < capacity i := by
  unfold capacity
  positivity

private lemma capacity_succ (i : ℕ) : capacity (i + 1) = 8 * capacity i := by
  simp only [capacity, pow_succ]
  omega

private lemma capacity_mono : Monotone capacity := by
  apply monotone_nat_of_le_succ
  intro i
  rw [capacity_succ]
  omega

private def rank : ℕ → ℤ → ℕ
  | 0, _ => 0
  | 1, z => baseRank z
  | n + 2, z => digit (n + 2) (z % 8) * capacity (n + 1) + rank (n + 1) (z / 8)

private lemma rank_lt_capacity (i : ℕ) (z : ℤ) : rank i z < capacity i := by
  induction i generalizing z with
  | zero =>
    change 0 < 2
    decide
  | succ i ih =>
    cases i with
    | zero =>
      have hl : baseRank z ≤ 14 := List.idxOf_le_length
      change baseRank z < 16
      omega
    | succ n =>
      have ht := ih (z / 8)
      have hd : digit (n + 2) (z % 8) + 1 ≤ 8 := digit_lt _ _
      have hmul := Nat.mul_le_mul_right (capacity (n + 1)) hd
      rw [Nat.add_mul, Nat.one_mul] at hmul
      rw [capacity_succ, rank]
      omega

private lemma digit_le_of_rank_le {n : ℕ} {a b : ℤ}
    (h : rank (n + 2) a ≤ rank (n + 2) b) :
    digit (n + 2) (a % 8) ≤ digit (n + 2) (b % 8) := by
  by_contra! hgt
  have hm := Nat.mul_le_mul_right (capacity (n + 1))
    (show digit (n + 2) (b % 8) + 1 ≤ digit (n + 2) (a % 8) by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  have hr := rank_lt_capacity (n + 1) (b / 8)
  rw [rank, rank] at h
  omega

private lemma split_rank_lt {n : ℕ} {a b : ℤ}
    (h : rank (n + 2) a < rank (n + 2) b) :
    digit (n + 2) (a % 8) < digit (n + 2) (b % 8) ∨
      (digit (n + 2) (a % 8) = digit (n + 2) (b % 8) ∧
      rank (n + 1) (a / 8) < rank (n + 1) (b / 8)) := by
  by_cases hlt : digit (n + 2) (a % 8) < digit (n + 2) (b % 8)
  · exact Or.inl hlt
  right
  have he := le_antisymm (digit_le_of_rank_le h.le) (le_of_not_gt hlt)
  exact ⟨he, by simpa only [rank, he, Nat.add_lt_add_iff_left] using h⟩

private lemma rank_eq_parts {n : ℕ} {a b : ℤ}
    (h : rank (n + 2) a = rank (n + 2) b) :
    digit (n + 2) (a % 8) = digit (n + 2) (b % 8) ∧
      rank (n + 1) (a / 8) = rank (n + 1) (b / 8) := by
  have he := le_antisymm (digit_le_of_rank_le h.le) (digit_le_of_rank_le h.ge)
  exact ⟨he, by simpa only [rank, he, Nat.add_left_cancel_iff] using h⟩

private def baseValue (a : Fin 16) : ℤ := (a.val : ℤ) - 8

private lemma as_base_value {a : ℤ} (ha : box 1 a) : ∃ u : Fin 16, baseValue u = a := by
  norm_num [box] at ha
  exact ⟨⟨(a + 8).toNat, by omega⟩, by unfold baseValue; dsimp; omega⟩

private def residueValue (a : Fin 8) : ℤ := a.val

private lemma as_residue_value (a : ℤ) : ∃ u : Fin 8, residueValue u = a % 8 :=
  ⟨⟨(a % 8).toNat, by omega⟩, by unfold residueValue; dsimp; omega⟩

private lemma residue_inj_finite : ∀ (p : Fin 2) (u v : Fin 8),
    digit p.val (residueValue u) = digit p.val (residueValue v) →
      residueValue u = residueValue v := by decide

private lemma residue_three_finite : ∀ (p : Fin 2) (u v : Fin 8),
    ¬ (digit p.val (residueValue u) < digit p.val (residueValue v) ∧
      digit p.val (residueValue v) <
        digit p.val ((2 * residueValue v - residueValue u) % 8)) := by decide

private lemma residue_four_finite : ∀ (p : Fin 2) (u v : Fin 8),
    ¬ (digit p.val (residueValue u) < digit p.val (residueValue v) ∧
      digit (p.val + 1) ((2 * residueValue v - residueValue u) % 8) <
        digit (p.val + 1) ((3 * residueValue v - 2 * residueValue u) % 8)) := by decide

private lemma base_inj_finite : ∀ (u v : Fin 16),
    ¬ box 0 (baseValue u) → ¬ box 0 (baseValue v) →
      baseRank (baseValue u) = baseRank (baseValue v) → baseValue u = baseValue v := by decide

private lemma base_three_finite : ∀ (u v : Fin 16),
    let a := baseValue u
    let b := baseValue v
    let c := 2 * b - a
    ¬ box 0 a → ¬ box 0 b → box 1 c → ¬ box 0 c →
      ¬ (baseRank a < baseRank b ∧ baseRank b < baseRank c) := by decide

private lemma base_four_finite : ∀ (u v : Fin 16),
    let a := baseValue u
    let b := baseValue v
    let c := 2 * b - a
    let d := 3 * b - 2 * a
    ¬ box 0 a → ¬ box 0 b → box 2 c → ¬ box 1 c → box 2 d → ¬ box 1 d →
      ¬ (rank 1 a < rank 1 b ∧ rank 2 c < rank 2 d) := by decide

private def prefixRank (z : ℤ) : ℕ := if z = 0 then 0 else baseRank z + 1

private lemma prefix_three_finite : ∀ (u v : Fin 16),
    baseValue u - 1 = 2 * baseValue v →
    ¬ prefixRank (baseValue u) < prefixRank (baseValue v) := by decide


private lemma digit_mod_inj {i : ℕ} {a b : ℤ}
    (h : digit i (a % 8) = digit i (b % 8)) : a % 8 = b % 8 := by
  obtain ⟨u, hu⟩ := as_residue_value a
  obtain ⟨v, hv⟩ := as_residue_value b
  let p : Fin 2 := ⟨i % 2, Nat.mod_lt _ (by decide)⟩
  have hp : digit p.val = digit i := digit_eq_of_parity (by dsimp [p]; omega)
  simpa only [hu, hv] using (residue_inj_finite p u v (by rwa [hp, hu, hv]))

private lemma no_digit_three {i : ℕ} {a b c : ℤ} (hap : a + c = 2 * b)
    (hab : digit i (a % 8) < digit i (b % 8))
    (hbc : digit i (b % 8) < digit i (c % 8)) : False := by
  obtain ⟨u, hu⟩ := as_residue_value a
  obtain ⟨v, hv⟩ := as_residue_value b
  let p : Fin 2 := ⟨i % 2, Nat.mod_lt _ (by decide)⟩
  have hp : digit p.val = digit i := digit_eq_of_parity (by dsimp [p]; omega)
  have hc : (2 * (b % 8) - a % 8) % 8 = c % 8 := by omega
  exact residue_three_finite p u v ⟨by rwa [hp, hu, hv], by rwa [hp, hu, hv, hc]⟩

private lemma no_digit_four {i : ℕ} {a b c d : ℤ}
    (hap₁ : a + c = 2 * b) (hap₂ : b + d = 2 * c)
    (hab : digit i (a % 8) < digit i (b % 8))
    (hcd : digit (i + 1) (c % 8) < digit (i + 1) (d % 8)) : False := by
  obtain ⟨u, hu⟩ := as_residue_value a
  obtain ⟨v, hv⟩ := as_residue_value b
  let p : Fin 2 := ⟨i % 2, Nat.mod_lt _ (by decide)⟩
  have hp : digit p.val = digit i := digit_eq_of_parity (by dsimp [p]; omega)
  have hp' : digit (p.val + 1) = digit (i + 1) :=
    digit_eq_of_parity (by dsimp [p]; omega)
  have hc : (2 * (b % 8) - a % 8) % 8 = c % 8 := by omega
  have hd : (3 * (b % 8) - 2 * (a % 8)) % 8 = d % 8 := by omega
  exact residue_four_finite p u v ⟨by rwa [hp, hu, hv], by rwa [hp', hu, hv, hc, hd]⟩

private lemma digit_lt_of_rank_lt {n : ℕ} {a b : ℤ}
    (h : rank (n + 2) a < rank (n + 2) b) (hres : a % 8 ≠ b % 8) :
    digit (n + 2) (a % 8) < digit (n + 2) (b % 8) :=
  (split_rank_lt h).resolve_right fun he => hres (digit_mod_inj he.1)

private lemma quotient_rank_lt {n : ℕ} {a b : ℤ}
    (h : rank (n + 2) a < rank (n + 2) b) (hres : a % 8 = b % 8) :
    rank (n + 1) (a / 8) < rank (n + 1) (b / 8) := by
  simpa only [rank, hres, Nat.add_lt_add_iff_left] using h

private lemma box_of_shell {i : ℕ} {z : ℤ} (h : shell z = i) : box i z :=
  h ▸ box_shell z

private lemma not_box_of_shell {i j : ℕ} {z : ℤ} (h : shell z = i) (hj : j < i) :
    ¬ box j z :=
  fun hb => (shell_le_iff.mpr hb).not_gt (h.symm ▸ hj)

private lemma rank_inj {i : ℕ} {a b : ℤ} (hi : 0 < i)
    (ha : shell a = i) (hb : shell b = i) (h : rank i a = rank i b) : a = b := by
  induction i generalizing a b with
  | zero => omega
  | succ i ih =>
    cases i with
    | zero =>
      obtain ⟨u, rfl⟩ := as_base_value (box_of_shell ha)
      obtain ⟨v, rfl⟩ := as_base_value (box_of_shell hb)
      exact base_inj_finite u v (not_box_of_shell ha (by decide))
        (not_box_of_shell hb (by decide)) h
    | succ n =>
      obtain ⟨hd, hq⟩ := rank_eq_parts h
      have hm := digit_mod_inj hd
      have he := ih (by omega : 0 < n + 1) (shell_div ha) (shell_div hb) hq
      omega

private lemma no_three_in_shell {i : ℕ} {a b c : ℤ}
    (ha : shell a = i) (hb : shell b = i) (hc : shell c = i)
    (hap : a + c = 2 * b) (hab : rank i a < rank i b) (hbc : rank i b < rank i c) :
    False := by
  induction i generalizing a b c with
  | zero => exact (lt_irrefl 0) hab
  | succ i ih =>
    cases i with
    | zero =>
      obtain ⟨u, rfl⟩ := as_base_value (box_of_shell ha)
      obtain ⟨v, rfl⟩ := as_base_value (box_of_shell hb)
      have hce : c = 2 * baseValue v - baseValue u := by omega
      subst c
      exact base_three_finite u v (not_box_of_shell ha (by decide))
        (not_box_of_shell hb (by decide)) (box_of_shell hc)
        (not_box_of_shell hc (by decide)) ⟨hab, hbc⟩
    | succ n =>
      by_cases hres : a % 8 = b % 8
      · have hres' : b % 8 = c % 8 := by omega
        exact ih (shell_div ha) (shell_div hb) (shell_div hc) (by omega)
          (quotient_rank_lt hab hres) (quotient_rank_lt hbc hres')
      · have hres' : b % 8 ≠ c % 8 := by omega
        exact no_digit_three hap (digit_lt_of_rank_lt hab hres) (digit_lt_of_rank_lt hbc hres')

private lemma no_four_across_shells {i : ℕ} {a b c d : ℤ}
    (ha : shell a = i) (hb : shell b = i) (hc : shell c = i + 1) (hd : shell d = i + 1)
    (hap₁ : a + c = 2 * b) (hap₂ : b + d = 2 * c)
    (hab : rank i a < rank i b) (hcd : rank (i + 1) c < rank (i + 1) d) : False := by
  induction i generalizing a b c d with
  | zero => exact (lt_irrefl 0) hab
  | succ i ih =>
    cases i with
    | zero =>
      obtain ⟨u, rfl⟩ := as_base_value (box_of_shell ha)
      obtain ⟨v, rfl⟩ := as_base_value (box_of_shell hb)
      have hce : c = 2 * baseValue v - baseValue u := by omega
      have hde : d = 3 * baseValue v - 2 * baseValue u := by omega
      subst c d
      exact base_four_finite u v (not_box_of_shell ha (by decide))
        (not_box_of_shell hb (by decide))
        (box_of_shell hc) (not_box_of_shell hc (by decide))
        (box_of_shell hd) (not_box_of_shell hd (by decide)) ⟨hab, hcd⟩
    | succ n =>
      by_cases hres : a % 8 = b % 8
      · have hres₁ : b % 8 = c % 8 := by omega
        have hres₂ : c % 8 = d % 8 := by omega
        exact ih (shell_div ha) (shell_div hb)
          (shell_div (n := n + 1) hc) (shell_div (n := n + 1) hd)
          (by omega) (by omega) (quotient_rank_lt hab hres) (quotient_rank_lt hcd hres₂)
      · have hres' : c % 8 ≠ d % 8 := by omega
        exact no_digit_four hap₁ hap₂
          (digit_lt_of_rank_lt hab hres) (digit_lt_of_rank_lt (n := n + 1) hcd hres')

-- The first three stages are zero, the first shell, and minus one.
private def stage (z : ℤ) : ℕ := if z = -1 then 3 else 2 * shell z

private lemma twice_shell_le_stage (z : ℤ) : 2 * shell z ≤ stage z := by
  by_cases hz : z = -1
  · have hs : shell z = 0 := shell_zero_iff.mpr (Or.inr hz)
    rw [hs, stage, if_pos hz]
    decide
  · simp [stage, hz]

private lemma stage_at_zero : stage 0 = 0 := by
  have hs : shell 0 = 0 := shell_zero_iff.mpr (Or.inl rfl)
  norm_num [stage, hs]

private lemma stage_at_minus_one : stage (-1) = 3 := by simp [stage]

private def key (z : ℤ) : ℕ := capacity (stage z) + rank (shell z) z

private lemma key_lt_of_stage_lt {a b : ℤ} (h : stage a < stage b) : key a < key b := by
  have hs : shell a ≤ stage a := by have := twice_shell_le_stage a; omega
  have hr := (rank_lt_capacity (shell a) a).trans_le (capacity_mono hs)
  have hcap := capacity_mono (show stage a + 1 ≤ stage b by omega)
  rw [capacity_succ] at hcap
  unfold key
  omega

private lemma stage_le_of_key_lt {a b : ℤ} (h : key a < key b) : stage a ≤ stage b :=
  le_of_not_gt fun hn => (key_lt_of_stage_lt hn).not_gt h

private lemma key_inj : Function.Injective key := by
  intro a b he
  have hs : stage a = stage b := by
    apply le_antisymm
    · exact le_of_not_gt fun h => (key_lt_of_stage_lt h).ne he.symm
    · exact le_of_not_gt fun h => (key_lt_of_stage_lt h).ne he
  by_cases ha : a = -1
  · by_contra! hab
    have hb : b ≠ -1 := by omega
    simp [stage, ha, hb] at hs
    omega
  by_cases hb : b = -1
  · simp [stage, ha, hb] at hs
    omega
  have hShell : shell a = shell b := by simpa [stage, ha, hb] using hs
  by_cases hz : shell a = 0
  · have ha' := (shell_zero_iff.mp hz).resolve_right ha
    have hb' := (shell_zero_iff.mp (hShell ▸ hz)).resolve_right hb
    exact ha'.trans hb'.symm
  · have hRank : rank (shell b) a = rank (shell b) b := by
      simpa only [key, hs, hShell, Nat.add_left_cancel_iff] using he
    exact rank_inj (by omega) hShell rfl hRank

private lemma rank_lt_of_key_lt {i : ℕ} {a b : ℤ}
    (ha : shell a = i) (hb : shell b = i) (ha' : a ≠ -1) (hb' : b ≠ -1)
    (h : key a < key b) : rank i a < rank i b := by
  simpa only [key, stage, if_neg ha', if_neg hb', ha, hb, Nat.add_lt_add_iff_left] using h

private lemma ne_zero_of_key_lt {a b : ℤ} (h : key a < key b) : b ≠ 0 := by
  intro hb
  subst b
  have hs := stage_le_of_key_lt h
  rw [stage_at_zero] at hs
  have ha' : a ≠ -1 := by
    intro he
    subst a
    rw [stage_at_minus_one] at hs
    omega
  have hsa := twice_shell_le_stage a
  have ha : a = 0 := (shell_zero_iff.mp (by omega : shell a = 0)).resolve_right ha'
  exact (lt_irrefl _) (ha ▸ h)

private lemma no_three_ending_minus_one {a b : ℤ} (hap : a + (-1) = 2 * b)
    (hab : key a < key b) (hb₁ : key b < key (-1)) : False := by
  have hsa := stage_le_of_key_lt (hab.trans hb₁)
  have hsb := stage_le_of_key_lt hb₁
  rw [stage_at_minus_one] at hsa hsb
  have hta := twice_shell_le_stage a
  have htb := twice_shell_le_stage b
  have hba : box 1 a := shell_le_iff.mp (by omega)
  have hbb : box 1 b := shell_le_iff.mp (by omega)
  have han : a ≠ -1 := fun h => (lt_irrefl _) (h ▸ hab.trans hb₁)
  have hbn : b ≠ -1 := fun h => (lt_irrefl _) (h ▸ hb₁)
  have hbz := ne_zero_of_key_lt hab
  have hpre : prefixRank a < prefixRank b := by
    by_cases haz : a = 0
    · simp [prefixRank, haz, hbz]
    · have hsa' : shell a = 1 := by
        have hn : shell a ≠ 0 := fun h => (shell_zero_iff.mp h).elim haz han
        omega
      have hsb' : shell b = 1 := by
        have hn : shell b ≠ 0 := fun h => (shell_zero_iff.mp h).elim hbz hbn
        omega
      have hr := rank_lt_of_key_lt hsa' hsb' han hbn hab
      simpa [prefixRank, haz, hbz, rank] using hr
  obtain ⟨u, rfl⟩ := as_base_value hba
  obtain ⟨v, rfl⟩ := as_base_value hbb
  exact prefix_three_finite u v (by omega) hpre

private lemma box_after_two {i : ℕ} {a b c d e : ℤ} (ha : box i a) (hb : box i b)
    (hap₁ : a + c = 2 * b) (hap₂ : b + d = 2 * c) (hap₃ : c + e = 2 * d) :
    box (i + 1) c ∧ box (i + 1) d ∧ box (i + 1) e := by
  unfold box at *
  simp only [pow_succ]
  have hp : (0 : ℤ) ≤ (8 : ℤ) ^ i := by positivity
  omega

private lemma shell_after_jump {i : ℕ} {z : ℤ} (hz : z ≠ -1)
    (hjump : 2 * i < stage z) (hbox : box (i + 1) z) : shell z = i + 1 := by
  have hs := shell_le_iff.mpr hbox
  simp [stage, hz] at hjump
  omega

private lemma no_five_keys {a b c d e : ℤ}
    (hap₁ : a + c = 2 * b) (hap₂ : b + d = 2 * c) (hap₃ : c + e = 2 * d)
    (hab : key a < key b) (hbc : key b < key c) (hcd : key c < key d)
    (hde : key d < key e) : False := by
  have hc' : c ≠ -1 := by
    intro hc
    subst c
    exact no_three_ending_minus_one hap₁ hab hbc
  have hd' : d ≠ -1 := by
    intro hd
    subst d
    exact no_three_ending_minus_one hap₂ hbc hcd
  have he' : e ≠ -1 := by
    intro he
    subst e
    exact no_three_ending_minus_one hap₃ hcd hde
  let i := if b = -1 then 1 else shell b
  have hib : stage b ≤ 2 * i + 1 := by
    by_cases hb : b = -1 <;> simp [i, stage, hb]
  have hsab := stage_le_of_key_lt hab
  have hsbc := stage_le_of_key_lt hbc
  have hscd := stage_le_of_key_lt hcd
  have hsde := stage_le_of_key_lt hde
  have hba : box i a := by
    have := twice_shell_le_stage a
    exact shell_le_iff.mp (by omega)
  have hbb : box i b := by
    have := twice_shell_le_stage b
    exact shell_le_iff.mp (by omega)
  by_cases hjump : 2 * i < stage c
  · obtain ⟨hbc', hbd, hbe⟩ := box_after_two hba hbb hap₁ hap₂ hap₃
    have hsc := shell_after_jump hc' hjump hbc'
    have hsd := shell_after_jump hd' (hjump.trans_le hscd) hbd
    have hse := shell_after_jump he' (hjump.trans_le (hscd.trans hsde)) hbe
    exact no_three_in_shell hsc hsd hse hap₃
      (rank_lt_of_key_lt hsc hsd hc' hd' hcd) (rank_lt_of_key_lt hsd hse hd' he' hde)
  · have hb' : b ≠ -1 := by
      intro hb
      simp [i, hb, stage] at hjump hsbc
      omega
    have hsb : shell b = i := by simp [i, hb']
    have hstageb : stage b = 2 * i := by simp [stage, hb', hsb]
    have hstagec : stage c = 2 * shell c := by simp [stage, hc']
    have hsc : shell c = i := by omega
    have hrbc := rank_lt_of_key_lt hsb hsc hb' hc' hbc
    have hjumpd : 2 * i < stage d := by
      by_contra! hn
      have hstaged : stage d = 2 * shell d := by simp [stage, hd']
      have hsd : shell d = i := by omega
      exact no_three_in_shell hsb hsc hsd hap₂ hrbc (rank_lt_of_key_lt hsc hsd hc' hd' hcd)
    have hbc' := box_of_shell hsc
    obtain ⟨hbd, hbe, -⟩ := box_after_two hbb hbc' hap₂ hap₃
      (show d + (2 * e - d) = 2 * e by omega)
    have hsd := shell_after_jump hd' hjumpd hbd
    have hse := shell_after_jump he' (hjumpd.trans_le hsde) hbe
    exact no_four_across_shells hsb hsc hsd hse hap₂ hap₃ hrbc
      (rank_lt_of_key_lt hsd hse hd' he' hde)

private lemma no_five_key_progression (a d : ℤ)
    (h₀ : key a < key (a + d))
    (h₁ : key (a + d) < key (a + 2 * d))
    (h₂ : key (a + 2 * d) < key (a + 3 * d))
    (h₃ : key (a + 3 * d) < key (a + 4 * d)) : False :=
  no_five_keys (by ring) (by ring) (by ring) h₀ h₁ h₂ h₃

private noncomputable def orderedIntegers : ℕ ≃ ℤ := by
  letI : Infinite (Set.range key) := (Set.infinite_range_of_injective key_inj).to_subtype
  exact (Nat.Subtype.orderIsoOfNat (Set.range key)).toEquiv.trans (Equiv.ofInjective key key_inj).symm

private lemma orderedIntegers_key : StrictMono fun n : ℕ => key (orderedIntegers n) := by
  let : Infinite (Set.range key) := (Set.infinite_range_of_injective key_inj).to_subtype
  let e := Nat.Subtype.orderIsoOfNat (Set.range key)
  intro m n hmn
  have hval (i : ℕ) : key (orderedIntegers i) = (e i).val := by
    exact congrArg Subtype.val ((Equiv.ofInjective key key_inj).apply_symm_apply (e i))
  change key (orderedIntegers m) < key (orderedIntegers n)
  rw [hval, hval]
  exact e.strictMono hmn

private lemma range_pair {r : ℤ → ℤ → Prop} {k i j : ℕ} {a d : ℤ}
    (h : ((List.range k).map fun n => a + n • d).Pairwise r)
    (hij : i < j) (hjk : j < k) : r (a + (i : ℤ) * d) (a + (j : ℤ) * d) := by
  have hi : i < ((List.range k).map fun n => a + n • d).length := by
    simpa using hij.trans hjk
  have hj : j < ((List.range k).map fun n => a + n • d).length := by simpa using hjk
  simpa only [List.getElem_map, List.getElem_range, nsmul_eq_mul] using
    (List.pairwise_iff_getElem.mp h) i j hi hj hij

private lemma no_long_ap {k : ℕ} (hk : 5 ≤ k) :
    ¬ HasMonotoneAP orderedIntegers k := by
  rintro ⟨l, ⟨a, d, hap⟩, hp⟩
  have hkeys : (l.map orderedIntegers).Pairwise (fun x y => key x < key y) :=
    List.pairwise_map.mpr (hp.imp fun h => orderedIntegers_key h)
  rcases hap with hforward | hreverse
  · rw [hforward] at hkeys
    have h₀ := range_pair hkeys (i := 0) (j := 1) (by decide) (by omega)
    have h₁ := range_pair hkeys (i := 1) (j := 2) (by decide) (by omega)
    have h₂ := range_pair hkeys (i := 2) (j := 3) (by decide) (by omega)
    have h₃ := range_pair hkeys (i := 3) (j := 4) (by decide) (by omega)
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, one_mul, add_zero] at h₀ h₁ h₂ h₃
    exact no_five_key_progression a d h₀ h₁ h₂ h₃
  · rw [hreverse, List.map_reverse, List.pairwise_reverse] at hkeys
    have h₀ := range_pair hkeys (i := 0) (j := 1) (by decide) (by omega)
    have h₁ := range_pair hkeys (i := 1) (j := 2) (by decide) (by omega)
    have h₂ := range_pair hkeys (i := 2) (j := 3) (by decide) (by omega)
    have h₃ := range_pair hkeys (i := 3) (j := 4) (by decide) (by omega)
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, one_mul, add_zero] at h₀ h₁ h₂ h₃
    apply no_five_key_progression (a + 4 * d) (-d)
    · convert h₃ using 2
      all_goals ring
    · convert h₂ using 2
      all_goals ring
    · convert h₁ using 2
      all_goals ring
    · convert h₀ using 2
      all_goals ring

end OMA

theorem OMA.solution : type_of% @Erdos195.erdos_195.variants.leq_4_bound := by
  apply csSup_le'
  intro k hk
  by_contra hn
  exact OMA.no_long_ap (by omega) (hk OMA.orderedIntegers)