import OMAReductions.R_Erdos686_erdos_686_R1_H2_R1

/-! A Vieta descent for the two-factor square quotient in Erdős problem 686. -/

namespace Erdos686SquareQuotients

private def step (s : ℤ) (z : ℤ × ℤ) : ℤ × ℤ :=
  (2 * s * z.1 - z.2, z.1)

private def onConic (s x y : ℤ) : Prop :=
  x ^ 2 + y ^ 2 - 2 * s * x * y = 1

private lemma step_preserves (s x y : ℤ) (h : onConic s x y) :
    onConic s (2 * s * x - y) x := by
  unfold onConic at *
  linear_combination h

private lemma descend (s : ℤ) (a : ℕ) (b : ℤ) (hb : 0 ≤ b) (hba : b < a)
    (h : onConic s a b) :
    ∃ j < a, (step s)^[j] (1, 0) = ((a : ℤ), b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases hb0 : b = 0
    · subst b
      have hsq : (a : ℤ) ^ 2 = 1 := by simpa [onConic] using h
      have ha : a = 1 := by
        rcases sq_eq_one_iff.mp hsq with hp | hm <;> omega
      subst a
      exact ⟨0, by decide, rfl⟩
    · let c : ℤ := 2 * s * b - a
      have ha : 0 < (a : ℤ) := by omega
      have hb1 : 1 ≤ b := by omega
      have prod : a * c = b ^ 2 - 1 := by
        dsimp [c]
        unfold onConic at h
        linear_combination -h
      have hc : 0 ≤ c := by
        by_contra! hc
        have neg := mul_neg_of_pos_of_neg ha hc
        nlinarith only [prod, neg, sq_nonneg (b - 1), hb1]
      have hcb : c < b := by
        by_contra! hcb
        have h₁ := mul_le_mul_of_nonneg_left hcb ha.le
        have h₂ := mul_le_mul_of_nonneg_right hba.le hb
        nlinarith only [prod, h₁, h₂]
      have hnext : onConic s b c := by
        dsimp [c]
        unfold onConic at *
        linear_combination h
      have cast_b : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb
      obtain ⟨j, hj, hjval⟩ := ih b.toNat (by omega) c hc (by omega)
        (by simpa only [cast_b] using hnext)
      refine ⟨j + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply', hjval]
      simp only [step, cast_b, c, sub_sub_cancel]

private lemma iterate_properties (s : ℤ) (hs : 3 ≤ s) (j : ℕ) :
    let z := (step s)^[j] (1, 0)
    0 ≤ z.2 ∧ z.2 < z.1 ∧ onConic s z.1 z.2 ∧ Odd (z.1 + z.2) ∧
      (j = 0 ∨ 2 * s ≤ z.1) := by
  induction j with
  | zero =>
    change (0 : ℤ) ≤ 0 ∧ (0 : ℤ) < 1 ∧ onConic s 1 0 ∧ Odd (1 + 0 : ℤ) ∧ _
    exact ⟨by decide, by decide, by simp [onConic], ⟨0, by decide⟩, Or.inl rfl⟩
  | succ j ih =>
    let z := (step s)^[j] (1, 0)
    obtain ⟨hy, hyx, hinv, ⟨w, hw⟩, _⟩ := ih
    change 0 ≤ z.2 at hy
    change z.2 < z.1 at hyx
    change z.1 + z.2 = 2 * w + 1 at hw
    rw [Function.iterate_succ_apply']
    change 0 ≤ z.1 ∧ z.1 < 2 * s * z.1 - z.2 ∧
      onConic s (2 * s * z.1 - z.2) z.1 ∧ Odd (2 * s * z.1 - z.2 + z.1) ∧ _
    have hx : 1 ≤ z.1 := by omega
    have grow := mul_nonneg (by omega : 0 ≤ 2 * s - 2) (by omega : 0 ≤ z.1 - 1)
    refine ⟨by omega, by nlinarith only [grow, hs, hx, hyx], step_preserves _ _ _ hinv,
      ⟨s * z.1 - z.2 + w, ?_⟩, Or.inr ?_⟩
    · linear_combination hw
    · change 2 * s ≤ 2 * s * z.1 - z.2
      nlinarith only [grow, hx, hyx]

/-- All integer square quotients for two disjoint blocks of length two.
Both indices in the recurrence test are strictly smaller than the square root. -/
theorem length_two_iff :
    ∀ a : ℕ, 2 ≤ a →
    ((∃ n m : ℕ, n + 2 ≤ m ∧ a ^ 2 * (n + 1) * (n + 2) = (m + 1) * (m + 2)) ↔
      ∃ n < a, ∃ j < a,
        ((fun z : ℤ × ℤ => (2 * (2 * (n : ℤ) + 3) * z.1 - z.2, z.1))^[j] (1, 0)).1 = a) := by
  intro a ha
  have ha' : 2 ≤ (a : ℤ) := by exact_mod_cast ha
  constructor
  · rintro ⟨n, m, _, heq⟩
    let s : ℤ := 2 * n + 3
    let t : ℤ := 2 * m + 3
    let b : ℤ := s * a - t
    have hs : 3 ≤ s := by dsimp [s]; omega
    have ht : 0 < t := by dsimp [t]; omega
    have hcast : (a : ℤ) ^ 2 * (n + 1) * (n + 2) = (m + 1) * (m + 2) := by
      exact_mod_cast heq
    have pell : t ^ 2 - (s ^ 2 - 1) * (a : ℤ) ^ 2 = 1 := by
      dsimp [s, t]
      linear_combination -4 * hcast
    have prod : b * (s * a + t) = (a : ℤ) ^ 2 - 1 := by
      dsimp [b]
      linear_combination -pell
    have hsum : (a : ℤ) < s * a + t := by
      nlinarith only [mul_nonneg (by omega : 0 ≤ s - 1) (by omega : 0 ≤ (a : ℤ)), ht]
    have hb : 0 < b := by
      by_contra! hn
      have hneg := mul_nonpos_of_nonpos_of_nonneg hn (by omega : 0 ≤ s * a + t)
      nlinarith only [hneg, prod, sq_nonneg ((a : ℤ) - 1), ha']
    have hba : b < a := by
      by_contra! hc
      have h₁ := mul_le_mul_of_nonneg_right hc (by omega : 0 ≤ s * a + t)
      have h₂ := mul_le_mul_of_nonneg_left hsum.le (by omega : 0 ≤ (a : ℤ))
      nlinarith only [h₁, h₂, prod]
    have hsa : s < a := by
      by_contra! hle
      have h₁ := mul_le_mul_of_nonneg_right (by omega : 1 ≤ b) (by omega : 0 ≤ s * a + t)
      have h₂ := mul_le_mul_of_nonneg_right hle (by omega : 0 ≤ (a : ℤ))
      nlinarith only [h₁, h₂, prod, ht]
    have hinv : onConic s a b := by
      dsimp [onConic, b]
      linear_combination pell
    obtain ⟨j, hj, hpair⟩ := descend s a b hb.le hba hinv
    exact ⟨n, by dsimp [s] at hsa; omega, j, hj, congrArg Prod.fst hpair⟩
  · rintro ⟨n, _, j, _, hjval⟩
    let s : ℤ := 2 * n + 3
    let z := (step s)^[j] (1, 0)
    let b := z.2
    have hs : 3 ≤ s := by dsimp [s]; omega
    have hx : z.1 = a := hjval
    obtain ⟨hb, hba, hinv, hodd, hlarge⟩ := iterate_properties s hs j
    change b < z.1 at hba
    change onConic s z.1 b at hinv
    change Odd (z.1 + b) at hodd
    change j = 0 ∨ 2 * s ≤ z.1 at hlarge
    rw [hx] at hba hinv hodd hlarge
    have large : 2 * s ≤ a := hlarge.resolve_left (by
      rintro rfl
      change (1 : ℤ) = a at hx
      omega)
    let t := s * (a : ℤ) - b
    have ht : s + 4 ≤ t := by
      dsimp [t]
      nlinarith only [mul_nonneg (by omega : 0 ≤ s - 1) (by omega : 0 ≤ (a : ℤ) - 4),
        hba, hs]
    obtain ⟨w, hw⟩ := hodd
    have htodd : Odd t := by
      refine ⟨((n : ℤ) + 1) * a - b + w, ?_⟩
      dsimp [t, s]
      linear_combination hw
    obtain ⟨d, hd⟩ := htodd
    let m := (d - 1).toNat
    have hm : (m : ℤ) = d - 1 := Int.toNat_of_nonneg (by omega)
    have ht' : t = 2 * (m : ℤ) + 3 := by omega
    have pell : t ^ 2 - (s ^ 2 - 1) * (a : ℤ) ^ 2 = 1 := by
      dsimp [t]
      unfold onConic at hinv
      linear_combination hinv
    rw [ht'] at pell
    dsimp [s] at pell ht
    refine ⟨n, m, by omega, ?_⟩
    exact_mod_cast (show (a : ℤ) ^ 2 * (n + 1) * (n + 2) = (m + 1) * (m + 2) by
      nlinarith only [pell])

end Erdos686SquareQuotients

theorem OMA.solution : OMA.R_Erdos686_erdos_686_R1_H2_R1.H1 := by
  exact Erdos686SquareQuotients.length_two_iff
