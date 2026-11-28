import OMAStatements.S_oeis_a273446

namespace OMA.S_oeis_a273446






/-- The same count for Rule 729. -/
noncomputable def a729 (n : ℕ) : ℕ := count 729 (2 ^ n - 1)

def origin (p : ℤ × ℤ) : Prop := p.1 = 0 ∧ p.2 = 0
def plus (p : ℤ × ℤ) : Prop := -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 ∧ (p.1 = 0 ∨ p.2 = 0)
def corners (p : ℤ × ℤ) : Prop := (p.1 = 1 ∨ p.1 = -1) ∧ (p.2 = 1 ∨ p.2 = -1)
def ring (p : ℤ × ℤ) : Prop := -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 ∧ ¬ (p.1 = 0 ∧ p.2 = 0)

instance (p : ℤ × ℤ) : Decidable (origin p) := by unfold origin; infer_instance
instance (p : ℤ × ℤ) : Decidable (plus p) := by unfold plus; infer_instance
instance (p : ℤ × ℤ) : Decidable (corners p) := by unfold corners; infer_instance
instance (p : ℤ × ℤ) : Decidable (ring p) := by unfold ring; infer_instance

lemma step_eq (N : ℕ) (f : ℤ × ℤ → Bool) (x y : ℤ) :
    rule N (f (x, y)) ((nbrs (x, y)).countP f) =
      rule N (f (x, y)) ((if f (x + 1, y) then 1 else 0) + (if f (x - 1, y) then 1 else 0) +
        (if f (x, y + 1) then 1 else 0) + (if f (x, y - 1) then 1 else 0)) := by
  simp only [nbrs, List.countP_cons, List.countP_nil]
  congr 1
  ring_nf

lemma state_succ (N t : ℕ) (p : ℤ × ℤ) :
    state N (t + 1) p = rule N (state N t p) ((nbrs p).countP (fun q => state N t q)) := rfl

lemma s0 (N : ℕ) (p : ℤ × ℤ) : state N 0 p = decide (¬ ¬ origin p) := by
  obtain ⟨x, y⟩ := p
  show decide ((x, y) = (0, 0)) = _
  exact decide_eq_decide.mpr (by unfold origin; simp)

lemma s1 (N : ℕ) (hN : N = 721 ∨ N = 729) (p : ℤ × ℤ) : state N 1 p = decide (¬ plus p) := by
  obtain ⟨x, y⟩ := p
  rw [state_succ, show (fun q => state N 0 q) = (fun q => decide (¬ ¬ origin q)) from funext (s0 N),
    s0, step_eq N (fun q => decide (¬ ¬ origin q))]
  rcases hN with rfl | rfl <;>
  by_cases h1 : origin (x, y) <;> by_cases h2 : origin (x + 1, y) <;>
    by_cases h3 : origin (x - 1, y) <;> by_cases h4 : origin (x, y + 1) <;>
    by_cases h5 : origin (x, y - 1) <;> by_cases h6 : plus (x, y) <;>
    simp only [h1, h2, h3, h4, h5, h6, decide_true, decide_false, not_true, not_false_eq_true] <;>
    first
      | decide
      | (exfalso; unfold origin plus at *; simp only at *; omega)

lemma s2 (N : ℕ) (hN : N = 721 ∨ N = 729) (p : ℤ × ℤ) : state N 2 p = decide (¬ corners p) := by
  obtain ⟨x, y⟩ := p
  rw [state_succ, show (fun q => state N 1 q) = (fun q => decide (¬ plus q)) from funext (s1 N hN),
    s1 N hN, step_eq N (fun q => decide (¬ plus q))]
  rcases hN with rfl | rfl <;>
  by_cases h1 : plus (x, y) <;> by_cases h2 : plus (x + 1, y) <;> by_cases h3 : plus (x - 1, y) <;>
    by_cases h4 : plus (x, y + 1) <;> by_cases h5 : plus (x, y - 1) <;>
    by_cases h6 : corners (x, y) <;>
    simp only [h1, h2, h3, h4, h5, h6, decide_true, decide_false, not_true, not_false_eq_true] <;>
    first
      | decide
      | (exfalso; unfold plus corners at *; simp only at *; omega)

lemma s3 (N : ℕ) (hN : N = 721 ∨ N = 729) (p : ℤ × ℤ) : state N 3 p = decide (¬ ring p) := by
  obtain ⟨x, y⟩ := p
  rw [state_succ, show (fun q => state N 2 q) = (fun q => decide (¬ corners q)) from
    funext (s2 N hN), s2 N hN, step_eq N (fun q => decide (¬ corners q))]
  rcases hN with rfl | rfl <;>
  by_cases h1 : corners (x, y) <;> by_cases h2 : corners (x + 1, y) <;>
    by_cases h3 : corners (x - 1, y) <;> by_cases h4 : corners (x, y + 1) <;>
    by_cases h5 : corners (x, y - 1) <;> by_cases h6 : ring (x, y) <;>
    simp only [h1, h2, h3, h4, h5, h6, decide_true, decide_false, not_true, not_false_eq_true] <;>
    first
      | decide
      | (exfalso; unfold corners ring at *; simp only at *; omega)

lemma s4 (N : ℕ) (hN : N = 721 ∨ N = 729) (p : ℤ × ℤ) : state N 4 p = decide (¬ origin p) := by
  obtain ⟨x, y⟩ := p
  rw [state_succ, show (fun q => state N 3 q) = (fun q => decide (¬ ring q)) from funext (s3 N hN),
    s3 N hN, step_eq N (fun q => decide (¬ ring q))]
  rcases hN with rfl | rfl <;>
  by_cases h1 : ring (x, y) <;> by_cases h2 : ring (x + 1, y) <;> by_cases h3 : ring (x - 1, y) <;>
    by_cases h4 : ring (x, y + 1) <;> by_cases h5 : ring (x, y - 1) <;> by_cases h6 : origin (x, y) <;>
    simp only [h1, h2, h3, h4, h5, h6, decide_true, decide_false, not_true, not_false_eq_true] <;>
    first
      | decide
      | (exfalso; unfold ring origin at *; simp only at *; omega)

lemma step_origin (N : ℕ) (hN : N = 721 ∨ N = 729) (p : ℤ × ℤ) :
    rule N (decide (¬ origin p)) ((nbrs p).countP (fun q => decide (¬ origin q))) =
      decide (¬ origin p) := by
  obtain ⟨x, y⟩ := p
  rw [step_eq N (fun q => decide (¬ origin q))]
  rcases hN with rfl | rfl <;>
  by_cases h1 : origin (x, y) <;> by_cases h2 : origin (x + 1, y) <;>
    by_cases h3 : origin (x - 1, y) <;> by_cases h4 : origin (x, y + 1) <;>
    by_cases h5 : origin (x, y - 1) <;>
    simp only [h1, h2, h3, h4, h5, decide_true, decide_false, not_true, not_false_eq_true] <;>
    first
      | decide
      | (exfalso; unfold origin at *; simp only at *; omega)

/-- From step 4 on, the origin is the only OFF cell, for both rules. -/
lemma pattern (N : ℕ) (hN : N = 721 ∨ N = 729) (t : ℕ) (ht : 4 ≤ t) (p : ℤ × ℤ) :
    state N t p = decide (¬ origin p) := by
  induction t, ht using Nat.le_induction generalizing p with
  | base => exact s4 N hN p
  | succ t _ ih =>
    rw [state_succ, show (fun q => state N t q) = (fun q => decide (¬ origin q)) from funext ih, ih,
      step_origin N hN]

/-- The two rules evolve identically. -/
lemma same (t : ℕ) (p : ℤ × ℤ) : state 729 t p = state 721 t p := by
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ 4 ≤ t) with h | h | h | h | h
  · subst h; rfl
  · subst h; rw [s1 _ (Or.inr rfl), s1 _ (Or.inl rfl)]
  · subst h; rw [s2 _ (Or.inr rfl), s2 _ (Or.inl rfl)]
  · subst h; rw [s3 _ (Or.inr rfl), s3 _ (Or.inl rfl)]
  · rw [pattern _ (Or.inr rfl) t h, pattern _ (Or.inl rfl) t h]

/-- Blomberg's first conjecture: Rule 729 generates the same sequence. -/
theorem rule729 (n : ℕ) : a729 n = a n := by
  unfold a729 a count
  congr 1
  exact Finset.filter_congr fun p _ => by rw [same]

lemma count_large (N : ℕ) (hN : N = 721 ∨ N = 729) (s : ℕ) (hs : 4 ≤ s) :
    count N s = (2 * s + 1) * (2 * s + 1) - 1 := by
  unfold count
  have hf : (Finset.Icc (-(s : ℤ)) s ×ˢ Finset.Icc (-(s : ℤ)) s).filter (fun p => state N s p) =
      (Finset.Icc (-(s : ℤ)) s ×ˢ Finset.Icc (-(s : ℤ)) s).erase (0, 0) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_erase, pattern N hN s hs]
    constructor
    · rintro ⟨hm, hd⟩
      refine ⟨?_, hm⟩
      have := of_decide_eq_true hd
      unfold origin at this
      intro h0
      simp only [Prod.mk.injEq] at h0
      exact this h0
    · rintro ⟨hne, hm⟩
      refine ⟨hm, decide_eq_true ?_⟩
      unfold origin
      intro h0
      exact hne (Prod.ext h0.1 h0.2)
  rw [hf, Finset.card_erase_of_mem (by simp), Finset.card_product, Int.card_Icc]
  congr 1
  have : ((s : ℤ) + 1 - -(s : ℤ)).toNat = 2 * s + 1 := by omega
  rw [this]

/-- Blomberg's second conjecture: `a(n) = 4*4^n - 4*2^n` for `n > 2`. -/
theorem closed_form (n : ℕ) (hn : 2 < n) : a n = 4 * 4 ^ n - 4 * 2 ^ n := by
  unfold a
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [count_large 721 (Or.inl rfl) _ (by omega)]
  have h4 : 4 ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  rw [h4]
  zify [h8, (by nlinarith : 4 * 2 ^ n ≤ 4 * (2 ^ n * 2 ^ n)),
    (by nlinarith : 1 ≤ (2 * (2 ^ n - 1) + 1) * (2 * (2 ^ n - 1) + 1)),
    (by omega : 1 ≤ 2 ^ n)]
  ring

/-- Controls: the listed terms a(0..2) = 1, 4, 41. -/
example : a 0 = 1 ∧ a 1 = 4 ∧ a 2 = 41 := by
  refine ⟨by decide, by decide, ?_⟩
  show count 721 3 = 41
  unfold count
  decide

end OMA.S_oeis_a273446

theorem OMA.solution : type_of% @OMA.S_oeis_a273446.main :=
  ⟨fun n => OMA.S_oeis_a273446.rule729 n, fun n hn => OMA.S_oeis_a273446.closed_form n hn⟩
