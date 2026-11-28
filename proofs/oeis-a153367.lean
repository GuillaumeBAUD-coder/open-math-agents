import OMAStatements.S_oeis_a153367
import Mathlib

/-!
# A153367: transfer-matrix proof of Barker's recurrence and closed form

Credit: @ivillar

`T m y` counts the admissible paths with `m + 1` rows that end in column `y`. Splitting off the
last row (`Fin.snocEquiv`) gives `T (m + 1) y = Σ_{x adjacent to y} T m x`, the parity condition
being automatic because `T m x = 0` when `m + x` is even. With `v = T (2k) ·` (supported on the odd
columns), a(k+1) = Σ v, a(k+2) = 1ᵀ B v and a(k+3) = 1ᵀ B² v where B = 2I + J on the odd columns
and J is the path adjacency on 4 vertices; since 1ᵀ(B² - 5B + 5I) = 1ᵀ(J² - J - I) = 0, the
recurrence a(n) = 5a(n-1) - 5a(n-2) holds for n > 2. The closed form follows by induction from
a(1) = 4, a(2) = 14, because (5 ± √5)² = 10(5 ± √5) - 20.
-/

namespace PA153367

def Good (M : ℕ) (p : Fin M → Fin 9) : Prop :=
  (∀ i j : Fin M, j.val = i.val + 1 → (p i).val = (p j).val + 1 ∨ (p j).val = (p i).val + 1) ∧
    ∀ i : Fin M, (i.val + (p i).val) % 2 = 1

instance (M : ℕ) : DecidablePred (Good M) := fun p => by unfold Good; infer_instance

def T (m : ℕ) (y : Fin 9) : ℕ :=
  ∑ q : Fin (m + 1) → Fin 9, if Good (m + 1) q ∧ q (Fin.last m) = y then 1 else 0

theorem a_eq (n : ℕ) : OMA.S_oeis_a153367.a n =
    ∑ p : Fin (2 * n - 1) → Fin 9, if Good (2 * n - 1) p then 1 else 0 := by
  unfold OMA.S_oeis_a153367.a
  rw [Finset.card_filter]
  rfl

theorem sum_split (m : ℕ) :
    ∑ p : Fin (m + 1) → Fin 9, (if Good (m + 1) p then 1 else 0) = ∑ y, T m y := by
  unfold T
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : Good (m + 1) p
  · simp [h]
  · simp [h]

theorem snocE (m : ℕ) (q : Fin (m + 1) → Fin 9) (y : Fin 9) :
    (Fin.snocEquiv fun _ => Fin 9) (y, q) = Fin.snoc q y := rfl

theorem snoc_good (m : ℕ) (q : Fin (m + 1) → Fin 9) (y : Fin 9) :
    Good (m + 1 + 1) (Fin.snoc q y) ↔ Good (m + 1) q ∧
      ((q (Fin.last m)).val = y.val + 1 ∨ y.val = (q (Fin.last m)).val + 1) ∧
      (m + 1 + y.val) % 2 = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, ?_⟩
    · have := h1 (Fin.castSucc i) (Fin.castSucc j) (by simpa using hij)
      simpa using this
    · have := h2 (Fin.castSucc i)
      simpa using this
    · have := h1 (Fin.castSucc (Fin.last m)) (Fin.last (m + 1)) (by simp)
      simpa using this
    · have := h2 (Fin.last (m + 1))
      simpa using this
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have hi : i.val < m + 1 := by simp at hij; omega
        obtain ⟨i', rfl⟩ : ∃ i' : Fin (m + 1), i = Fin.castSucc i' := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
        simp only [Fin.snoc_castSucc]
        exact h1 i' j' (by simpa using hij)
      · have : i = Fin.castSucc (Fin.last m) := Fin.ext (by simp at hij ⊢; omega)
        subst this
        simpa using h3
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · simpa using h2 i'
      · simpa using h4

theorem T_succ (m : ℕ) (y : Fin 9) :
    T (m + 1) y = if (m + 1 + y.val) % 2 = 1 then
      ∑ x : Fin 9, (if x.val = y.val + 1 ∨ y.val = x.val + 1 then T m x else 0) else 0 := by
  unfold T
  rw [← (Fin.snocEquiv (fun _ => Fin 9)).sum_comp, Fintype.sum_prod_type]
  simp only [snocE, snoc_good, Fin.snoc_last]
  rw [Finset.sum_eq_single y (fun z _ hz => by simp [hz]) (by simp)]
  split_ifs with hc
  · simp only [and_true]
    have hR : ∀ x : Fin 9, (if x.val = y.val + 1 ∨ y.val = x.val + 1 then
        ∑ q : Fin (m + 1) → Fin 9, (if Good (m + 1) q ∧ q (Fin.last m) = x then 1 else 0) else 0) =
        ∑ q : Fin (m + 1) → Fin 9, (if (x.val = y.val + 1 ∨ y.val = x.val + 1) ∧
          Good (m + 1) q ∧ q (Fin.last m) = x then 1 else 0) := by
      intro x; split_ifs with h <;> simp [h]
    rw [Finset.sum_congr rfl (fun x _ => hR x), Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single (q (Fin.last m))]
    · by_cases hg : Good (m + 1) q <;>
        by_cases ha : ((q (Fin.last m)).val = y.val + 1 ∨ y.val = (q (Fin.last m)).val + 1) <;>
        simp [hg, ha, hc]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · simp [hc]

theorem T_zero (y : Fin 9) : T 0 y = if y.val % 2 = 1 then 1 else 0 := by
  unfold T
  rw [← (Equiv.funUnique (Fin 1) (Fin 9)).symm.sum_comp, Finset.sum_eq_single y]
  · simp [Good]
  · intro b _ hb; simp [hb]
  · simp

theorem T_van (m : ℕ) (y : Fin 9) (h : (m + y.val) % 2 = 0) : T m y = 0 := by
  unfold T
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [if_neg]
  rintro ⟨⟨_, h2⟩, h3⟩
  have := h2 (Fin.last m)
  rw [h3] at this
  simp at this
  omega

theorem T_rec (m : ℕ) (y : Fin 9) :
    T (m + 1) y = ∑ x : Fin 9, (if x.val = y.val + 1 ∨ y.val = x.val + 1 then T m x else 0) := by
  rw [T_succ]
  split_ifs with hc
  · rfl
  · symm
    refine Finset.sum_eq_zero fun x _ => ?_
    split_ifs with ha
    · exact T_van m x (by omega)
    · rfl

theorem r0 (m : ℕ) : T (m + 1) 0 = T m 1 := by rw [T_rec]; simp [Fin.sum_univ_succ]
theorem r1 (m : ℕ) : T (m + 1) 1 = T m 0 + T m 2 := by rw [T_rec]; simp [Fin.sum_univ_succ]
theorem r2 (m : ℕ) : T (m + 1) 2 = T m 1 + T m 3 := by rw [T_rec]; simp [Fin.sum_univ_succ]
theorem r3 (m : ℕ) : T (m + 1) 3 = T m 2 + T m 4 := by rw [T_rec]; simp [Fin.sum_univ_succ]
theorem r4 (m : ℕ) : T (m + 1) 4 = T m 3 + T m 5 := by rw [T_rec]; simp [Fin.sum_univ_succ]
theorem r5 (m : ℕ) : T (m + 1) 5 = T m 4 + T m 6 := by rw [T_rec]; simp [Fin.sum_univ_succ]
theorem r6 (m : ℕ) : T (m + 1) 6 = T m 5 + T m 7 := by rw [T_rec]; simp [Fin.sum_univ_succ]
theorem r7 (m : ℕ) : T (m + 1) 7 = T m 6 + T m 8 := by rw [T_rec]; simp [Fin.sum_univ_succ]
theorem r8 (m : ℕ) : T (m + 1) 8 = T m 7 := by rw [T_rec]; simp [Fin.sum_univ_succ]

theorem sum9 (f : Fin 9 → ℕ) :
    ∑ y, f y = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp [Fin.sum_univ_succ]
  ring

theorem sum_good (M m : ℕ) (h : M = m + 1) :
    ∑ p : Fin M → Fin 9, (if Good M p then 1 else 0) = ∑ y, T m y := by
  subst h
  exact sum_split m

theorem a_succ (k : ℕ) : OMA.S_oeis_a153367.a (k + 1) = ∑ y, T (2 * k) y := by
  rw [a_eq, sum_good (2 * (k + 1) - 1) (2 * k) (by omega)]

theorem rec_main (k : ℕ) : (OMA.S_oeis_a153367.a (k + 1 + 1 + 1) : ℤ) =
    5 * OMA.S_oeis_a153367.a (k + 1 + 1) - 5 * OMA.S_oeis_a153367.a (k + 1) := by
  rw [a_succ, a_succ, a_succ, show 2 * (k + 1 + 1) = 2 * k + 1 + 1 + 1 + 1 by ring,
    show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
  simp only [sum9, r0, r1, r2, r3, r4, r5, r6, r7, r8]
  have h0 := T_van (2 * k) 0 (by simp)
  have h2 := T_van (2 * k) 2 (by simp)
  have h4 := T_van (2 * k) 4 (by simp)
  have h6 := T_van (2 * k) 6 (by simp)
  have h8 := T_van (2 * k) 8 (by simp)
  simp only [h0, h2, h4, h6, h8]
  push_cast
  ring

theorem a_one : OMA.S_oeis_a153367.a 1 = 4 := by
  rw [a_succ, sum9]
  simp [T_zero]

theorem a_two : OMA.S_oeis_a153367.a 2 = 14 := by
  rw [a_succ, show 2 * 1 = 0 + 1 + 1 from rfl, sum9]
  simp only [r0, r1, r2, r3, r4, r5, r6, r7, r8]
  simp [T_zero]

/-- Barker's closed form. -/
noncomputable def F (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ((5 - Real.sqrt 5) ^ n * (-5 + 3 * Real.sqrt 5) +
    (5 + Real.sqrt 5) ^ n * (5 + 3 * Real.sqrt 5)) / (5 * Real.sqrt 5)

theorem sq_m : (5 - Real.sqrt 5) ^ 2 = 30 - 10 * Real.sqrt 5 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  nlinarith [h]

theorem sq_p : (5 + Real.sqrt 5) ^ 2 = 30 + 10 * Real.sqrt 5 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  nlinarith [h]

theorem F_rec (n : ℕ) : F (n + 2) = 5 * F (n + 1) - 5 * F n := by
  unfold F
  rw [pow_succ (5 - Real.sqrt 5) (n + 1), pow_succ (5 - Real.sqrt 5) n,
    pow_succ (5 + Real.sqrt 5) (n + 1), pow_succ (5 + Real.sqrt 5) n]
  have hm : (5 - Real.sqrt 5) ^ n * (5 - Real.sqrt 5) * (5 - Real.sqrt 5) =
      (5 - Real.sqrt 5) ^ n * (30 - 10 * Real.sqrt 5) := by rw [← sq_m]; ring
  have hp : (5 + Real.sqrt 5) ^ n * (5 + Real.sqrt 5) * (5 + Real.sqrt 5) =
      (5 + Real.sqrt 5) ^ n * (30 + 10 * Real.sqrt 5) := by rw [← sq_p]; ring
  rw [hm, hp]
  ring

theorem s5_ne : Real.sqrt 5 ≠ 0 := by positivity

theorem F_one : F 1 = 4 := by
  unfold F
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  field_simp
  nlinarith [h]

theorem F_two : F 2 = 14 := by
  unfold F
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  rw [sq_m, sq_p]
  field_simp
  nlinarith [h]

theorem closed (k : ℕ) :
    (OMA.S_oeis_a153367.a (k + 1) : ℝ) = F (k + 1) ∧
      (OMA.S_oeis_a153367.a (k + 1 + 1) : ℝ) = F (k + 1 + 1) := by
  induction k with
  | zero => exact ⟨by rw [a_one, F_one]; norm_num, by rw [a_two, F_two]; norm_num⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h := rec_main k
    have h' : (OMA.S_oeis_a153367.a (k + 1 + 1 + 1) : ℝ) =
        5 * OMA.S_oeis_a153367.a (k + 1 + 1) - 5 * OMA.S_oeis_a153367.a (k + 1) := by
      exact_mod_cast h
    rw [h', ih.1, ih.2, F_rec (k + 1)]

end PA153367

theorem OMA.solution : type_of% @OMA.S_oeis_a153367.main := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact (PA153367.closed k).1
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 + 1 + 1 := ⟨n - 3, by omega⟩
    rw [show k + 1 + 1 + 1 - 1 = k + 1 + 1 by omega, show k + 1 + 1 + 1 - 2 = k + 1 by omega]
    exact PA153367.rec_main k
