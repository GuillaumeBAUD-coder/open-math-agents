import OMAStatements.S_oeis_a154138

/-!
The equation (2k + 1)² − 8m² = −23 has two increasing orbits from (k, m) = (1, 2)
and (3, 3). Every solution with k ≥ 8 descends, and the forward map interleaves the
orbits in increasing order. Its square gives the index-four affine recurrence.

The descent and the identification with Nat.nth adapt @Salofe's proof for A154151
(https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19441).
-/

namespace PellTriangles

open OMA.S_oeis_a154138

/-- The pairs (k, m) with 6 + k(k+1) = 2 m^2, in increasing order. -/
def pr : ℕ → ℕ × ℕ
  | 0 => (1, 2)
  | 1 => (3, 3)
  | n + 2 => (3 * (pr n).1 + 4 * (pr n).2 + 1, 2 * (pr n).1 + 3 * (pr n).2 + 1)

theorem pr_add_two (n : ℕ) :
    pr (n + 2) = (3 * (pr n).1 + 4 * (pr n).2 + 1, 2 * (pr n).1 + 3 * (pr n).2 + 1) := rfl

theorem pr_sol (n : ℕ) : 6 + (pr n).1 * ((pr n).1 + 1) = 2 * (pr n).2 ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | n + 2, ih =>
      have h := ih n (by omega)
      rw [pr_add_two]
      dsimp only
      zify at h ⊢
      linear_combination h

theorem pr_mono (n : ℕ) : (pr n).1 < (pr (n + 1)).1 ∧ (pr n).2 < (pr (n + 1)).2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | n + 2, ih =>
      have h := ih n (by omega)
      rw [pr_add_two, show n + 2 + 1 = (n + 1) + 2 by omega, pr_add_two]
      dsimp only
      constructor <;> omega

theorem small_cases : ∀ k < 8, ∀ m < 6, 6 + k * (k + 1) = 2 * m ^ 2 →
    (k = 1 ∧ m = 2) ∨ (k = 3 ∧ m = 3) := by
  decide

theorem complete (k : ℕ) : ∀ m, 6 + k * (k + 1) = 2 * m ^ 2 → ∃ n, pr n = (k, m) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m h
    by_cases hk : k < 8
    · have hm : m < 6 := by nlinarith
      rcases small_cases k hk m hm h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · replace hk : 8 ≤ k := by omega
      have hA : 4 * m ≤ 3 * k + 1 := by nlinarith
      have hB : 2 * k + 1 ≤ 3 * m := by nlinarith
      have hC : 2 * k + 1 < 4 * m := by nlinarith
      obtain ⟨k', hk'⟩ : ∃ k', k' + 4 * m = 3 * k + 1 := ⟨3 * k + 1 - 4 * m, by omega⟩
      obtain ⟨m', hm'⟩ : ∃ m', m' + 2 * k + 1 = 3 * m := ⟨3 * m - (2 * k + 1), by omega⟩
      have hlt : k' < k := by omega
      have hs : 6 + k' * (k' + 1) = 2 * m' ^ 2 := by
        have e1 : (k' : ℤ) = 3 * k + 1 - 4 * m := by omega
        have e2 : (m' : ℤ) = 3 * m - 2 * k - 1 := by omega
        zify at h ⊢
        rw [e1, e2]
        linear_combination h
      obtain ⟨n, hn⟩ := ih k' hlt m' hs
      refine ⟨n + 2, ?_⟩
      rw [pr_add_two, hn]
      dsimp only
      ext <;> dsimp only <;> omega

theorem P_iff (k : ℕ) : P k ↔ ∃ m, 6 + k * (k + 1) = 2 * m ^ 2 := by
  have he : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
  unfold P
  generalize k * (k + 1) = t at he ⊢
  obtain ⟨c, rfl⟩ := he
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by omega⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by omega⟩

theorem q_strictMono : StrictMono (fun n => (pr n).1) :=
  strictMono_nat_of_lt_succ (fun n => (pr_mono n).1)

theorem nth_eq (n : ℕ) : Nat.nth P n = (pr n).1 := by
  have hP : ∀ i, P ((fun n => (pr n).1) i) := fun i => (P_iff _).2 ⟨_, pr_sol i⟩
  have hinf : (Set.ofPred P).Infinite :=
    Set.infinite_of_injective_forall_mem q_strictMono.injective hP
  have h0 : ∀ k, P k → k ∈ Set.range (fun n => (pr n).1) := by
    intro k hk
    obtain ⟨m, hm⟩ := (P_iff k).1 hk
    obtain ⟨j, hj⟩ := complete k m hm
    exact ⟨j, by simp [hj]⟩
  have := Nat.nth_comp_of_strictMono (p := P) (n := n) q_strictMono h0
    (fun hf => absurd hf hinf)
  have h2 : Nat.nth (fun i => P (pr i).1) n = n := Nat.nth_of_forall (fun i _ => hP i)
  rw [h2] at this
  exact this.symm

theorem a_eq (n : ℕ) : a n = (pr (n - 1)).1 := by
  unfold a
  exact nth_eq _

theorem q_rec (j : ℕ) : (pr (j + 4)).1 + (pr j).1 = 6 * (pr (j + 2)).1 + 2 := by
  rw [show j + 4 = (j + 2) + 2 by omega, pr_add_two, pr_add_two]
  dsimp only
  omega

theorem trace (n : ℕ) (hn : 0 < n) :
    (a (n + 4) : ℤ) = 6 * a (n + 2) - a n + 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simp only [a_eq, show j + 1 + 4 - 1 = j + 4 by omega,
    show j + 1 + 2 - 1 = j + 2 by omega, show j + 1 - 1 = j by omega]
  have h := q_rec j
  omega

theorem initial : a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 12 ∧ a 4 = 22 := by
  simp only [a_eq]
  decide

end PellTriangles

open OMA.S_oeis_a154138 PowerSeries

private theorem pellFinish
    (h : ∀ n : ℕ, 0 < n → (a (n+4) : ℤ) = 6 * a (n+2) - a n + 2)
    (h1 : a 1 = 1) (h2 : a 2 = 3) (h3 : a 3 = 12) (h4 : a 4 = 22) :
    type_of% @OMA.S_oeis_a154138.main := by
  have recn (n : ℕ) (hn : 5 < n) : (a n : ℤ) =
      a (n-1) + 6 * a (n-2) - 6 * a (n-3) - a (n-4) + a (n-5) := by
    have h0 := h (n-5) (by omega)
    have h1' := h (n-4) (by omega)
    rw [show n-5+4 = n-1 by omega, show n-5+2 = n-3 by omega] at h0
    rw [show n-4+4 = n by omega, show n-4+2 = n-2 by omega] at h1'
    linarith
  refine ⟨recn, ?_⟩
  let A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  change A * _ = _
  rw [show A * ((1-X)*(X^2-2*X-1)*(X^2+2*X-1)) =
      A - A * X^1 - C 6 * (A * X^2) + C 6 * (A * X^3) + A * X^4 - A * X^5 by
        simp only [map_ofNat]; ring]
  rw [show (X : ℚ⟦X⟧) * (1+2*X+3*X^2-2*X^3-2*X^4) =
      X^1 + C 2 * X^2 + C 3 * X^3 - C 2 * X^4 - C 2 * X^5 by
        simp only [map_ofNat]; ring]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, A, coeff_mk]
  by_cases hn : n ≤ 5
  · have h5i := h 1 (by decide)
    norm_num [h1, h3] at h5i
    have h5 : a 5 = 73 := by exact_mod_cast h5i
    interval_cases n <;> norm_num [h1, h2, h3, h4, h5]
  · have r : (a n : ℚ) = a (n-1) + 6 * a (n-2) - 6 * a (n-3) - a (n-4) + a (n-5) := by
      exact_mod_cast recn n (by omega)
    simp (disch := omega) only [coeff_C, if_pos, if_neg, add_zero, sub_zero]
    linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a154138.main := by
  obtain ⟨h1, h2, h3, h4⟩ := PellTriangles.initial
  exact pellFinish PellTriangles.trace h1 h2 h3 h4
