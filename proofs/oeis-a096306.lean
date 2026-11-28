import OMAStatements.S_oeis_a096306

namespace DigitSync
open OMA.S_oeis_a096306

private def small (t : ℕ) := t + max ((Nat.digits 10 t).foldl max 0) 1

private lemma fold_le (ds : List ℕ) (x b : ℕ) :
    ds.foldl max x ≤ b ↔ x ≤ b ∧ ∀ d ∈ ds, d ≤ b := by
  induction ds generalizing x with
  | nil => simp
  | cons d ds ih => simp [ih, max_le_iff, and_assoc]

private lemma step_bounds (n : ℕ) (hn : 0 < n) : n < step n ∧ step n ≤ n + 9 := by
  let ds := Nat.digits 10 n
  have hp : 0 < ds.foldl max 0 := by
    apply Nat.pos_of_ne_zero
    intro hz
    have h := ((fold_le ds 0 0).mp hz.le).2 _
      (List.getLast_mem (Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne'))
    exact Nat.getLast_digit_ne_zero 10 hn.ne' (Nat.eq_zero_of_le_zero h)
  have hl := (fold_le ds 0 9).mpr
    ⟨by decide, fun d hd => Nat.le_of_lt_succ (Nat.digits_lt_base (by decide : 1 < 10) hd)⟩
  change n < n + ds.foldl max 0 ∧ n + ds.foldl max 0 ≤ n + 9
  omega

private lemma zeros (k x : ℕ) : (List.replicate k 0).foldl max x = x := by
  induction k <;> simp [List.replicate_succ, *]

private lemma translate (k t : ℕ) (hk : 3 ≤ k) (ht : t ≤ 101) :
    step (10 ^ k + t) = 10 ^ k + small t := by
  have len : (Nat.digits 10 t).length ≤ 3 :=
    (Nat.digits_length_le_iff (by decide) t).mpr (by norm_num; omega)
  have h := Nat.digits_append_zeroes_append_digits (b := 10) (n := t) (m := 1)
    (k := k - (Nat.digits 10 t).length) (by decide) (by decide)
  rw [show (Nat.digits 10 t).length + (k - (Nat.digits 10 t).length) = k by omega,
    Nat.mul_one, Nat.add_comm t] at h
  unfold step small
  rw [← h, List.foldl_append, List.foldl_append, zeros]
  simp [Nat.add_assoc]

private lemma cross (B n : ℕ) (hn : 0 < n) (hB : n < B + 9) :
    ∃ j : ℕ, B ≤ step^[j] n ∧ step^[j] n < B + 9 := by
  by_cases h : B ≤ n
  · exact ⟨0, h, hB⟩
  · have b := step_bounds n hn
    obtain ⟨j, hj, hj'⟩ := cross B (step n) (by omega) (by omega)
    exact ⟨j + 1, by simpa only [Function.iterate_succ_apply] using And.intro hj hj'⟩
termination_by B - n
decreasing_by omega

private lemma shifted (k t j : ℕ) (hk : 3 ≤ k) (h : small^[j] t ≤ 101) :
    step^[j] (10 ^ k + t) = 10 ^ k + small^[j] t := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply'] at h ⊢
    have le : small^[j] t ≤ 101 := (Nat.le_add_right _ _).trans h
    rw [ih le, translate k _ hk le, Function.iterate_succ_apply']

private lemma finite_sync (t : Fin 9) : ∃ j : ℕ, small^[j] t.val = 101 := by
  exact ⟨![19, 18, 17, 18, 16, 19, 17, 16, 15] t, by fin_cases t <;> decide⟩

private lemma meet (k n : ℕ) (hk : 3 ≤ k) (hn : 0 < n) (hn' : n ≤ 10 ^ k) :
    ∃ m : ℕ, step^[m] n = 10 ^ k + 101 := by
  obtain ⟨j, lo, hi⟩ := cross (10 ^ k) n hn (by omega)
  let t : Fin 9 := ⟨step^[j] n - 10 ^ k, by omega⟩
  have eq : step^[j] n = 10 ^ k + t.val := by dsimp [t]; omega
  obtain ⟨i, hit⟩ := finite_sync t
  exact ⟨i + j, by rw [Function.iterate_add_apply, eq, shifted k _ i hk (by rw [hit]), hit]⟩

end DigitSync

open DigitSync

theorem OMA.solution : type_of% @OMA.S_oeis_a096306.main := by
  intro n hn
  let k := n + 3
  have hk : 3 ≤ k := by dsimp [k]; omega
  have big : k < 10 ^ k := Nat.lt_pow_self (by decide)
  obtain ⟨i, hi⟩ := meet k n hk hn (by dsimp [k] at big ⊢; omega)
  obtain ⟨j, hj⟩ := meet k 1 hk (by decide) (by omega)
  exact ⟨i, j, hi.trans hj.symm⟩
