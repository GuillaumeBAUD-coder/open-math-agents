import OMAStatements.S_oeis_a269470

/-!
Proof of the g.f. of OEIS A269470.

Scan the array from the left, remembering the last value u and the last repeated value r (if any).
The number of admissible continuations of length m depends only on whether r is absent, equal to u,
or different from u; these counts A, B, D satisfy A' = B + n A, B' = n D, D' = 2 B + (n - 1) D.
So a(n) = (n + 1) A(5, n), an explicit polynomial, and the g.f. follows.
-/

namespace A269470Proof

open OMA.S_oeis_a269470 Finset

/-- The condition on a continuation l after the last value u, with last repeated value r. -/
def Good (u : ℕ) (r : Option ℕ) (l : List ℕ) : Prop :=
  (r.toList ++ repVals (u :: l)).IsChain (· ≠ ·)

instance (u : ℕ) (r : Option ℕ) (l : List ℕ) : Decidable (Good u r l) := by
  unfold Good; infer_instance

theorem good_nil (u : ℕ) (r : Option ℕ) : Good u r [] := by
  cases r <;> simp [Good, repVals]

theorem good_cons (u v : ℕ) (r : Option ℕ) (l : List ℕ) :
    Good u r (v :: l) ↔ (v = u → r ≠ some u) ∧ Good v (if v = u then some u else r) l := by
  unfold Good
  rw [show repVals (u :: v :: l) = (if v = u then [v] else []) ++ repVals (v :: l) from rfl]
  by_cases h : v = u
  · subst h
    simp only [if_true, List.singleton_append]
    cases r with
    | none => simp
    | some w =>
      simp only [Option.toList_some, List.singleton_append, List.isChain_cons_cons, ne_eq,
        Option.some.injEq]
      tauto
  · simp [h]

/-- Arrays of length m over 0..n. -/
abbrev W (n m : ℕ) : Finset (Fin m → ℕ) := Fintype.piFinset fun _ : Fin m => range (n + 1)

theorem sum_W_succ (n m : ℕ) (f : (Fin (m + 1) → ℕ) → ℤ) :
    (∑ y ∈ W n (m + 1), f y) = ∑ v ∈ range (n + 1), ∑ z ∈ W n m, f (Fin.cons v z) := by
  have h := Finset.filter_piFinset_eq_map_consEquiv (fun _ : Fin (m + 1) => range (n + 1))
    (fun _ => True)
  simp only [Finset.filter_true] at h
  rw [show W n (m + 1) = _ from h, Finset.sum_map, ← Finset.sum_product']
  rfl

/-- The number of admissible continuations of length m. -/
def Cnt (n m u : ℕ) (r : Option ℕ) : ℤ :=
  ∑ y ∈ W n m, if Good u r (List.ofFn y) then 1 else 0

theorem Cnt_zero (n u : ℕ) (r : Option ℕ) : Cnt n 0 u r = 1 := by
  simp [Cnt, good_nil]

theorem ofFn_cons {m : ℕ} (v : ℕ) (z : Fin m → ℕ) :
    List.ofFn (Fin.cons v z : Fin (m + 1) → ℕ) = v :: List.ofFn z := by
  simp [List.ofFn_succ]

theorem Cnt_succ (n m u : ℕ) (r : Option ℕ) :
    Cnt n (m + 1) u r = ∑ v ∈ range (n + 1),
      if (v = u → r ≠ some u) then Cnt n m v (if v = u then some u else r) else 0 := by
  unfold Cnt
  rw [sum_W_succ]
  apply Finset.sum_congr rfl
  intro v _
  simp only [ofFn_cons, good_cons]
  by_cases h : (v = u → r ≠ some u)
  · rw [if_pos h]
    apply Finset.sum_congr rfl
    intro z _
    exact if_congr (and_iff_right h) rfl rfl
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro z _
    exact if_neg (fun hh => h hh.1)

/-- The lumped counts (A, B, D) of continuations of length m. -/
def T3 : ℕ → ℤ → ℤ × ℤ × ℤ
  | 0, _ => (1, 1, 1)
  | m + 1, n => ((T3 m n).2.1 + n * (T3 m n).1, n * (T3 m n).2.2,
      2 * (T3 m n).2.1 + (n - 1) * (T3 m n).2.2)

theorem sum_erase_const (s : Finset ℕ) (u : ℕ) (f : ℕ → ℤ) (c : ℤ)
    (h : ∀ v ∈ s, v ≠ u → f v = c) : (∑ v ∈ s.erase u, f v) = ((s.erase u).card : ℤ) * c := by
  rw [Finset.sum_congr rfl (fun v hv => h v (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv)),
    Finset.sum_const, nsmul_eq_mul]

theorem lumped (n m : ℕ) :
    (∀ u, u ≤ n → Cnt n m u none = (T3 m n).1) ∧
    (∀ u, u ≤ n → Cnt n m u (some u) = (T3 m n).2.1) ∧
    (∀ u w, u ≤ n → w ≤ n → w ≠ u → Cnt n m u (some w) = (T3 m n).2.2) := by
  induction m with
  | zero => exact ⟨fun _ _ => Cnt_zero _ _ _, fun _ _ => Cnt_zero _ _ _, fun _ _ _ _ _ => Cnt_zero _ _ _⟩
  | succ m ih =>
    obtain ⟨iA, iB, iD⟩ := ih
    refine ⟨fun u hu => ?_, fun u hu => ?_, fun u w hu hw hwu => ?_⟩
    · rw [Cnt_succ]
      have hu' : u ∈ range (n + 1) := Finset.mem_range.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ hu']
      simp only [if_true, ne_eq, reduceCtorEq, not_false_eq_true, imp_true_iff]
      rw [iB u hu]
      rw [sum_erase_const _ u _ (T3 m n).1 (fun v hv hvu => by
        rw [if_neg hvu, iA v (by simp at hv; omega)])]
      rw [Finset.card_erase_of_mem hu', Finset.card_range]
      simp only [T3]
      push_cast
      ring
    · rw [Cnt_succ]
      have hu' : u ∈ range (n + 1) := Finset.mem_range.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ hu']
      simp only [if_true, ne_eq, not_true_eq_false, imp_false, not_not]
      rw [sum_erase_const _ u _ (T3 m n).2.2 (fun v hv hvu => by
        rw [if_pos hvu, if_neg hvu, iD v u (by simp at hv; omega) hu (Ne.symm hvu)])]
      rw [Finset.card_erase_of_mem hu', Finset.card_range]
      simp only [T3]
      push_cast
      ring
    · rw [Cnt_succ]
      have hu' : u ∈ range (n + 1) := Finset.mem_range.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ hu']
      have hne : (some w ≠ some u) := fun h => hwu (Option.some.inj h)
      rw [if_pos (fun _ => hne), if_pos rfl, iB u hu]
      have hw' : w ∈ (range (n + 1)).erase u :=
        Finset.mem_erase.mpr ⟨hwu, Finset.mem_range.mpr (by omega)⟩
      rw [← Finset.add_sum_erase _ _ hw']
      rw [if_pos (fun h => absurd h hwu), if_neg hwu, iB w hw]
      rw [sum_erase_const _ w _ (T3 m n).2.2 (fun v hv hvw => by
        have hvu : v ≠ u := Finset.ne_of_mem_erase hv
        have hvn : v ≤ n := by
          have := Finset.mem_of_mem_erase hv
          simp at this; omega
        rw [if_pos (fun h => absurd h hvu), if_neg hvu, iD v w hvn hw (Ne.symm hvw)])]
      rw [Finset.card_erase_of_mem hw', Finset.card_erase_of_mem hu', Finset.card_range]
      have hn : 1 ≤ n := by omega
      simp only [T3]
      rw [show n + 1 - 1 - 1 = n - 1 by omega]
      push_cast [Nat.cast_sub hn]
      ring

theorem a_eq (n : ℕ) : (a n : ℤ) = (n + 1) * (T3 5 n).1 := by
  have h1 : (a n : ℤ) = ∑ y ∈ W n 6, if (repVals (List.ofFn y)).IsChain (· ≠ ·) then 1 else 0 := by
    rw [a, Finset.card_filter]
    push_cast
    rfl
  rw [h1, sum_W_succ]
  have h2 : ∀ v ∈ range (n + 1), (∑ z ∈ W n 5,
      (if (repVals (List.ofFn (Fin.cons v z : Fin 6 → ℕ))).IsChain (· ≠ ·) then (1 : ℤ) else 0)) =
      (T3 5 n).1 := by
    intro v hv
    have := (lumped n 5).1 v (by simp at hv; omega)
    rw [← this, Cnt]
    apply Finset.sum_congr rfl
    intro z _
    simp only [ofFn_cons, Good, Option.toList_none, List.nil_append]
    exact if_congr Iff.rfl rfl rfl
  rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

theorem a_poly (n : ℕ) : (a n : ℚ) = 1 * (n : ℚ) ^ 1 - 1 * (n : ℚ) ^ 2 + 4 * (n : ℚ) ^ 3 + 11 * (n : ℚ) ^ 4 + 6 * (n : ℚ) ^ 5 + 1 * (n : ℚ) ^ 6 := by
  have h := a_eq n
  simp only [T3] at h
  have h' := congrArg (Int.cast : ℤ → ℚ) h
  push_cast at h'
  rw [h']
  ring

open PowerSeries in
theorem gf : (PowerSeries.mk fun n => (a n : ℚ)) * (1 - X) ^ 7 = 2 * X * (11 + 154 * X + 204 * X ^ 2 - 14 * X ^ 3 + 5 * X ^ 4) := by
  have hd : ((1 - X) ^ 7 : PowerSeries ℚ) = 1 - C 7 * X ^ 1 + C 21 * X ^ 2 - C 35 * X ^ 3 + C 35 * X ^ 4 - C 21 * X ^ 5 + C 7 * X ^ 6 - X ^ 7 := by
    simp only [map_ofNat]
    ring
  have hq : (2 * X * (11 + 154 * X + 204 * X ^ 2 - 14 * X ^ 3 + 5 * X ^ 4) : PowerSeries ℚ) = C 22 * X ^ 1 + C 308 * X ^ 2 + C 408 * X ^ 3 - C 28 * X ^ 4 + C 10 * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [hd, hq, mul_comm]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_one]
  by_cases hn : n < 7
  · interval_cases n <;> norm_num [a_poly]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simp only [if_pos (show 1 ≤ m + 7 by omega), if_pos (show 2 ≤ m + 7 by omega), if_pos (show 3 ≤ m + 7 by omega), if_pos (show 4 ≤ m + 7 by omega), if_pos (show 5 ≤ m + 7 by omega), if_pos (show 6 ≤ m + 7 by omega), if_pos (show 7 ≤ m + 7 by omega), if_neg (show m + 7 ≠ 0 by omega), if_neg (show m + 7 ≠ 1 by omega), if_neg (show m + 7 ≠ 2 by omega), if_neg (show m + 7 ≠ 3 by omega), if_neg (show m + 7 ≠ 4 by omega), if_neg (show m + 7 ≠ 5 by omega)]
    rw [show m + 7 - 1 = m + 6 by omega]
    rw [show m + 7 - 2 = m + 5 by omega]
    rw [show m + 7 - 3 = m + 4 by omega]
    rw [show m + 7 - 4 = m + 3 by omega]
    rw [show m + 7 - 5 = m + 2 by omega]
    rw [show m + 7 - 6 = m + 1 by omega]
    rw [show m + 7 - 7 = m + 0 by omega]
    rw [a_poly (m + 7), a_poly (m + 6), a_poly (m + 5), a_poly (m + 4), a_poly (m + 3), a_poly (m + 2), a_poly (m + 1), a_poly (m + 0)]
    push_cast
    ring

end A269470Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a269470.main := A269470Proof.gf
