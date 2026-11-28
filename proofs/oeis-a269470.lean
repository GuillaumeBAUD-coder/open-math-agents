import OMAStatements.S_oeis_a269470

-- Credit: @mjsechrest2

namespace OMA.P_oeis_a269470

open OMA.S_oeis_a269470

private def goodFrom (cur : ℕ) (lastRep : Option ℕ) : List ℕ → Bool
  | [] => true
  | x :: xs =>
    if x = cur then
      match lastRep with
      | none => goodFrom x (some x) xs
      | some r => if x = r then false else goodFrom x (some x) xs
    else
      goodFrom x lastRep xs

private def chainFrom : Option ℕ → List ℕ → Bool
  | _, [] => true
  | none, r :: t => chainFrom (some r) t
  | some p, r :: t => decide (p ≠ r) && chainFrom (some r) t

private lemma goodFrom_eq_chainFrom (xs : List ℕ) :
    ∀ cur lastRep, goodFrom cur lastRep xs = chainFrom lastRep (repVals (cur :: xs)) := by
  induction xs with
  | nil =>
    intro cur lastRep
    simp [goodFrom, repVals, chainFrom]
  | cons x xs ih =>
    intro cur lastRep
    simp only [goodFrom, repVals]
    split_ifs with h
    · cases lastRep with
      | none =>
        simp only [List.singleton_append, chainFrom]
        exact ih x (some x)
      | some r =>
        simp only [List.singleton_append, chainFrom]
        by_cases hxr : x = r
        · simp [hxr]
        · have hrne : r ≠ x := Ne.symm hxr
          simp [hxr, hrne, ih x (some x)]
    · simp only [List.nil_append]
      exact ih x lastRep

private lemma chainFrom_some_iff (p : ℕ) (rv : List ℕ) :
    chainFrom (some p) rv = true ↔ (p :: rv).IsChain (· ≠ ·) := by
  induction rv generalizing p with
  | nil => simp [chainFrom]
  | cons r t ih =>
    simp [chainFrom, ih]

private lemma chainFrom_none_iff (rv : List ℕ) :
    chainFrom none rv = true ↔ rv.IsChain (· ≠ ·) := by
  cases rv with
  | nil => simp [chainFrom]
  | cons r t =>
    simp [chainFrom, chainFrom_some_iff]

private def countGood (n : ℕ) : ℕ → ℕ → Option ℕ → ℕ
  | 0, _, _ => 1
  | k + 1, cur, lastRep =>
    ∑ x ∈ Finset.range (n + 1),
      if x = cur then
        match lastRep with
        | none => countGood n k x (some x)
        | some r => if x = r then 0 else countGood n k x (some x)
      else
        countGood n k x lastRep

private lemma card_filter_goodFrom (n k : ℕ) :
    ∀ cur lastRep,
      ((Fintype.piFinset fun _ : Fin k => Finset.range (n + 1)).filter
        (fun v => goodFrom cur lastRep (List.ofFn v) = true)).card =
      countGood n k cur lastRep := by
  induction k with
  | zero =>
    intro cur lastRep
    have h1 : (Fintype.piFinset fun _ : Fin 0 => Finset.range (n + 1)) = {default} := by
      ext v
      exact ⟨fun _ => Finset.mem_singleton.mpr (Subsingleton.elim v default),
        fun _ => Fintype.mem_piFinset.mpr fun i => Fin.elim0 i⟩
    rw [h1]
    simp [goodFrom, countGood]
  | succ k ih =>
    intro cur lastRep
    let S := (Fintype.piFinset fun _ : Fin (k + 1) => Finset.range (n + 1)).filter
      (fun v => goodFrom cur lastRep (List.ofFn v) = true)
    have hpart : S.card = ∑ x ∈ Finset.range (n + 1), (S.filter (fun v => v 0 = x)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext v
        simp only [Finset.mem_biUnion, Finset.mem_filter, S, Fintype.mem_piFinset]
        exact ⟨fun hv => ⟨v 0, hv.1 0, hv, rfl⟩, fun ⟨_, _, hv, _⟩ => hv⟩
      · intro x _ y _ hxy
        exact Finset.disjoint_left.mpr fun v hv1 hv2 =>
          hxy ((Finset.mem_filter.mp hv1).2.symm.trans (Finset.mem_filter.mp hv2).2)
    rw [hpart]
    simp only [countGood]
    apply Finset.sum_congr rfl
    intro x hx
    have hfiber :
        (S.filter (fun v => v 0 = x)).card =
        ((Fintype.piFinset fun _ : Fin k => Finset.range (n + 1)).filter
          (fun w => goodFrom cur lastRep (x :: List.ofFn w) = true)).card := by
      refine Finset.card_bij (fun v _ => fun i : Fin k => v i.succ) ?_ ?_ ?_
      · intro v hv
        simp only [Finset.mem_filter, S, Fintype.mem_piFinset] at hv ⊢
        refine ⟨fun i => hv.1.1 i.succ, ?_⟩
        have hof : List.ofFn v = x :: List.ofFn (fun i : Fin k => v i.succ) := by
          rw [List.ofFn_succ, hv.2]
        rw [← hof]
        exact hv.1.2
      · intro v₁ hv₁ v₂ hv₂ heq
        simp only [Finset.mem_filter] at hv₁ hv₂
        funext i
        refine Fin.cases ?_ (fun j => congr_fun heq j) i
        exact hv₁.2.trans hv₂.2.symm
      · intro w hw
        simp only [Finset.mem_filter, Fintype.mem_piFinset] at hw
        refine ⟨Fin.cons x w, ?_, by funext i; simp⟩
        simp only [Finset.mem_filter, S, Fintype.mem_piFinset, Fin.cons_zero]
        refine ⟨⟨fun i => Fin.cases hx (fun j => hw.1 j) i, ?_⟩, trivial⟩
        rw [List.ofFn_succ, Fin.cons_zero]
        simpa using hw.2
    rw [hfiber]
    simp only [goodFrom]
    split_ifs with hxc
    · cases lastRep with
      | none => exact ih x (some x)
      | some r =>
        dsimp only
        split_ifs with hxr
        · simp
        · exact ih x (some x)
    · exact ih x lastRep

private def dpA (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => dpE n k + n * dpA n k
where
  dpE (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => n * dpC n k
  dpC (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * dpE n k + (n - 1) * dpC n k

private lemma countGood_eq_dp (n k : ℕ) :
    (∀ cur ∈ Finset.range (n + 1), countGood n k cur none = dpA n k) ∧
    (∀ cur ∈ Finset.range (n + 1), countGood n k cur (some cur) = dpA.dpE n k) ∧
    (∀ cur ∈ Finset.range (n + 1), ∀ r ∈ Finset.range (n + 1), cur ≠ r →
      countGood n k cur (some r) = dpA.dpC n k) := by
  induction k with
  | zero =>
    refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  | succ k ih =>
    rcases ih with ⟨ihA, ihE, ihC⟩
    refine ⟨?_, ?_, ?_⟩
    · intro cur hcur
      simp only [countGood, dpA]
      rw [← Finset.add_sum_erase _ _ hcur]
      simp only [↓reduceIte]
      rw [ihE cur hcur]
      have hsum :
          ∑ x ∈ (Finset.range (n + 1)).erase cur,
            (if x = cur then countGood n k x (some x) else countGood n k x none) =
          ∑ _x ∈ (Finset.range (n + 1)).erase cur, dpA n k := by
        apply Finset.sum_congr rfl
        intro x hx
        have hne : x ≠ cur := (Finset.mem_erase.mp hx).1
        rw [if_neg hne, ihA x (Finset.mem_erase.mp hx).2]
      rw [hsum, Finset.sum_const, Finset.card_erase_of_mem hcur, Finset.card_range]
      simp
    · intro cur hcur
      simp only [countGood, dpA.dpE]
      rw [← Finset.add_sum_erase _ _ hcur]
      simp only [↓reduceIte, zero_add]
      have hsum :
          ∑ x ∈ (Finset.range (n + 1)).erase cur,
            (if x = cur then if x = cur then 0 else countGood n k x (some x)
             else countGood n k x (some cur)) =
          ∑ _x ∈ (Finset.range (n + 1)).erase cur, dpA.dpC n k := by
        apply Finset.sum_congr rfl
        intro x hx
        have hne : x ≠ cur := (Finset.mem_erase.mp hx).1
        rw [if_neg hne, ihC x (Finset.mem_erase.mp hx).2 cur hcur hne]
      rw [hsum, Finset.sum_const, Finset.card_erase_of_mem hcur, Finset.card_range]
      simp
    · intro cur hcur r hr hne
      simp only [countGood, dpA.dpC]
      rw [← Finset.add_sum_erase _ _ hcur]
      simp only [↓reduceIte, if_neg hne]
      rw [ihE cur hcur]
      have hr_er : r ∈ (Finset.range (n + 1)).erase cur := Finset.mem_erase.mpr ⟨hne.symm, hr⟩
      rw [← Finset.add_sum_erase _ _ hr_er]
      have hne2 : r ≠ cur := hne.symm
      rw [if_neg hne2, ihE r hr]
      have hsum :
          ∑ x ∈ ((Finset.range (n + 1)).erase cur).erase r,
            (if x = cur then if x = r then 0 else countGood n k x (some x)
             else countGood n k x (some r)) =
          ∑ _x ∈ ((Finset.range (n + 1)).erase cur).erase r, dpA.dpC n k := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxr : x ≠ r := (Finset.mem_erase.mp hx).1
        have hx1 := Finset.mem_erase.mp (Finset.mem_erase.mp hx).2
        rw [if_neg hx1.1, ihC x hx1.2 r hr hxr]
      rw [hsum, Finset.sum_const, Finset.card_erase_of_mem hr_er, Finset.card_erase_of_mem hcur,
        Finset.card_range]
      simp only [Nat.add_sub_cancel, smul_eq_mul]
      ring

private lemma a_eq_dp (n : ℕ) : a n = (n + 1) * dpA n 5 := by
  unfold a
  let S := (Fintype.piFinset fun _ : Fin 6 => Finset.range (n + 1)).filter
    (fun v => (repVals (List.ofFn v)).IsChain (· ≠ ·))
  have hpart : S.card = ∑ x ∈ Finset.range (n + 1), (S.filter (fun v => v 0 = x)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_filter, S, Fintype.mem_piFinset]
      exact ⟨fun hv => ⟨v 0, hv.1 0, hv, rfl⟩, fun ⟨_, _, hv, _⟩ => hv⟩
    · intro x _ y _ hxy
      exact Finset.disjoint_left.mpr fun v hv1 hv2 =>
        hxy ((Finset.mem_filter.mp hv1).2.symm.trans (Finset.mem_filter.mp hv2).2)
  change S.card = _
  rw [hpart]
  have hterm : ∀ x ∈ Finset.range (n + 1), (S.filter (fun v => v 0 = x)).card = dpA n 5 := by
    intro x hx
    have hfiber :
        (S.filter (fun v => v 0 = x)).card =
        ((Fintype.piFinset fun _ : Fin 5 => Finset.range (n + 1)).filter
          (fun w => goodFrom x none (List.ofFn w) = true)).card := by
      refine Finset.card_bij (fun v _ => fun i : Fin 5 => v i.succ) ?_ ?_ ?_
      · intro v hv
        simp only [Finset.mem_filter, S, Fintype.mem_piFinset] at hv ⊢
        refine ⟨fun i => hv.1.1 i.succ, ?_⟩
        rw [goodFrom_eq_chainFrom, chainFrom_none_iff]
        have hof : List.ofFn v = x :: List.ofFn (fun i : Fin 5 => v i.succ) := by
          rw [List.ofFn_succ, hv.2]
        rw [← hof]
        exact hv.1.2
      · intro v₁ hv₁ v₂ hv₂ heq
        simp only [Finset.mem_filter] at hv₁ hv₂
        funext i
        refine Fin.cases ?_ (fun j => congr_fun heq j) i
        exact hv₁.2.trans hv₂.2.symm
      · intro w hw
        simp only [Finset.mem_filter, Fintype.mem_piFinset] at hw
        refine ⟨Fin.cons x w, ?_, by funext i; simp⟩
        simp only [Finset.mem_filter, S, Fintype.mem_piFinset, Fin.cons_zero]
        refine ⟨⟨fun i => Fin.cases hx (fun j => hw.1 j) i, ?_⟩, trivial⟩
        rw [List.ofFn_succ, Fin.cons_zero]
        have := hw.2
        rw [goodFrom_eq_chainFrom, chainFrom_none_iff] at this
        simpa using this
    rw [hfiber, card_filter_goodFrom, (countGood_eq_dp n 5).1 x hx]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, smul_eq_mul]

private lemma a_poly (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) =
      (n : ℚ) ^ 6 + 6 * (n : ℚ) ^ 5 + 11 * (n : ℚ) ^ 4 + 4 * (n : ℚ) ^ 3 -
        (n : ℚ) ^ 2 + (n : ℚ) := by
  rw [a_eq_dp]
  simp only [dpA, dpA.dpE, dpA.dpC]
  have hsub : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub hn]; simp
  push_cast
  rw [hsub]
  ring

private lemma coeff_lhs (n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.mk fun k => (a k : ℚ)) * (1 - PowerSeries.X) ^ 7) =
      (a n : ℚ)
        - (if 1 ≤ n then 7 * (a (n - 1) : ℚ) else 0)
        + (if 2 ≤ n then 21 * (a (n - 2) : ℚ) else 0)
        - (if 3 ≤ n then 35 * (a (n - 3) : ℚ) else 0)
        + (if 4 ≤ n then 35 * (a (n - 4) : ℚ) else 0)
        - (if 5 ≤ n then 21 * (a (n - 5) : ℚ) else 0)
        + (if 6 ≤ n then 7 * (a (n - 6) : ℚ) else 0)
        - (if 7 ≤ n then (a (n - 7) : ℚ) else 0) := by
  have hpoly : ((1 - PowerSeries.X : PowerSeries ℚ) ^ 7) =
      1 - PowerSeries.C 7 * PowerSeries.X + PowerSeries.C 21 * PowerSeries.X ^ 2 -
        PowerSeries.C 35 * PowerSeries.X ^ 3 + PowerSeries.C 35 * PowerSeries.X ^ 4 -
        PowerSeries.C 21 * PowerSeries.X ^ 5 + PowerSeries.C 7 * PowerSeries.X ^ 6 -
        PowerSeries.X ^ 7 := by
    simp only [map_ofNat]; ring
  rw [hpoly]
  have hc (c : ℚ) (k : ℕ) :
      PowerSeries.coeff n ((PowerSeries.mk fun m => (a m : ℚ)) * (PowerSeries.C c * PowerSeries.X ^ k)) =
        if k ≤ n then c * (a (n - k) : ℚ) else 0 := by
    rw [mul_left_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
    split_ifs <;> simp
  have hc1 (k : ℕ) :
      PowerSeries.coeff n ((PowerSeries.mk fun m => (a m : ℚ)) * PowerSeries.X ^ k) =
        if k ≤ n then (a (n - k) : ℚ) else 0 := by
    rw [PowerSeries.coeff_mul_X_pow']
    split_ifs <;> simp
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, PowerSeries.coeff_mk,
    show PowerSeries.C (7 : ℚ) * PowerSeries.X = PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 1 by simp,
    hc, hc1]

end OMA.P_oeis_a269470

theorem OMA.solution : type_of% @OMA.S_oeis_a269470.main := by
  open OMA.S_oeis_a269470 OMA.P_oeis_a269470 PowerSeries in
  ext n
  rw [coeff_lhs]
  have hrhs :
      (2 * X * (11 + 154 * X + 204 * X ^ 2 - 14 * X ^ 3 + 5 * X ^ 4) : PowerSeries ℚ) =
      C 22 * X ^ 1 + C 308 * X ^ 2 + C 408 * X ^ 3 - C 28 * X ^ 4 + C 10 * X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [hrhs]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow]
  by_cases hn : 8 ≤ n
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    rw [a_poly n (by omega), a_poly (n - 1) (by omega), a_poly (n - 2) (by omega),
      a_poly (n - 3) (by omega), a_poly (n - 4) (by omega), a_poly (n - 5) (by omega),
      a_poly (n - 6) (by omega), a_poly (n - 7) (by omega)]
    have h1 : n ≠ 1 := by omega
    have h2 : n ≠ 2 := by omega
    have h3 : n ≠ 3 := by omega
    have h4 : n ≠ 4 := by omega
    have h5 : n ≠ 5 := by omega
    simp only [h1, h2, h3, h4, h5, ↓reduceIte, mul_zero, add_zero, sub_zero]
    rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
      Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega),
      Nat.cast_sub (show 5 ≤ n by omega), Nat.cast_sub (show 6 ≤ n by omega),
      Nat.cast_sub (show 7 ≤ n by omega)]
    push_cast
    ring
  · have ha0 : a 0 = 0 := by rw [a_eq_dp]; decide
    have ha1 : a 1 = 22 := by rw [a_eq_dp]; decide
    have ha2 : a 2 = 462 := by rw [a_eq_dp]; decide
    have ha3 : a 3 = 3180 := by rw [a_eq_dp]; decide
    have ha4 : a 4 = 13300 := by rw [a_eq_dp]; decide
    have ha5 : a 5 = 41730 := by rw [a_eq_dp]; decide
    have ha6 : a 6 = 108402 := by rw [a_eq_dp]; decide
    have ha7 : a 7 = 246232 := by rw [a_eq_dp]; decide
    interval_cases n <;> simp [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7] <;> norm_num
