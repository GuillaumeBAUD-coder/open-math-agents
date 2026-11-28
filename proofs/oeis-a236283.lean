import OMAStatements.S_oeis_a236283

namespace A236283P
open MulAction OMA.S_oeis_a236283 DihedralGroup

lemma two_unit (n : ℕ) (h : Odd n) : IsUnit (2 : ZMod n) := by
  have := (ZMod.isUnit_iff_coprime 2 n).mpr (Nat.coprime_two_left.mpr h)
  simpa using this

lemma half_cases (t : ℕ) (ht : 0 < t) (y : ZMod (t + t)) (hy : 2 * y = 0) :
    y = 0 ∨ y = (t : ZMod (t + t)) := by
  haveI : NeZero (t + t) := ⟨by omega⟩
  have hv := ZMod.natCast_zmod_val y
  have h2 : ((2 * y.val : ℕ) : ZMod (t + t)) = 0 := by
    push_cast
    rw [hv]
    exact hy
  rw [ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨c, hc⟩ := h2
  have hlt := ZMod.val_lt y
  have hc2 : c < 2 := by nlinarith
  interval_cases c
  · left
    rw [← hv, show y.val = 0 by omega]
    simp
  · right
    rw [← hv, show y.val = t by omega]

lemma cardT (n : ℕ) [NeZero n] :
    Nat.card {y : ZMod n // 2 * y = 0} = if Even n then 2 else 1 := by
  split_ifs with h
  · obtain ⟨t, rfl⟩ := h
    have ht : 0 < t := by
      have := NeZero.pos (t + t)
      omega
    rw [Nat.card_eq_two_iff]
    have htz : 2 * (t : ZMod (t + t)) = 0 := by
      rw [show (2 : ZMod (t + t)) * t = ((t + t : ℕ) : ZMod (t + t)) by push_cast; ring]
      exact ZMod.natCast_self _
    refine ⟨⟨0, by simp⟩, ⟨(t : ZMod (t + t)), htz⟩, ?_, ?_⟩
    · intro e
      have e2 := congrArg (fun z : {y : ZMod (t + t) // 2 * y = 0} => ZMod.val z.1) e
      simp only [ZMod.val_zero] at e2
      rw [ZMod.val_cast_of_lt (by omega)] at e2
      omega
    · ext ⟨y, hy⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true,
        Subtype.ext_iff]
      exact half_cases t ht y hy
  · have hu := two_unit n (Nat.not_even_iff_odd.mp h)
    have h0 : ∀ y : {y : ZMod n // 2 * y = 0}, y.1 = 0 := fun y => hu.mul_right_eq_zero.mp y.2
    exact Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun a b => Subtype.ext (by rw [h0 a, h0 b])⟩, ⟨⟨0, by simp⟩⟩⟩

lemma smul_apply_r (n k : ℕ) (i : ZMod n) (x : Fin k → ZMod n) (j : Fin k) :
    (r i • x) j = x j + i := rfl

lemma smul_apply_sr (n k : ℕ) (i : ZMod n) (x : Fin k → ZMod n) (j : Fin k) :
    (sr i • x) j = -i - x j := rfl

lemma fix_r (n k : ℕ) [NeZero n] (i : ZMod n) :
    Nat.card (fixedBy (Fin (k + 1) → ZMod n) (r i)) = if i = 0 then n ^ (k + 1) else 0 := by
  split_ifs with h
  · subst h
    rw [show (r 0 : DihedralGroup n) = 1 from rfl, fixedBy_one_eq_univ, Set.univ.eq_def,
      ← Set.univ.eq_def, Nat.card_univ, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  · rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨x, hx⟩ => h ?_⟩
    have := congrFun (hx : r i • x = x) 0
    rw [smul_apply_r] at this
    simpa using this

lemma fix_sr (n k : ℕ) (i : ZMod n) :
    fixedBy (Fin k → ZMod n) (sr i) = {x | ∀ j, -i - x j = x j} := by
  ext x
  simp only [mem_fixedBy, Set.mem_ofPred_eq, funext_iff, smul_apply_sr]

def sigmaEquiv (n k : ℕ) :
    (Σ i : ZMod n, {x : Fin (k + 1) → ZMod n // ∀ j, -i - x j = x j}) ≃
      ZMod n × (Fin k → {y : ZMod n // 2 * y = 0}) where
  toFun s := (s.2.1 0, fun j => ⟨s.2.1 j.succ - s.2.1 0, by
    have h1 := s.2.2 j.succ
    have h0 := s.2.2 0
    linear_combination (-1 : ZMod n) * h1 + h0⟩)
  invFun p := ⟨-2 * p.1, Fin.cons p.1 (fun j => p.1 + (p.2 j).1), by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.cons_zero]
      ring
    · simp only [Fin.cons_succ]
      linear_combination (-1 : ZMod n) * (p.2 j).2⟩
  left_inv s := by
    obtain ⟨i, x, hx⟩ := s
    refine Sigma.subtype_ext ?_ ?_
    · show -2 * x 0 = i
      linear_combination hx 0
    · funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp
  right_inv p := by
    obtain ⟨c, d⟩ := p
    simp only [Fin.cons_zero, Fin.cons_succ, Prod.mk.injEq, true_and]
    funext j
    ext
    simp

lemma sum_fix_sr (n k : ℕ) [NeZero n] :
    ∑ i : ZMod n, Nat.card (fixedBy (Fin (k + 1) → ZMod n) (sr i)) =
      n * (if Even n then 2 else 1) ^ k := by
  have hc : ∀ i : ZMod n, Nat.card (fixedBy (Fin (k + 1) → ZMod n) (sr i)) =
      Nat.card {x : Fin (k + 1) → ZMod n // ∀ j, -i - x j = x j} := fun i => by
    rw [fix_sr]; rfl
  simp only [hc]
  rw [← Nat.card_sigma]
  rw [Nat.card_congr (sigmaEquiv n k), Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin,
    cardT]

lemma burnside (n k : ℕ) [NeZero n] :
    Nat.card (orbitRel.Quotient (DihedralGroup n) (Fin (k + 1) → ZMod n)) * (2 * n) =
      n ^ (k + 1) + n * (if Even n then 2 else 1) ^ k := by
  classical
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (DihedralGroup n)
    (Fin (k + 1) → ZMod n)
  rw [DihedralGroup.card] at hb
  have hs : ∑ g : DihedralGroup n, Fintype.card (fixedBy (Fin (k + 1) → ZMod n) g) =
      ∑ g : DihedralGroup n, Nat.card (fixedBy (Fin (k + 1) → ZMod n) g) := by
    simp only [Nat.card_eq_fintype_card]
  rw [Nat.card_eq_fintype_card, ← hb, hs]
  rw [← (Fintype.sum_equiv DihedralGroup.equivSum.symm _ _ (fun _ => rfl)), Fintype.sum_sum_type]
  simp only [DihedralGroup.equivSum_symm_apply]
  rw [sum_fix_sr]
  simp only [fix_r, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end A236283P

namespace A236283P
open OMA.S_oeis_a236283 PowerSeries

lemma two_a (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) * 2 = (n : ℚ) ^ 2 + ((if Even n then 2 else 1 : ℕ) : ℚ) ^ 2 := by
  haveI : NeZero n := ⟨by omega⟩
  have h : a n * (2 * n) = n ^ 3 + n * (if Even n then 2 else 1) ^ 2 := burnside n 2
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] at hq
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have e : ((a n : ℚ) * 2 - (n : ℚ) ^ 2 - ((if Even n then 2 else 1 : ℕ) : ℚ) ^ 2) * n = 0 := by
    linear_combination hq
  rcases mul_eq_zero.mp e with e | e
  · linear_combination e
  · exact absurd e hn0

lemma cf (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (5 + 3 * (-1) ^ n + 2 * (n : ℚ) ^ 2) / 4 := by
  have h := two_a n hn
  rcases Nat.even_or_odd n with he | ho
  · rw [if_pos he] at h
    rw [he.neg_one_pow]
    push_cast at h
    linarith
  · rw [if_neg (Nat.not_even_iff_odd.mpr ho)] at h
    rw [ho.neg_one_pow]
    push_cast at h
    linarith

lemma rec (n : ℕ) (hn : 5 ≤ n) : (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 3 = m + 2 by omega,
    show m + 5 - 4 = m + 1 by omega]
  have e : ((a (m + 5) : ℤ) : ℚ) = ((2 * a (m + 4) - 2 * a (m + 2) + a (m + 1) : ℤ) : ℚ) := by
    push_cast
    rw [cf (m + 5) (by omega), cf (m + 4) (by omega), cf (m + 2) (by omega), cf (m + 1) (by omega)]
    push_cast
    ring
  exact_mod_cast e

lemma cm (f : ℕ → ℚ) (d n : ℕ) :
    coeff n (PowerSeries.mk f * X ^ d) = if d ≤ n then f (n - d) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

lemma gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) * ((X - 1) ^ 3 * (X + 1) : ℚ⟦X⟧) =
    -X * (2 * X ^ 3 - 3 * X ^ 2 + 2 * X + 1) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else a n with hF
  have key : PowerSeries.mk F * ((X - 1) ^ 3 * (X + 1) : ℚ⟦X⟧) =
      PowerSeries.mk F * X ^ 4 - PowerSeries.mk F * X ^ 3 - PowerSeries.mk F * X ^ 3 + PowerSeries.mk F * X ^ 1 + PowerSeries.mk F * X ^ 1 - PowerSeries.mk F := by ring
  rw [key, show (-X * (2 * X ^ 3 - 3 * X ^ 2 + 2 * X + 1) : ℚ⟦X⟧) = X ^ 3 + X ^ 3 + X ^ 3 - X ^ 4 - X ^ 4 - X ^ 2 - X ^ 2 - X ^ 1 by ring]
  ext n
  simp only [map_sub, map_add, map_neg, cm, coeff_mk, coeff_X_pow]
  by_cases hn : 5 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [hF, show 1 ≤ m + 5 by omega, show 3 ≤ m + 5 by omega, show 4 ≤ m + 5 by omega, if_true, show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega, show m + 5 ≠ 4 by omega, show m + 5 ≠ 0 by omega, show m + 5 - 1 ≠ 0 by omega, show m + 5 - 3 ≠ 0 by omega, show m + 5 - 4 ≠ 0 by omega, if_false]
    rw [cf (m + 5) (by omega), cf (m + 5 - 1) (by omega), cf (m + 5 - 3) (by omega), cf (m + 5 - 4) (by omega)]
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    push_cast
    ring
  · have v0 : (0 : ℕ) = 0 := rfl
    have v1 := cf 1 (by norm_num)
    have v2 := cf 2 (by norm_num)
    have v3 := cf 3 (by norm_num)
    have v4 := cf 4 (by norm_num)
    norm_num at v1 v2 v3 v4
    interval_cases n <;> simp [hF, v1, v2, v3, v4] <;> norm_num

end A236283P

theorem OMA.solution : type_of% @OMA.S_oeis_a236283.main :=
  ⟨A236283P.cf, A236283P.rec, A236283P.gf⟩
