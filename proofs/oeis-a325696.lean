import OMAStatements.S_oeis_a325696
import Mathlib

-- The argument follows the accepted proof of OEIS A325695 (the template entry): the sorted
-- count A325695 is defined and its recurrence proved exactly as there (lemmas copied, with the
-- counting function renamed sterm). New here: every sorted triple x < y < z corresponds to
-- exactly six strict compositions (its orderings), shown by counting the fibres of the sorting
-- map, so A325696(n) = 6 * A325695(n); the recurrence and generating function follow.

namespace OMA.P_a325696
open OMA.S_oeis_a325696 PowerSeries

/-- The sorted count of the template entry A325695 (u = a-1, v = b-a-1). -/
def sallowed (n u v : ℕ) : Bool :=
  let a := u+1
  let b := a+v+1
  let c := n-(a+b)
  decide (b<c ∧ a+b+c=n ∧ c≠a+b)

def sterm (n : ℕ) : ℕ := ∑ u ∈ Finset.range (n+1),
  ((Finset.range (n+1)).filter (fun v => sallowed n u v)).card

def A' (n u : ℕ) : ℕ := (n - (3*u+5) + 1)/2
def B' (n u : ℕ) : ℕ := if n % 2 = 0 ∧ 4*u+6 ≤ n then 1 else 0

lemma sallowed_iff (n u v : ℕ) :
    sallowed n u v = true ↔ 3*u+2*v+5 < n ∧ n ≠ 4*u+2*v+6 := by
  simp only [sallowed, decide_eq_true_eq]
  omega

lemma card_eq (n u : ℕ) :
    ((Finset.range (n+1)).filter (fun v => sallowed n u v)).card + B' n u = A' n u := by
  unfold A' B'
  split_ifs with h
  · have hs : (Finset.range (n+1)).filter (fun v => sallowed n u v) =
        (Finset.range ((n - (3*u+5) + 1)/2)).erase ((n - (4*u+6))/2) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, sallowed_iff]
      omega
    have hm : (n - (4*u+6))/2 ∈ Finset.range ((n - (3*u+5) + 1)/2) := by
      simp only [Finset.mem_range]; omega
    rw [hs, Finset.card_erase_of_mem hm, Finset.card_range]
    omega
  · have hs : (Finset.range (n+1)).filter (fun v => sallowed n u v) =
        Finset.range ((n - (3*u+5) + 1)/2) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, sallowed_iff]
      omega
    rw [hs, Finset.card_range, add_zero]

lemma term_eq (n : ℕ) :
    sterm n + ∑ u ∈ Finset.range (n+1), B' n u = ∑ u ∈ Finset.range (n+1), A' n u := by
  simp only [sterm, ← Finset.sum_add_distrib, card_eq]

lemma sumA_ext (n j : ℕ) :
    ∑ u ∈ Finset.range (n+1+j), A' n u = ∑ u ∈ Finset.range (n+1), A' n u := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show n+1+(j+1) = (n+1+j)+1 by omega, Finset.sum_range_succ, ih]
    have : A' n (n+1+j) = 0 := by unfold A'; omega
    rw [this, add_zero]

lemma sumB_ext (n j : ℕ) :
    ∑ u ∈ Finset.range (n+1+j), B' n u = ∑ u ∈ Finset.range (n+1), B' n u := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show n+1+(j+1) = (n+1+j)+1 by omega, Finset.sum_range_succ, ih]
    have : B' n (n+1+j) = 0 := by unfold B'; split_ifs <;> omega
    rw [this, add_zero]

lemma sumA_shift (n : ℕ) :
    ∑ u ∈ Finset.range (n+12+1), A' (n+12) u = ∑ u ∈ Finset.range (n+1), A' n u +
      (A' (n+12) 0 + A' (n+12) 1 + A' (n+12) 2 + A' (n+12) 3) := by
  rw [show n+12+1 = 4 + (n+1+8) by omega, Finset.sum_range_add]
  have : ∀ u, A' (n+12) (4+u) = A' n u := by intro u; unfold A'; omega
  simp only [this]
  rw [sumA_ext]
  have hs : ∑ u ∈ Finset.range 4, A' (n+12) u =
      A' (n+12) 0 + A' (n+12) 1 + A' (n+12) 2 + A' (n+12) 3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hs]
  ring

lemma sumB_shift (n : ℕ) :
    ∑ u ∈ Finset.range (n+12+1), B' (n+12) u = ∑ u ∈ Finset.range (n+1), B' n u +
      (B' (n+12) 0 + B' (n+12) 1 + B' (n+12) 2) := by
  rw [show n+12+1 = 3 + (n+1+9) by omega, Finset.sum_range_add]
  have : ∀ u, B' (n+12) (3+u) = B' n u := by
    intro u; unfold B'
    have : (4*(3+u)+6 ≤ n+12) ↔ 4*u+6 ≤ n := by omega
    have h2 : (n+12) % 2 = n % 2 := by omega
    simp only [this, h2]
  simp only [this]
  rw [sumB_ext]
  have hs : ∑ u ∈ Finset.range 3, B' (n+12) u = B' (n+12) 0 + B' (n+12) 1 + B' (n+12) 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hs]
  ring

lemma key (n : ℕ) (hn : 1 ≤ n) :
    sterm (n+12) + 3*((n+1)%2) = sterm n + ((n+8)/2 + (n+5)/2 + (n+2)/2 + (n-2+1)/2) := by
  have h1 := term_eq (n+12)
  have h2 := term_eq n
  rw [sumA_shift, sumB_shift] at h1
  have hB : B' (n+12) 0 + B' (n+12) 1 + B' (n+12) 2 = 3*((n+1)%2) := by
    unfold B'; split_ifs <;> omega
  have hA : A' (n+12) 0 + A' (n+12) 1 + A' (n+12) 2 + A' (n+12) 3 =
      (n+8)/2 + (n+5)/2 + (n+2)/2 + (n-2+1)/2 := by
    unfold A'; omega
  omega

set_option maxRecDepth 100000 in
lemma base (k : ℕ) (hk : k < 12) :
    sterm (k+10)+sterm (k+5)+sterm (k+4)+sterm (k+3) =
      sterm (k+8)+sterm (k+7)+sterm (k+6)+sterm (k+1) := by
  interval_cases k <;> decide +kernel

lemma recur : ∀ k : ℕ, sterm (k+10)+sterm (k+5)+sterm (k+4)+sterm (k+3) =
      sterm (k+8)+sterm (k+7)+sterm (k+6)+sterm (k+1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < 12
    · exact base k hk
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 12 := ⟨k - 12, by omega⟩
      have IH := ih j (by omega)
      have e1 := key (j+10) (by omega)
      have e2 := key (j+5) (by omega)
      have e3 := key (j+4) (by omega)
      have e4 := key (j+3) (by omega)
      have e5 := key (j+8) (by omega)
      have e6 := key (j+7) (by omega)
      have e7 := key (j+6) (by omega)
      have e8 := key (j+1) (by omega)
      rw [show j+12+10 = j+10+12 by omega, show j+12+5 = j+5+12 by omega,
        show j+12+4 = j+4+12 by omega, show j+12+3 = j+3+12 by omega,
        show j+12+8 = j+8+12 by omega, show j+12+7 = j+7+12 by omega,
        show j+12+6 = j+6+12 by omega, show j+12+1 = j+1+12 by omega]
      omega

set_option maxRecDepth 100000 in
lemma ssmall : sterm 0 = 0 ∧ sterm 1 = 0 ∧ sterm 2 = 0 ∧ sterm 3 = 0 ∧ sterm 4 = 0 ∧
    sterm 5 = 0 ∧ sterm 6 = 0 ∧ sterm 7 = 1 ∧ sterm 8 = 1 ∧ sterm 9 = 3 := by
  decide +kernel


/-! Ordered versus sorted triples. -/

lemma allowed_iff' (n a b : ℕ) :
    allowed n a b = true ↔ 0<a ∧ 0<b ∧ a+b<n ∧ a≠b ∧ a≠n-(a+b) ∧ b≠n-(a+b) ∧
      2*a≠n ∧ 2*b≠n ∧ 2*(a+b)≠n := by
  simp only [allowed, decide_eq_true_eq]
  omega

def E (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n+1) ×ˢ Finset.range (n+1)).filter (fun p => allowed n p.1 p.2)

def Z (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n+1) ×ˢ Finset.range (n+1)).filter (fun p => sallowed n p.1 p.2)

lemma term_card (n : ℕ) : term n = (E n).card := by
  rw [E, Finset.card_filter, Finset.sum_product, term]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.card_filter]

lemma sterm_card (n : ℕ) : sterm n = (Z n).card := by
  rw [Z, Finset.card_filter, Finset.sum_product, sterm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.card_filter]

/-- Sorting map: the smallest part minus one and the gap between the two smallest parts minus one. -/
def srt (n : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (min p.1 (min p.2 (n-(p.1+p.2))) - 1,
    (p.1 + p.2 + (n-(p.1+p.2)) - min p.1 (min p.2 (n-(p.1+p.2))) -
      max p.1 (max p.2 (n-(p.1+p.2)))) - min p.1 (min p.2 (n-(p.1+p.2))) - 1)

lemma maps (n : ℕ) : ∀ p ∈ E n, srt n p ∈ Z n := by
  rintro ⟨a, b⟩ hp
  simp only [E, Z, srt, Finset.mem_filter, Finset.mem_product, Finset.mem_range, allowed_iff',
    sallowed_iff] at hp ⊢
  omega

lemma six (x y z : ℕ) (h1 : x < y) (h2 : y < z) :
    ({(x,y), (y,x), (x,z), (z,x), (y,z), (z,y)} : Finset (ℕ × ℕ)).card = 6 := by
  have e1 : (x,y) ∉ ({(y,x), (x,z), (z,x), (y,z), (z,y)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]; omega
  have e2 : (y,x) ∉ ({(x,z), (z,x), (y,z), (z,y)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]; omega
  have e3 : (x,z) ∉ ({(z,x), (y,z), (z,y)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]; omega
  have e4 : (z,x) ∉ ({(y,z), (z,y)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]; omega
  have e5 : (y,z) ∉ ({(z,y)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton, Prod.mk.injEq]; omega
  rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
    Finset.card_insert_of_notMem e3, Finset.card_insert_of_notMem e4,
    Finset.card_insert_of_notMem e5, Finset.card_singleton]

lemma fiber (n : ℕ) (q : ℕ × ℕ) (hq : q ∈ Z n) :
    ((E n).filter (fun p => srt n p = q)).card = 6 := by
  obtain ⟨u, v⟩ := q
  have hq' := hq
  simp only [Z, Finset.mem_filter, Finset.mem_product, Finset.mem_range, sallowed_iff] at hq'
  have hs : (E n).filter (fun p => srt n p = (u, v)) =
      {(u+1, u+v+2), (u+v+2, u+1), (u+1, n-(2*u+v+3)), (n-(2*u+v+3), u+1),
        (u+v+2, n-(2*u+v+3)), (n-(2*u+v+3), u+v+2)} := by
    ext ⟨a, b⟩
    simp only [E, srt, Finset.mem_filter, Finset.mem_product, Finset.mem_range, allowed_iff',
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [hs]
  exact six _ _ _ (by omega) (by omega)

lemma term_six (n : ℕ) : term n = 6 * sterm n := by
  rw [term_card, sterm_card, Finset.card_eq_sum_card_fiberwise (maps n),
    Finset.sum_const_nat (fun q hq => fiber n q hq), mul_comm]

lemma recur6 : ∀ k : ℕ, term (k+10)+term (k+5)+term (k+4)+term (k+3) =
      term (k+8)+term (k+7)+term (k+6)+term (k+1) := by
  intro k
  have := recur k
  simp only [term_six]
  omega

lemma small : term 0 = 0 ∧ term 1 = 0 ∧ term 2 = 0 ∧ term 3 = 0 ∧ term 4 = 0 ∧
    term 5 = 0 ∧ term 6 = 0 ∧ term 7 = 6 ∧ term 8 = 6 ∧ term 9 = 18 := by
  simp only [term_six]
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := ssmall
  omega

lemma poly_eq : ((1-X)^3*(1+X)^2*(1+X^2)*(1+X+X^2) : PowerSeries ℚ) =
    1 - X^2 - X^3 - X^4 + X^5 + X^6 + X^7 - X^9 := by ring

lemma gf : ((1-X)^3*(1+X)^2*(1+X^2)*(1+X+X^2))*series =
    (6*X^7*(1+X+2*X^2) : PowerSeries ℚ) := by
  have c6 : (C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat C 6
  have c12 : (C (12 : ℚ) : PowerSeries ℚ) = 12 := map_ofNat C 12
  rw [poly_eq, show (6*X^7*(1+X+2*X^2) : PowerSeries ℚ) =
    C 6 * X^7 + C 6 * X^8 + C 12 * X^9 by rw [c6, c12]; ring]
  ext n
  simp only [sub_mul, add_mul, one_mul, map_sub, map_add, coeff_X_pow_mul', series, coeff_mk,
    coeff_X_pow, coeff_C_mul]
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := small
  by_cases hn : 10 ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    have h := recur6 k
    have h' : ((term (k+10) : ℚ) + term (k+5) + term (k+4) + term (k+3)) =
        term (k+8) + term (k+7) + term (k+6) + term (k+1) := by exact_mod_cast h
    simp only [show 2 ≤ k+10 by omega, show 3 ≤ k+10 by omega, show 4 ≤ k+10 by omega,
      show 5 ≤ k+10 by omega, show 6 ≤ k+10 by omega, show 7 ≤ k+10 by omega,
      show 9 ≤ k+10 by omega, if_true, show k+10 ≠ 7 by omega, show k+10 ≠ 8 by omega,
      show k+10 ≠ 9 by omega, if_false, mul_zero, add_zero,
      show k+10-2 = k+8 by omega, show k+10-3 = k+7 by omega, show k+10-4 = k+6 by omega,
      show k+10-5 = k+5 by omega, show k+10-6 = k+4 by omega, show k+10-7 = k+3 by omega,
      show k+10-9 = k+1 by omega]
    linarith
  · interval_cases n <;> simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9] <;> norm_num

end OMA.P_a325696

theorem OMA.solution : type_of% @OMA.S_oeis_a325696.main :=
  ⟨OMA.P_a325696.recur6, OMA.P_a325696.gf⟩
