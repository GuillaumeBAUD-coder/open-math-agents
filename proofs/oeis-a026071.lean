import OMAStatements.S_oeis_a026071

/-! Independent proof of Mathar's A026071 recurrence.
Credit: @CubeJerry, with Codex assistance.
The exact walk count is the coefficient of Q*P^(n-2), and an integer
polynomial certificate turns the recurrence into an Euler derivative. -/

namespace A026071Proof
open Polynomial
open scoped BigOperators

def GoodWord {n : ℕ} (w : Fin n → Fin 3) : Prop :=
  (∀ i : Fin n, i.val < 2 → w i ≠ 1) ∧ ∑ i : Fin n, (w i).val = n + 4

noncomputable def wordCount (n : ℕ) : ℤ :=
  (Nat.card {w : Fin n → Fin 3 // GoodWord w} : ℤ)

noncomputable def P : ℤ[X] := 1 + X + X^2
noncomputable def Q : ℤ[X] := (1 + X^2)^2
end A026071Proof

namespace A026071Proof
open Polynomial
open scoped BigOperators

noncomputable def weight (i : ℕ) (d : Fin 3) : ℤ[X] :=
  if i < 2 ∧ d = 1 then 0 else X ^ d.val

noncomputable def rowPoly (n : ℕ) : ℤ[X] :=
  ∏ i : Fin n, ∑ d : Fin 3, weight i.val d

theorem word_product {n : ℕ} (w : Fin n → Fin 3) :
    (∏ i : Fin n, weight i.val (w i)) =
      if (∀ i : Fin n, i.val < 2 → w i ≠ 1) then X ^ (∑ i : Fin n, (w i).val) else 0 := by
  classical
  by_cases h : ∀ i : Fin n, i.val < 2 → w i ≠ 1
  · rw [if_pos h]
    calc
      _ = ∏ i : Fin n, (X : ℤ[X]) ^ (w i).val := by
        apply Finset.prod_congr rfl
        intro i _
        apply if_neg
        exact fun hi => h i hi.1 hi.2
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    have ht := Classical.not_imp.mp hi
    have hw : w i = 1 := Classical.not_not.mp ht.2
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [weight, ht.1, hw]

theorem wordCount_eq_coeff (n : ℕ) :
    wordCount n = (rowPoly n).coeff (n + 4) := by
  classical
  rw [wordCount, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.natCast_card_filter]
  unfold rowPoly
  rw [Fintype.prod_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro w _
  rw [word_product]
  by_cases h : ∀ i : Fin n, i.val < 2 → w i ≠ 1
  · rw [if_pos h]
    by_cases hs : (∑ i : Fin n, (w i).val) = n + 4
    · have hg : GoodWord w := ⟨h, hs⟩
      simp only [if_pos hg, coeff_X_pow, if_pos hs.symm]
    · have hg : ¬GoodWord w := fun hw => hs hw.2
      simp only [if_neg hg, coeff_X_pow, if_neg (Ne.symm hs)]
  · have hg : ¬GoodWord w := fun hw => h hw.1
    rw [if_neg h, if_neg hg, coeff_zero]

theorem weight_sum_low (i : ℕ) (hi : i < 2) :
    (∑ d : Fin 3, weight i d) = (1 + X ^ 2 : ℤ[X]) := by
  simp [weight, hi, Fin.sum_univ_succ]

theorem weight_sum_high (i : ℕ) (hi : 2 ≤ i) :
    (∑ d : Fin 3, weight i d) = P := by
  simp [weight, show ¬i < 2 by omega, Fin.sum_univ_succ, P, add_assoc]

theorem rowPoly_closed (n : ℕ) : rowPoly (n + 2) = Q * P ^ n := by
  classical
  unfold rowPoly
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ]
  rw [weight_sum_low 0 (by omega), weight_sum_low 1 (by omega)]
  have htail : (∏ i : Fin n, ∑ d : Fin 3, weight (i.val + 1 + 1) d) = P ^ n := by
    calc
      _ = ∏ _i : Fin n, P := by
        apply Finset.prod_congr rfl
        intro i _
        exact weight_sum_high _ (by omega)
      _ = _ := by simp
  rw [htail]
  simp only [Q, pow_two]
  ring

theorem wordCount_coeff (n : ℕ) :
    wordCount (n + 2) = (Q * P ^ n).coeff (n + 6) := by
  rw [wordCount_eq_coeff, rowPoly_closed]

end A026071Proof

namespace A026071Proof
open Polynomial

def c0 (n : ℤ) : ℤ := -(n - 4) * (n + 4)
def c1 (n : ℤ) : ℤ := (4*n+7)*(n-4)
def c2 (n : ℤ) : ℤ := -2*n^2+23*n-12
def c3 (n : ℤ) : ℤ := -(4*n+3)*(n-4)
def c4 (n : ℤ) : ℤ := 3*(n-4)*(n-5)

noncomputable def cert (n : ℤ) : ℤ[X] :=
 C (n-4) + C (3*n-20)*X^2 - C 8*X^3 + C (2*(n-20))*X^4 - C 24*X^5 -
 C (2*(n+20))*X^6 - C 24*X^7 - C (3*n+20)*X^8 - C 8*X^9 - C (n+4)*X^10

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem certificate (n : ℤ) :
    Q * (C (c0 n)*P^4 + C (c1 n)*X*P^3 + C (c2 n)*X^2*P^2 +
      C (c3 n)*X^3*P + C (c4 n)*X^4) =
    X*P*(cert n).derivative + (C (n-5)*X*P.derivative-C (n+4)*P)*cert n := by
  simp only [cert, P, Q, c0, c1, c2, c3, c4, derivative_add, derivative_sub,
    derivative_C_mul_X_pow, derivative_C, derivative_one, derivative_X, derivative_X_pow]
  simp only [map_mul, map_add, map_sub, map_pow, map_neg, map_ofNat]
  norm_num
  ring

end A026071Proof

namespace A026071Proof
open Polynomial

theorem coeff_euler (F : ℤ[X]) (k : ℕ) :
    (X * F.derivative - C ((k + 1 : ℕ) : ℤ) * F).coeff (k + 1) = 0 := by
  simp only [coeff_sub, coeff_X_mul, coeff_derivative, coeff_C_mul,
    Nat.cast_add, Nat.cast_one]
  ring

noncomputable def combination (m : ℕ) : ℤ[X] :=
  C (c0 (m + 8)) * (Q * P ^ (m + 6)) +
  C (c1 (m + 8)) * ((Q * P ^ (m + 5)) * X) +
  C (c2 (m + 8)) * ((Q * P ^ (m + 4)) * X ^ 2) +
  C (c3 (m + 8)) * ((Q * P ^ (m + 3)) * X ^ 3) +
  C (c4 (m + 8)) * ((Q * P ^ (m + 2)) * X ^ 4)

theorem combination_coeff (m : ℕ) :
    (combination m).coeff (m + 12) =
      c0 (m + 8) * wordCount (m + 8) + c1 (m + 8) * wordCount (m + 7) +
      c2 (m + 8) * wordCount (m + 6) + c3 (m + 8) * wordCount (m + 5) +
      c4 (m + 8) * wordCount (m + 4) := by
  have h0 := wordCount_coeff (m + 6)
  have h1 := wordCount_coeff (m + 5)
  have h2 := wordCount_coeff (m + 4)
  have h3 := wordCount_coeff (m + 3)
  have h4 := wordCount_coeff (m + 2)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h0 h1 h2 h3 h4
  have hx1 : ((Q * P ^ (m + 5)) * X).coeff (m + 12) =
      (Q * P ^ (m + 5)).coeff (m + 11) := by
    simpa only [Nat.add_assoc] using coeff_mul_X (Q * P ^ (m + 5)) (m + 11)
  have hx2 : ((Q * P ^ (m + 4)) * X ^ 2).coeff (m + 12) =
      (Q * P ^ (m + 4)).coeff (m + 10) := by
    simpa only [Nat.add_assoc] using coeff_mul_X_pow (Q * P ^ (m + 4)) 2 (m + 10)
  have hx3 : ((Q * P ^ (m + 3)) * X ^ 3).coeff (m + 12) =
      (Q * P ^ (m + 3)).coeff (m + 9) := by
    simpa only [Nat.add_assoc] using coeff_mul_X_pow (Q * P ^ (m + 3)) 3 (m + 9)
  have hx4 : ((Q * P ^ (m + 2)) * X ^ 4).coeff (m + 12) =
      (Q * P ^ (m + 2)).coeff (m + 8) := by
    simpa only [Nat.add_assoc] using coeff_mul_X_pow (Q * P ^ (m + 2)) 4 (m + 8)
  simp only [combination, coeff_add, coeff_C_mul, hx1, hx2, hx3, hx4]
  rw [← h0, ← h1, ← h2, ← h3, ← h4]

set_option maxHeartbeats 1000000 in
theorem combination_zero (m : ℕ) : (combination m).coeff (m + 12) = 0 := by
  let F : ℤ[X] := P ^ (m + 2 + 1) * cert (m + 8)
  have hn : (m : ℤ) + 8 - 5 = ((m + 2 + 1 : ℕ) : ℤ) := by
    push_cast; ring
  have hk : (m : ℤ) + 8 + 4 = ((m + 12 : ℕ) : ℤ) := by
    push_cast; ring
  have hp : combination m = X * F.derivative - C ((m + 12 : ℕ) : ℤ) * F := by
    calc
      combination m =
          P ^ (m + 2) * (Q *
            (C (c0 (m + 8)) * P ^ 4 + C (c1 (m + 8)) * X * P ^ 3 +
              C (c2 (m + 8)) * X ^ 2 * P ^ 2 + C (c3 (m + 8)) * X ^ 3 * P +
              C (c4 (m + 8)) * X ^ 4)) := by
        rw [combination, show m + 6 = (m + 2) + 4 by omega,
          show m + 5 = (m + 2) + 3 by omega,
          show m + 4 = (m + 2) + 2 by omega,
          show m + 3 = (m + 2) + 1 by omega]
        simp only [pow_add, pow_one]
        ring
      _ = P ^ (m + 2) * (X * P * (cert (m + 8)).derivative +
          (C ((m : ℤ) + 8 - 5) * X * P.derivative -
            C ((m : ℤ) + 8 + 4) * P) * cert (m + 8)) := by
        rw [certificate]
      _ = X * F.derivative - C ((m + 12 : ℕ) : ℤ) * F := by
        rw [hn, hk]
        dsimp [F]
        rw [derivative_mul, derivative_pow_succ]
        simp only [pow_succ]
        simp only [Nat.cast_add, Nat.cast_ofNat, map_add, map_ofNat]
        ring
  rw [hp, show m + 12 = (m + 11) + 1 by omega, coeff_euler]

theorem recurrence_wordCount (n : ℕ) (hn : 8 ≤ n) :
    c0 n * wordCount n + c1 n * wordCount (n - 1) + c2 n * wordCount (n - 2) +
      c3 n * wordCount (n - 3) + c4 n * wordCount (n - 4) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  have h := (combination_coeff m).symm.trans (combination_zero m)
  simpa only [Nat.cast_add, Nat.cast_ofNat,
    show m + 8 - 1 = m + 7 by omega,
    show m + 8 - 2 = m + 6 by omega,
    show m + 8 - 3 = m + 5 by omega,
    show m + 8 - 4 = m + 4 by omega] using h

end A026071Proof

namespace A026071Proof
open scoped BigOperators
open OMA.S_oeis_a026071

def walkDelta {n : ℕ} (s : Fin (n + 1) → ℤ) (i : Fin n) : ℤ :=
  s i.succ - s i.castSucc

lemma walkDelta_bounds {n : ℕ} {s : Fin (n + 1) → ℤ} (hs : s ∈ walks n)
    (i : Fin n) : -1 ≤ walkDelta s i ∧ walkDelta s i ≤ 1 := by
  apply abs_le.mp
  by_cases hi : i.val < 2
  · exact le_of_eq (hs.2.2.1 i.castSucc i.succ rfl (by change i.val + 1 ≤ 2; omega))
  · exact hs.2.2.2 i.castSucc i.succ rfl (by change 2 < i.val + 1; omega)

lemma walkDelta_first_ne_zero {n : ℕ} {s : Fin (n + 1) → ℤ} (hs : s ∈ walks n)
    (i : Fin n) (hi : i.val < 2) : walkDelta s i ≠ 0 := by
  have h := hs.2.2.1 i.castSucc i.succ rfl (by simpa using hi)
  change |walkDelta s i| = 1 at h
  intro hz
  simp [hz] at h

def wordOfWalk {n : ℕ} (s : ↥(walks n)) (i : Fin n) : Fin 3 :=
  ⟨(walkDelta s.val i + 1).toNat, by
    have hb := walkDelta_bounds s.property i
    omega⟩

lemma wordOfWalk_value {n : ℕ} (s : ↥(walks n)) (i : Fin n) :
    ((wordOfWalk s i).val : ℤ) = walkDelta s.val i + 1 := by
  change ((walkDelta s.val i + 1).toNat : ℤ) = walkDelta s.val i + 1
  have hb := walkDelta_bounds s.property i
  exact Int.toNat_of_nonneg (by omega)

lemma sum_walkDelta {n : ℕ} (s : Fin (n + 1) → ℤ) :
    ∑ i : Fin n, walkDelta s i = s (Fin.last n) - s 0 := by
  have h1 := Fin.sum_univ_succ s
  have h2 := Fin.sum_univ_castSucc s
  simp only [walkDelta, Finset.sum_sub_distrib]
  omega

lemma wordOfWalk_good {n : ℕ} (s : ↥(walks n)) : GoodWord (wordOfWalk s) := by
  constructor
  · intro i hi h
    have hz := walkDelta_first_ne_zero s.property i hi
    have hv : (wordOfWalk s i).val = 1 := congrArg Fin.val h
    have hc := wordOfWalk_value s i
    rw [hv] at hc
    exact hz (by omega)
  · have hs0 : s.val 0 = 0 := s.property.1 0 rfl
    have hsn : s.val (Fin.last n) = 4 := s.property.2.1 (Fin.last n) rfl
    have hh : (∑ i : Fin n, ((wordOfWalk s i).val : ℤ)) = (n : ℤ) + 4 := by
      simp only [wordOfWalk_value, Finset.sum_add_distrib]
      rw [sum_walkDelta, hs0, hsn]
      simp
      omega
    exact_mod_cast hh

def decodeWord {n : ℕ} (w : Fin n → Fin 3) : Fin (n + 1) → ℤ :=
  Fin.partialSum (fun i => ((w i).val : ℤ) - 1)

lemma decodeWord_zero {n : ℕ} (w : Fin n → Fin 3) : decodeWord w 0 = 0 := by
  simp [decodeWord]

lemma decodeWord_succ {n : ℕ} (w : Fin n → Fin 3) (i : Fin n) :
    decodeWord w i.succ = decodeWord w i.castSucc + (((w i).val : ℤ) - 1) :=
  Fin.partialSum_succ _ i

lemma decodeWord_delta {n : ℕ} (w : Fin n → Fin 3) (i : Fin n) :
    walkDelta (decodeWord w) i = ((w i).val : ℤ) - 1 := by
  simp [walkDelta, decodeWord_succ]

lemma partialSum_last_int {n : ℕ} (f : Fin n → ℤ) :
    Fin.partialSum f (Fin.last n) = ∑ i : Fin n, f i := by
  change (List.take n (List.ofFn f)).sum = ∑ i : Fin n, f i
  rw [List.take_of_length_le (by simp : (List.ofFn f).length ≤ n), List.sum_ofFn]

lemma decodeWord_last {n : ℕ} (w : Fin n → Fin 3) :
    decodeWord w (Fin.last n) = ((∑ i : Fin n, (w i).val : ℕ) : ℤ) - n := by
  rw [decodeWord, partialSum_last_int, Finset.sum_sub_distrib]
  simp

lemma decodeWord_mem {n : ℕ} {w : Fin n → Fin 3} (hw : GoodWord w) :
    decodeWord w ∈ walks n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have he : i = 0 := Fin.ext hi
    rw [he, decodeWord_zero]
  · intro i hi
    have he : i = Fin.last n := Fin.ext hi
    rw [he, decodeWord_last, hw.2]
    push_cast
    omega
  · intro i j hij hj
    let k : Fin n := ⟨i.val, by have := j.isLt; omega⟩
    have hki : k.castSucc = i := Fin.ext rfl
    have hkj : k.succ = j := Fin.ext (by simpa [k] using hij.symm)
    rw [← hki, ← hkj]
    change |walkDelta (decodeWord w) k| = 1
    rw [decodeWord_delta]
    have hk2 : k.val < 2 := by dsimp [k]; omega
    have hne : (w k).val ≠ 1 := by
      intro he
      exact hw.1 k hk2 (Fin.ext he)
    have hlt := (w k).isLt
    have he : (w k).val = 0 ∨ (w k).val = 2 := by omega
    rcases he with he | he <;> norm_num [he]
  · intro i j hij hj
    let k : Fin n := ⟨i.val, by have := j.isLt; omega⟩
    have hki : k.castSucc = i := Fin.ext rfl
    have hkj : k.succ = j := Fin.ext (by simpa [k] using hij.symm)
    rw [← hki, ← hkj]
    change |walkDelta (decodeWord w) k| ≤ 1
    rw [decodeWord_delta, abs_le]
    have hlt := (w k).isLt
    constructor <;> omega

lemma decodeWord_wordOfWalk {n : ℕ} (s : ↥(walks n)) :
    decodeWord (wordOfWalk s) = s.val := by
  funext i
  induction i using Fin.induction with
  | zero =>
    rw [decodeWord_zero]
    exact (s.property.1 0 rfl).symm
  | succ i ih =>
    rw [decodeWord_succ, ih, wordOfWalk_value]
    dsimp [walkDelta]
    omega

lemma wordOfWalk_decodeWord {n : ℕ} (w : {w : Fin n → Fin 3 // GoodWord w}) :
    wordOfWalk ⟨decodeWord w.val, decodeWord_mem w.property⟩ = w.val := by
  funext i
  apply Fin.ext
  have h := wordOfWalk_value ⟨decodeWord w.val, decodeWord_mem w.property⟩ i
  simp only [decodeWord_delta, sub_add_cancel] at h
  exact_mod_cast h

def walkWordEquiv (n : ℕ) : ↥(walks n) ≃ {w : Fin n → Fin 3 // GoodWord w} where
  toFun s := ⟨wordOfWalk s, wordOfWalk_good s⟩
  invFun w := ⟨decodeWord w.val, decodeWord_mem w.property⟩
  left_inv s := Subtype.ext (decodeWord_wordOfWalk s)
  right_inv w := Subtype.ext (wordOfWalk_decodeWord w)

theorem a_eq_wordCount (n : ℕ) : OMA.S_oeis_a026071.a n = wordCount n := by
  unfold OMA.S_oeis_a026071.a wordCount
  congr 1
  exact Nat.card_congr (walkWordEquiv n)

end A026071Proof

namespace A026071Proof
open OMA.S_oeis_a026071

theorem target : ∀ n : ℕ, 8 ≤ n →
    -((n : ℤ) - 4) * ((n : ℤ) + 4) * a n + (4 * (n : ℤ) + 7) * ((n : ℤ) - 4) * a (n - 1) +
      (-2 * (n : ℤ) ^ 2 + 23 * (n : ℤ) - 12) * a (n - 2) - (4 * (n : ℤ) + 3) * ((n : ℤ) - 4) * a (n - 3) +
      3 * ((n : ℤ) - 4) * ((n : ℤ) - 5) * a (n - 4) = 0 := by
  intro n hn
  have h := recurrence_wordCount n hn
  simp only [← a_eq_wordCount] at h
  simpa only [c0, c1, c2, c3, c4, sub_eq_add_neg, neg_mul] using h

end A026071Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a026071.main :=
  A026071Proof.target
