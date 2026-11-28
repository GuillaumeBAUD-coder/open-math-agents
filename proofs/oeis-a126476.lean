import OMAStatements.S_oeis_a126476
import Mathlib

namespace A126476Aux

lemma chain_cons {B n : ℕ} (R : Fin B → Fin B → Prop) (d : Fin B) (v : Fin (n + 1) → Fin B) :
    (∀ i j : Fin (n + 1 + 1), (j : ℕ) = (i : ℕ) + 1 →
      R ((Fin.cons d v : Fin (n + 1 + 1) → Fin B) i) ((Fin.cons d v : Fin (n + 1 + 1) → Fin B) j)) ↔
    (R d (v 0) ∧ ∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → R (v i) (v j)) := by
  constructor
  · intro h
    refine ⟨?_, fun i j hij => ?_⟩
    · have h0 := h 0 (Fin.succ 0) (by simp)
      rwa [Fin.cons_zero, Fin.cons_succ] at h0
    · have h1 := h i.succ j.succ (by simp [hij])
      rwa [Fin.cons_succ, Fin.cons_succ] at h1
  · rintro ⟨h0, h⟩ i j hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · simp at hij
      · have hj : j' = 0 := Fin.ext (by
          simp only [Fin.val_succ, Fin.val_zero] at hij ⊢
          omega)
        subst hj
        rw [Fin.cons_zero, Fin.cons_succ]
        exact h0
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · simp at hij
      · rw [Fin.cons_succ, Fin.cons_succ]
        exact h i' j' (by
          simp only [Fin.val_succ] at hij
          omega)

open OMA.S_oeis_a126476 in
lemma valid_cons (n : ℕ) (d : Fin 8) (v : Fin (n + 1) → Fin 8) :
    (∀ i j : Fin (n + 1 + 1), (j : ℕ) = (i : ℕ) + 1 → close ((Fin.cons d v : Fin (n + 1 + 1) → Fin 8) i) ((Fin.cons d v : Fin (n + 1 + 1) → Fin 8) j)) ↔
      (close d (v 0) ∧ (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → close (v i) (v j))) :=
  chain_cons close d v

open OMA.S_oeis_a126476 in
def T (f : Fin 8 → ℕ) : Fin 8 → ℕ := fun e => ∑ d : Fin 8, if close d e then f d else 0

def u0 : Fin 8 → ℕ := fun _ => 1

def vec (L : List ℕ) : Fin 8 → ℕ := fun d => L.getD d.val 0

open OMA.S_oeis_a126476 in
def V (n : ℕ) (f : Fin 8 → ℕ) : ℕ :=
  ∑ w : Fin (n + 1) → Fin 8, if (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → close (w i) (w j)) then f (w 0) else 0

open OMA.S_oeis_a126476 in
lemma V_succ (n : ℕ) (f : Fin 8 → ℕ) : V (n + 1) f = V n (T f) := by
  have h1 : V (n + 1) f = ∑ p : Fin 8 × (Fin (n + 1) → Fin 8),
      if close p.1 (p.2 0) ∧ (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → close (p.2 i) (p.2 j)) then f p.1 else 0 := by
    unfold V
    symm
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1 + 1) => Fin 8) :
      Fin 8 × (Fin (n + 1) → Fin 8) ≃ (Fin (n + 1 + 1) → Fin 8))
    intro p
    show (if close p.1 (p.2 0) ∧ (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → close (p.2 i) (p.2 j)) then f p.1 else 0) =
      (if (∀ i j : Fin (n + 1 + 1), (j : ℕ) = (i : ℕ) + 1 → close ((Fin.cons p.1 p.2 : Fin (n + 1 + 1) → Fin 8) i) ((Fin.cons p.1 p.2 : Fin (n + 1 + 1) → Fin 8) j))
        then f ((Fin.cons p.1 p.2 : Fin (n + 1 + 1) → Fin 8) 0) else 0)
    rw [Fin.cons_zero]
    by_cases hv : (∀ i j : Fin (n + 1 + 1), (j : ℕ) = (i : ℕ) + 1 → close ((Fin.cons p.1 p.2 : Fin (n + 1 + 1) → Fin 8) i) ((Fin.cons p.1 p.2 : Fin (n + 1 + 1) → Fin 8) j))
    · rw [if_pos hv, if_pos ((valid_cons n p.1 p.2).mp hv)]
    · rw [if_neg hv, if_neg (fun h => hv ((valid_cons n p.1 p.2).mpr h))]
  rw [h1, Fintype.sum_prod_type, Finset.sum_comm]
  unfold V
  apply Finset.sum_congr rfl
  intro v _
  show (∑ x : Fin 8, if close x (v 0) ∧ (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → close (v i) (v j)) then f x else 0) =
    if (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → close (v i) (v j)) then T f (v 0) else 0
  by_cases hv : (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → close (v i) (v j))
  · rw [if_pos hv]
    show (∑ x : Fin 8, if close x (v 0) ∧ (∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → close (v i) (v j)) then f x else 0) =
      ∑ d : Fin 8, if close d (v 0) then f d else 0
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : close d (v 0)
    · rw [if_pos hd, if_pos ⟨hd, hv⟩]
    · rw [if_neg hd, if_neg (fun h => hd h.1)]
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro d _
    rw [if_neg (fun h => hv h.2)]

open OMA.S_oeis_a126476 in
lemma V_zero (f : Fin 8 → ℕ) : V 0 f = ∑ d : Fin 8, f d := by
  have hval : ∀ w : Fin 1 → Fin 8, (∀ i j : Fin (1), (j : ℕ) = (i : ℕ) + 1 → close (w i) (w j)) := fun w i j hij => absurd hij (by omega)
  have e : ∀ w : Fin 1 → Fin 8, (if (∀ i j : Fin (1), (j : ℕ) = (i : ℕ) + 1 → close (w i) (w j)) then f (w 0) else 0) = f (w 0) :=
    fun w => if_pos (hval w)
  show ∑ w : Fin 1 → Fin 8, (if (∀ i j : Fin (1), (j : ℕ) = (i : ℕ) + 1 → close (w i) (w j)) then f (w 0) else 0) = ∑ d : Fin 8, f d
  refine (Fintype.sum_congr _ _ e).trans ?_
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 8)) _ _ (fun w => rfl)

def U : ℕ → (Fin 8 → ℕ) → (Fin 8 → ℕ)
  | 0, f => f
  | n + 1, f => U n (T f)

lemma U_T (n : ℕ) (f : Fin 8 → ℕ) : U n (T f) = U (n + 1) f := rfl

lemma V_iter (n : ℕ) : ∀ f : Fin 8 → ℕ, V n f = ∑ d : Fin 8, U n f d := by
  induction n with
  | zero =>
    intro f
    exact V_zero f
  | succ k ih =>
    intro f
    rw [V_succ, ih, U_T]

open OMA.S_oeis_a126476 in
lemma a_succ (n : ℕ) : a (n + 1) = ∑ d : Fin 8, U n u0 d := by
  unfold a
  rw [← V_iter, Finset.card_filter]
  rfl

open OMA.S_oeis_a126476 in
lemma T_add (f g : Fin 8 → ℕ) : T (f + g) = T f + T g := by
  funext e
  show (∑ d : Fin 8, if close d e then (f d + g d) else 0) =
    (∑ d : Fin 8, if close d e then f d else 0) + ∑ d : Fin 8, if close d e then g d else 0
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : close d e
  · simp [h]
  · simp [h]

lemma U_add (n : ℕ) : ∀ f g : Fin 8 → ℕ, U n (f + g) = U n f + U n g := by
  induction n with
  | zero =>
    intro f g
    rfl
  | succ k ih =>
    intro f g
    show U k (T (f + g)) = U k (T f) + U k (T g)
    rw [T_add, ih]

set_option maxRecDepth 100000 in
lemma T0 : T (u0) = vec [4, 5, 6, 7, 7, 6, 5, 4] := by decide +kernel

set_option maxRecDepth 100000 in
lemma T1 : T (vec [4, 5, 6, 7, 7, 6, 5, 4]) = vec [22, 29, 35, 40, 40, 35, 29, 22] := by decide +kernel

set_option maxRecDepth 100000 in
lemma T2 : T (vec [22, 29, 35, 40, 40, 35, 29, 22]) = vec [126, 166, 201, 230, 230, 201, 166, 126] := by decide +kernel

set_option maxRecDepth 100000 in
lemma T3 : T (vec [126, 166, 201, 230, 230, 201, 166, 126]) = vec [723, 953, 1154, 1320, 1320, 1154, 953, 723] := by decide +kernel

lemma E1 (m : ℕ) : U m (vec [4, 5, 6, 7, 7, 6, 5, 4]) = U (m + 1) u0 := by
  rw [← T0, U_T]

lemma E2 (m : ℕ) : U m (vec [22, 29, 35, 40, 40, 35, 29, 22]) = U (m + 1 + 1) u0 := by
  rw [← T1, U_T, E1]

lemma E3 (m : ℕ) : U m (vec [126, 166, 201, 230, 230, 201, 166, 126]) = U (m + 1 + 1 + 1) u0 := by
  rw [← T2, U_T, E2]

lemma E4 (m : ℕ) : U m (vec [723, 953, 1154, 1320, 1320, 1154, 953, 723]) = U (m + 1 + 1 + 1 + 1) u0 := by
  rw [← T3, U_T, E3]

set_option maxRecDepth 100000 in
lemma lin : vec [723, 953, 1154, 1320, 1320, 1154, 953, 723] + vec [22, 29, 35, 40, 40, 35, 29, 22] + (vec [4, 5, 6, 7, 7, 6, 5, 4] + vec [4, 5, 6, 7, 7, 6, 5, 4] + vec [4, 5, 6, 7, 7, 6, 5, 4]) =
    (vec [126, 166, 201, 230, 230, 201, 166, 126] + vec [126, 166, 201, 230, 230, 201, 166, 126] + vec [126, 166, 201, 230, 230, 201, 166, 126] + vec [126, 166, 201, 230, 230, 201, 166, 126] + vec [126, 166, 201, 230, 230, 201, 166, 126] + vec [126, 166, 201, 230, 230, 201, 166, 126]) + u0 := by decide +kernel

lemma rec_vec (m : ℕ) : U (m + 1 + 1 + 1 + 1) u0 + U (m + 1 + 1) u0 + (U (m + 1) u0 + U (m + 1) u0 + U (m + 1) u0) =
    (U (m + 1 + 1 + 1) u0 + U (m + 1 + 1 + 1) u0 + U (m + 1 + 1 + 1) u0 + U (m + 1 + 1 + 1) u0 + U (m + 1 + 1 + 1) u0 + U (m + 1 + 1 + 1) u0) + U m u0 := by
  have h := congrArg (U m) lin
  simp only [U_add] at h
  simp only [E1, E2, E3, E4] at h
  exact h

open OMA.S_oeis_a126476 in
lemma rec_a (m : ℕ) : a (m + 5) + a (m + 3) + 3 * a (m + 2) = 6 * a (m + 4) + a (m + 1) := by
  have hs := congrArg (fun F : Fin 8 → ℕ => ∑ d : Fin 8, F d) (rec_vec m)
  simp only [Pi.add_apply, Finset.sum_add_distrib] at hs
  have h1 : a (m + 1) = ∑ d : Fin 8, U m u0 d := a_succ (m)
  have h2 : a (m + 2) = ∑ d : Fin 8, U (m + 1) u0 d := a_succ (m + 1)
  have h3 : a (m + 3) = ∑ d : Fin 8, U (m + 1 + 1) u0 d := a_succ (m + 1 + 1)
  have h4 : a (m + 4) = ∑ d : Fin 8, U (m + 1 + 1 + 1) u0 d := a_succ (m + 1 + 1 + 1)
  have h5 : a (m + 5) = ∑ d : Fin 8, U (m + 1 + 1 + 1 + 1) u0 d := a_succ (m + 1 + 1 + 1 + 1)
  omega

open OMA.S_oeis_a126476 in
lemma av0 : a 0 = 1 := by
  have h : ∀ w ∈ (Finset.univ : Finset (Fin 0 → Fin 8)), (∀ i j : Fin (0), (j : ℕ) = (i : ℕ) + 1 → close (w i) (w j)) := fun w _ i => i.elim0
  unfold a
  rw [Finset.filter_true_of_mem h]
  simp

open OMA.S_oeis_a126476 in
lemma av1 : a 1 = 8 := by
  have h := a_succ 0
  have h2 : ∑ d : Fin 8, U 0 u0 d = 8 := by decide +kernel
  exact h.trans h2

open OMA.S_oeis_a126476 in
lemma av2 : a 2 = 44 := by
  have h := a_succ 1
  have ek : U 1 u0 = vec [4, 5, 6, 7, 7, 6, 5, 4] := (E1 0).symm
  rw [ek] at h
  have h2 : ∑ d : Fin 8, vec [4, 5, 6, 7, 7, 6, 5, 4] d = 44 := by decide +kernel
  exact h.trans h2

open OMA.S_oeis_a126476 in
lemma av3 : a 3 = 252 := by
  have h := a_succ 2
  have ek : U 2 u0 = vec [22, 29, 35, 40, 40, 35, 29, 22] := (E2 0).symm
  rw [ek] at h
  have h2 : ∑ d : Fin 8, vec [22, 29, 35, 40, 40, 35, 29, 22] d = 252 := by decide +kernel
  exact h.trans h2

open OMA.S_oeis_a126476 in
lemma av4 : a 4 = 1446 := by
  have h := a_succ 3
  have ek : U 3 u0 = vec [126, 166, 201, 230, 230, 201, 166, 126] := (E3 0).symm
  rw [ek] at h
  have h2 : ∑ d : Fin 8, vec [126, 166, 201, 230, 230, 201, 166, 126] d = 1446 := by decide +kernel
  exact h.trans h2

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A126476Aux

open OMA.S_oeis_a126476 A126476Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a126476.main := by
  refine ⟨?_, ?_⟩
  · have hD : (1 - 6 * X + X ^ 2 + 3 * X ^ 3 - X ^ 4 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (-6 : ℚ) * X ^ 1 + C (1 : ℚ) * X ^ 2 + C (3 : ℚ) * X ^ 3 + C (-1 : ℚ) * X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : (1 + 2 * X - 3 * X ^ 2 - X ^ 3 + X ^ 4 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (2 : ℚ) * X ^ 1 + C (-3 : ℚ) * X ^ 2 + C (-1 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 5 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3, av4]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
      rw [if_pos (show 0 ≤ m + 5 by omega),
        if_pos (show 1 ≤ m + 5 by omega),
        if_pos (show 2 ≤ m + 5 by omega),
        if_pos (show 3 ≤ m + 5 by omega),
        if_pos (show 4 ≤ m + 5 by omega),
        if_neg (show ¬ (m + 5 = 0) by omega),
        if_neg (show ¬ (m + 5 = 1) by omega),
        if_neg (show ¬ (m + 5 = 2) by omega),
        if_neg (show ¬ (m + 5 = 3) by omega),
        if_neg (show ¬ (m + 5 = 4) by omega)]
      rw [show m + 5 - 0 = m + 5 from by omega,
        show m + 5 - 1 = m + 4 from by omega,
        show m + 5 - 2 = m + 3 from by omega,
        show m + 5 - 3 = m + 2 from by omega,
        show m + 5 - 4 = m + 1 from by omega]
      have h := rec_a m
      have hq : (a (m + 5) : ℚ) + (a (m + 3) : ℚ) + 3 * (a (m + 2) : ℚ) = 6 * (a (m + 4) : ℚ) + (a (m + 1) : ℚ) := by
        exact_mod_cast h
      linarith
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 1 = m + 4 from by omega, show m + 5 - 2 = m + 3 from by omega, show m + 5 - 3 = m + 2 from by omega, show m + 5 - 4 = m + 1 from by omega]
    have h := rec_a m
    omega
