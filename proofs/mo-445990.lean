import OMAStatements.S_mo_445990
import Mathlib

open Finset Polynomial OMA.S_mo_445990

private abbrev P := ℤ[X]

private theorem sum_insert_outside (s : Finset ℕ) (f : Finset ℕ → P) :
    (∑ S ∈ s.powerset, ∑ j ∈ s \ S, f (insert j S)) =
      ∑ S ∈ s.powerset, (S.card : P) * f S := by
  classical
  have hfilter (S : Finset ℕ) : s \ S = s.filter (fun j => j ∉ S) := by
    ext j
    simp
  simp_rw [hfilter, sum_filter]
  rw [sum_comm]
  have hswap (j : ℕ) (hj : j ∈ s) :
      (∑ S ∈ s.powerset, if j ∉ S then f (insert j S) else 0) =
        ∑ S ∈ s.powerset, if j ∈ S then f S else 0 := by
    rw [← insert_erase hj, sum_powerset_insert (notMem_erase _ _),
      sum_powerset_insert (notMem_erase _ _)]
    have hnot (S : Finset ℕ) (hS : S ∈ (s.erase j).powerset) : j ∉ S :=
      fun hjS => notMem_erase j s (mem_powerset.mp hS hjS)
    rw [show ∑ S ∈ (s.erase j).powerset, (if j ∉ S then f (insert j S) else 0) =
        ∑ S ∈ (s.erase j).powerset, f (insert j S) from
        sum_congr rfl fun S hS => if_pos (hnot S hS)]
    rw [show ∑ S ∈ (s.erase j).powerset, (if j ∈ S then f S else 0) = 0 from
        (sum_congr rfl fun S hS => if_neg (hnot S hS)).trans sum_const_zero]
    simp
  rw [sum_congr rfl hswap, sum_comm]
  refine sum_congr rfl fun S hS => ?_
  rw [← sum_filter]
  have hsubset : s.filter (· ∈ S) = S := by
    ext j
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun hj => mem_powerset.mp hS hj
  rw [hsubset, sum_const, nsmul_eq_mul]

private noncomputable def affine (m k : ℤ) : P := C m - C k * X

private noncomputable def step (m k : ℤ) (N : ℕ) (p : P) : P :=
  X * (C (1 + k * (N : ℤ)) * p + affine m k * derivative p)

private noncomputable def weights (b : Finset ℕ → ℤ) (n : ℕ) : P :=
  ∑ S ∈ (range n).powerset, C (b S) * X ^ (n + 1 - S.card)

private theorem step_sum {ι : Type*} (s : Finset ι) (f : ι → P) (m k : ℤ) (N : ℕ) :
    step m k N (∑ i ∈ s, f i) = ∑ i ∈ s, step m k N (f i) := by
  simp only [step, derivative_sum, mul_add, mul_sum, sum_add_distrib]

private theorem step_Cmul (m k b : ℤ) (N : ℕ) (p : P) :
    step m k N (C b * p) = C b * step m k N p := by
  simp only [step, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

private theorem euler (p : P) (r : ℕ) :
    p * derivative (p ^ r) = C (r : ℤ) * derivative p * p ^ r := by
  cases r with
  | zero => simp
  | succ r =>
    rw [derivative_pow_succ, pow_succ]
    push_cast
    ring

private theorem step_X (m k : ℤ) (N c : ℕ) (hc : c < N) :
    step m k N (X ^ (N - c)) =
      C (m * (N - c : ℕ)) * X ^ (N - c) +
        C (1 + k * (c : ℤ)) * (X ^ (N - c) * X) := by
  have hcast : (N : ℤ) = (N - c : ℕ) + c := by omega
  simp only [step, affine, derivative_X_pow]
  have hpow : (X : P) ^ (N - c) = X ^ (N - c - 1) * X := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow, hcast]
  simp only [C_add, C_mul, C_1]
  ring

private theorem weights_succ (m k : ℤ) (b : Finset ℕ → ℤ)
    (hb : ∀ (d : ℕ) (S : Finset ℕ), S ⊆ range d →
        b (insert d S) = m * ((d + 1 - S.card : ℕ) : ℤ) * b S +
          ∑ j ∈ range d \ S, k * b (insert j S)) (n : ℕ) :
    weights b (n + 1) = step m k (n + 1) (weights b n) := by
  classical
  have hcard (S : Finset ℕ) (hS : S ∈ (range n).powerset) : S.card < n + 1 :=
    Nat.lt_succ_of_le (by simpa using card_le_card (mem_powerset.mp hS))
  have hnew (S : Finset ℕ) (hS : S ∈ (range n).powerset) : n ∉ S :=
    fun hs => notMem_range_self (mem_powerset.mp hS hs)
  have hshift : (∑ S ∈ (range n).powerset, ∑ j ∈ range n \ S,
      C (k * b (insert j S)) * X ^ (n + 1 - S.card)) =
      ∑ S ∈ (range n).powerset, (S.card : P) *
        (C (k * b S) * X ^ (n + 1 - S.card) * X) := by
    rw [← sum_insert_outside]
    refine sum_congr rfl fun S hS => sum_congr rfl fun j hj => ?_
    have hj' := mem_sdiff.mp hj
    rw [card_insert_of_notMem hj'.2, mul_assoc, ← pow_succ]
    have hs := hcard S hS
    rw [show n + 1 - (S.card + 1) + 1 = n + 1 - S.card by omega]
  rw [weights, range_add_one, sum_powerset_insert notMem_range_self, weights, step_sum]
  have hrewrite :
      (∑ S ∈ (range n).powerset, C (b (insert n S)) * X ^ (n + 1 + 1 - (insert n S).card)) =
        (∑ S ∈ (range n).powerset, C (m * (n + 1 - S.card : ℕ) * b S) * X ^ (n + 1 - S.card)) +
          ∑ S ∈ (range n).powerset, ∑ j ∈ range n \ S, C (k * b (insert j S)) * X ^ (n + 1 - S.card) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun S hS => ?_
    rw [hb n S (mem_powerset.mp hS), card_insert_of_notMem (hnew S hS)]
    rw [show n + 1 + 1 - (S.card + 1) = n + 1 - S.card by omega]
    rw [map_add, map_sum, add_mul, sum_mul]
  rw [hrewrite, hshift, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun S hS => ?_
  rw [step_Cmul, step_X m k _ _ (hcard S hS)]
  rw [show n + 1 + 1 - S.card = n + 1 - S.card + 1 by have := hcard S hS; omega, pow_succ]
  simp only [map_mul, map_add, map_one, C_eq_natCast]
  ring

private noncomputable def basisTerm (m k : ℤ) (N i : ℕ) : P :=
  X ^ i * affine m k ^ (N - i)

private def factors (k : ℤ) (i : ℕ) : ℤ :=
  ∏ j ∈ range i, (k * (j : ℤ) + 1)

private noncomputable def term (m k : ℤ) (N i : ℕ) : P :=
  C ((Nat.stirlingSecond N i : ℤ) * factors k i) * basisTerm m k N i

private noncomputable def closedPoly (m k : ℤ) (N : ℕ) : P :=
  ∑ i ∈ range (N + 1), term m k N i

private theorem step_basis (m k : ℤ) (N i : ℕ) (hi : i ≤ N) :
    step m k N (basisTerm m k N i) =
      C (1 + k * (i : ℤ)) * basisTerm m k (N + 1) (i + 1) +
        C (i : ℤ) * basisTerm m k (N + 1) i := by
  let u := affine m k
  let r := N - i
  have hN : (N : ℤ) = (i : ℤ) + (r : ℤ) := by dsimp [r]; omega
  have hu : derivative u = - C k := by simp [u, affine, derivative_mul]
  have hd : X * u * derivative (X ^ i * u ^ r) =
      (C (i : ℤ) * u - C (r : ℤ) * C k * X) * (X ^ i * u ^ r) := by
    rw [derivative_mul]
    calc
      X * u * (derivative (X ^ i) * u ^ r + X ^ i * derivative (u ^ r)) =
          (X * derivative (X ^ i)) * (u * u ^ r) +
            (u * derivative (u ^ r)) * (X * X ^ i) := by ring
      _ = _ := by
        rw [euler X i, euler u r, derivative_X, hu]
        ring
  simp only [basisTerm, show N + 1 - (i + 1) = r by simp [r],
    show N + 1 - i = r + 1 by dsimp [r]; omega]
  change X * (C (1 + k * (N : ℤ)) * (X ^ i * u ^ r) + u * derivative (X ^ i * u ^ r))
    = C (1 + k * (i : ℤ)) * (X ^ (i + 1) * u ^ r) + C (i : ℤ) * (X ^ i * u ^ (r + 1))
  rw [mul_add, ← mul_assoc X u, hd, hN, pow_succ X, pow_succ u]
  simp only [C_add, C_mul, C_1]
  ring

private noncomputable def stay (m k : ℤ) (N i : ℕ) : P :=
  C ((i : ℤ) * (Nat.stirlingSecond N i : ℤ) * factors k i) * basisTerm m k (N + 1) i

private noncomputable def advance (m k : ℤ) (N i : ℕ) : P :=
  C ((Nat.stirlingSecond N i : ℤ) * factors k (i + 1)) * basisTerm m k (N + 1) (i + 1)

private theorem step_term (m k : ℤ) (N i : ℕ) (hi : i ≤ N) :
    step m k N (term m k N i) = stay m k N i + advance m k N i := by
  simp only [term, stay, advance, step_Cmul, step_basis m k N i hi]
  rw [show factors k (i + 1) = factors k i * (k * (i : ℤ) + 1) by
    simp [factors, prod_range_succ]]
  simp only [C_add, C_1, C_mul]
  ring

private theorem term_succ (m k : ℤ) (N i : ℕ) :
    term m k (N + 1) (i + 1) = stay m k N (i + 1) + advance m k N i := by
  simp only [term, stay, advance, Nat.stirlingSecond_succ_succ, Nat.cast_add, Nat.cast_mul,
    C_add, C_mul]
  ring

private theorem closed_succ (m k : ℤ) (N : ℕ) :
    closedPoly m k (N + 1) = step m k N (closedPoly m k N) := by
  have hzero : stay m k N 0 = 0 := by simp [stay]
  have hend : stay m k N (N + 1) = 0 := by
    simp [stay, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self N)]
  have hshift : (∑ i ∈ range (N + 1), stay m k N (i + 1)) =
      ∑ i ∈ range (N + 1), stay m k N i := by
    calc
      _ = ∑ i ∈ range (N + 2), stay m k N i := by
        conv_rhs => rw [sum_range_succ', hzero, add_zero]
      _ = _ := by rw [sum_range_succ, hend, add_zero]
  unfold closedPoly
  rw [sum_range_succ', show term m k (N + 1) 0 = 0 by simp [term], add_zero,
    step_sum]
  simp_rw [term_succ m k N]
  rw [sum_add_distrib, hshift, ← sum_add_distrib]
  exact sum_congr rfl fun i hi => (step_term m k N i (Nat.le_of_lt_succ (mem_range.mp hi))).symm

theorem OMA.solution : type_of% @OMA.S_mo_445990.main := by
  intro m k b hb0 hb n
  have heq : weights b n = closedPoly m k (n + 1) := by
    induction n with
    | zero =>
      simp [weights, hb0, closedPoly, term, basisTerm, factors, sum_range_succ, Nat.stirlingSecond]
    | succ n ih =>
      rw [weights_succ m k b hb, ih, ← closed_succ m k (n + 1)]
  have heval := congrArg (evalRingHom (1 : ℤ)) heq
  simpa [weights, closedPoly, term, basisTerm, factors, affine, closedForm, Polynomial.eval_prod,
    mul_assoc, mul_left_comm, mul_comm] using heval
