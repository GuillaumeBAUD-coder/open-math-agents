import FormalConjectures.ErdosProblems.«367»

private def pell : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | t + 1 => let p := pell t; (3 * p.1 + 4 * p.2, 2 * p.1 + 3 * p.2)

open Erdos367 Asymptotics Filter in
theorem OMA.solution : type_of% @Erdos367.erdos_367.parts.ii := by
  intro H
  rcases isBigO_iff.1 (H 3 (by decide)) with ⟨C, hev⟩
  rcases eventually_atTop.1 hev with ⟨N0, hN0⟩
  have hpeq : ∀ t, (pell t).1 ^ 2 + 1 = 2 * (pell t).2 ^ 2 := fun t => by
    induction t with
    | zero => decide
    | succ t ih => dsimp [pell]; nlinarith
  have hpge : ∀ t, t + 1 ≤ (pell t).1 ∧ 1 ≤ (pell t).2 := fun t => by
    induction t with
    | zero => decide
    | succ t ih => dsimp [pell]; omega
  set M := Nat.ceil (2 * max C 0) + 2
  have hM2 : M ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  have : NeZero (M ^ 2) := ⟨hM2⟩
  let step (p : ZMod (M ^ 2) × ZMod (M ^ 2)) := (3 * p.1 + 4 * p.2, 2 * p.1 + 3 * p.2)
  have hinj : Function.Injective step :=
    Function.LeftInverse.injective (g := fun p => (3 * p.1 - 4 * p.2, -2 * p.1 + 3 * p.2))
      fun ⟨x, y⟩ => by ext <;> dsimp [step] <;> ring
  have hmod : ∀ t, (((pell t).1 : ZMod (M ^ 2)), ((pell t).2 : ZMod (M ^ 2))) = step^[t] (1, 1) := by
    intro t; induction t with
    | zero => simp [pell]
    | succ t ih => rw [Function.iterate_succ_apply', ← ih]; ext <;> simp [pell, step]
  rcases Finite.exists_ne_map_eq_of_infinite (fun t : ℕ => step^[t] (1, 1)) with ⟨i, j, hij, hEq⟩
  have ⟨L, hL1, hL⟩ : ∃ L, 1 ≤ L ∧ step^[L] (1, 1) = (1, 1) := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨j - i, by omega, hinj.iterate i (by rw [← Function.iterate_add_apply, Nat.add_sub_of_le h.le, hEq])⟩
    · exact ⟨i - j, by omega, hinj.iterate j (by rw [← Function.iterate_add_apply, Nat.add_sub_of_le h.le, hEq.symm])⟩
  set t := (N0 + 1) * L
  have hiter : ∀ r, step^[r * L] (1, 1) = (1, 1) := fun r => by
    induction r with
    | zero => simp
    | succ r ih => rw [add_mul, one_mul, Function.iterate_add_apply, hL, ih]
  set u := (pell t).1; set v := (pell t).2
  have hge := hpge t; have hpe : u ^ 2 + 1 = 2 * v ^ 2 := hpeq t
  have hu_ge : N0 + 2 ≤ u := by have : N0 + 1 ≤ t := Nat.le_mul_of_pos_right _ hL1; omega
  have hM_dvd : M ^ 2 ∣ u - 1 := by
    have h1 : (u : ZMod (M ^ 2)) = 1 := congr_arg Prod.fst ((hmod t).trans (hiter (N0 + 1)))
    exact (ZMod.natCast_eq_zero_iff (u - 1) (M ^ 2)).1 (by rw [Nat.cast_sub (by omega), Nat.cast_one, h1, sub_self])
  have hsqB : ∀ {d m : ℕ}, m ≠ 0 → d ^ 2 ∣ m → d ^ 2 ≤ B 2 m := by
    intro d m hm hd
    have hd0 : d ≠ 0 := fun h => hm (by simpa [h] using hd)
    have hfl : ∀ p, 2 * d.factorization p ≤ m.factorization p := fun p => by
      simpa [Nat.factorization_pow] using (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd0) hm).2 hd p
    have hd_eq : d ^ 2 = ∏ p ∈ d.factorization.support, p ^ (2 * d.factorization p) := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hd0]
      rw [Finsupp.prod, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun p _ => by rw [← pow_mul, mul_comm]
    have hBpos : 0 < B 2 m := Finset.prod_pos fun p hp =>
      pow_pos (Nat.prime_of_mem_primeFactors (by simpa [Nat.support_factorization] using (Finset.mem_filter.1 hp).1)).pos _
    refine Nat.le_of_dvd hBpos ?_
    rw [hd_eq, B]
    exact dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun p _ => Nat.pow_dvd_pow p (hfl p))
      (Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => by
        have := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hp); have := hfl p
        exact Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 (by omega), by omega⟩)
  set n := u ^ 2 - 1
  have hu2 : 4 ≤ u ^ 2 := by nlinarith
  have hnN : N0 ≤ n := by have : u ≤ u ^ 2 := (by nlinarith); dsimp [n]; omega
  have hndvd : M ^ 2 ∣ n := by
    have : n = (u - 1) * (u + 1) := by dsimp [n]; zify [show 1 ≤ u by omega, show 1 ≤ u ^ 2 by omega]; ring
    rw [this]; exact dvd_mul_of_dvd_left hM_dvd _
  have hB0 : M ^ 2 ≤ B 2 n := hsqB (by dsimp [n]; omega) hndvd
  have hB1 : u ^ 2 ≤ B 2 (n + 1) := hsqB (by omega) ⟨1, by dsimp [n]; omega⟩
  have hB2 : v ^ 2 ≤ B 2 (n + 2) := hsqB (by omega) ⟨2, by dsimp [n]; omega⟩
  have hprod : M ^ 2 * n ^ 2 ≤ 2 * ∏ m ∈ Finset.Ico n (n + 3), B 2 m := by
    have hIco : Finset.Ico n (n + 3) = {n, n + 1, n + 2} := by ext x; simp; omega
    rw [hIco, Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
    have hBp : M ^ 2 * u ^ 2 * v ^ 2 ≤ B 2 n * (B 2 (n + 1) * B 2 (n + 2)) := by
      have := Nat.mul_le_mul hB0 (Nat.mul_le_mul hB1 hB2); linarith
    have hn2 : n ^ 2 ≤ u ^ 2 * (2 * v ^ 2) := by
      rw [sq]; exact Nat.mul_le_mul (by dsimp [n]; omega) (by dsimp [n]; omega)
    nlinarith
  have hprodR : (M : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ 2 * ((∏ m ∈ Finset.Ico n (n + 3), B 2 m : ℕ) : ℝ) := by
    exact_mod_cast hprod
  have hbd := hN0 n hnN
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _)] at hbd
  have hMgt : 2 * C < (M : ℝ) ^ 2 := by
    have h1 := Nat.le_ceil (2 * max C 0)
    have h2 : (Nat.ceil (2 * max C 0) : ℝ) + 2 ≤ M := by dsimp [M]; push_cast; linarith
    nlinarith [le_max_left C 0, le_max_right C 0]
  have hnpos : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by dsimp [n]; omega)
    positivity
  nlinarith
