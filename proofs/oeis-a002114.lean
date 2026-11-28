import OMAStatements.S_oeis_a002114

/-!
Peter Bala's eventual periodicity conjecture for Glaisher's H′ numbers.
Pair the two ends of each central difference to cancel the division by two.
Differences above the polynomial degree vanish, so two indices can be
compared with identical summation limits. The remaining powers stabilize
modulo each prime power with a period dividing Euler's totient.
Lean proof by KoaOkano, assisted by OpenAI Codex.
-/

open Finset OMA.S_oeis_a002114

private theorem powers_stabilize {m : ℕ} : 0 < m → ∀ b n d : ℕ, m ≤ n →
    m.totient ∣ d → b^(n+d) ≡ b^n [MOD m] := by
  induction m using Nat.recOnPrimeCoprime with
  | zero => omega
  | prime_pow p e hp =>
    intro hm b n d hn hd
    by_cases hb : p ∣ b
    · have he : e ≤ n := by
        have h₁ := Nat.lt_two_pow_self (n := e)
        have h₂ := Nat.pow_le_pow_left hp.two_le e
        omega
      have h : p^e ∣ b^n := (pow_dvd_pow_of_dvd hb e).trans (pow_dvd_pow b he)
      exact (h.trans (pow_dvd_pow b (by omega : n ≤ n+d))).modEq_zero_nat.trans
        h.modEq_zero_nat.symm
    · have hc : b.Coprime (p^e) := (hp.coprime_iff_not_dvd.mpr hb).symm.pow_right _
      obtain ⟨t, rfl⟩ := hd
      have h := ((Nat.ModEq.pow_totient hc).pow t).mul_left (b^n)
      simpa only [pow_add, pow_mul, one_pow, mul_one] using h
  | coprime u v hu hv huv ihu ihv =>
    intro hm b n d hn hd
    apply (Nat.modEq_and_modEq_iff_modEq_mul huv).mp
    constructor
    · apply ihu (by omega) b n d
      · exact (Nat.le_of_dvd hm (dvd_mul_right u v)).trans hn
      · exact (Nat.totient_dvd_of_dvd (dvd_mul_right u v)).trans hd
    · apply ihv (by omega) b n d
      · exact (Nat.le_of_dvd hm (dvd_mul_left v u)).trans hn
      · exact (Nat.totient_dvd_of_dvd (dvd_mul_left v u)).trans hd

private theorem powers_stabilize_mod {m n : ℕ} (hm : 0 < m) (hn : m ≤ n) (b : ZMod m) :
    b^(n + m.totient) = b^n := by
  have : NeZero m := ⟨hm.ne'⟩
  have h := (ZMod.natCast_eq_natCast_iff _ _ m).2
    (powers_stabilize hm b.val n m.totient hn dvd_rfl)
  simpa using h

private def term (n k j : ℕ) : ℤ :=
  (-1)^j * ((2*k).choose j : ℤ) * ((k:ℤ)-j)^(2*n)

private def row (n k : ℕ) : ℤ := (-1 : ℤ)^(n+k) * ∑ j ∈ range k, term n k j

private theorem sign_reflect {k j : ℕ} (hj : j ≤ 2*k) :
    (-1:ℤ)^(2*k-j) = (-1)^j := by
  calc
    _ = (-1:ℤ)^((2*k-j)%2) := neg_one_pow_eq_pow_mod_two _
    _ = (-1:ℤ)^(j%2) := by congr 1; omega
    _ = _ := (neg_one_pow_eq_pow_mod_two j).symm

private theorem reflected {n k j : ℕ} (hj : j ≤ 2*k) :
    term n k (2*k-j) = term n k j := by
  unfold term
  rw [sign_reflect hj, Nat.choose_symm hj, Nat.cast_sub hj, Nat.cast_mul, Nat.cast_ofNat,
    pow_mul, pow_mul]
  congr 2
  ring

private theorem double_sum {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ∑ j ∈ range (2*k+1), term n k j = 2 * ∑ j ∈ range k, term n k j := by
  have hmid : term n k k = 0 := by simp [term, hn.ne']
  have hr : ∑ i ∈ range k, term n k (k+1+i) = ∑ i ∈ range k, term n k i := by
    calc
      _ = ∑ i ∈ range k, term n k (k-1-i) := by
        apply sum_congr rfl
        intro i hi
        have hi' := mem_range.mp hi
        have h := reflected (n := n) (k := k) (j := k+1+i) (by omega)
        rw [show 2*k-(k+1+i) = k-1-i by omega] at h
        exact h.symm
      _ = _ := sum_range_reflect _ _
  rw [show 2*k+1 = (k+1)+k by omega, sum_range_add, sum_range_succ, hmid, hr]
  ring

private theorem row_zero {n k : ℕ} (hn : 0 < n) (hk : n < k) : row n k = 0 := by
  have h := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ)
    (show 2*n < 2*k by omega)) (-(k:ℤ))
  rw [fwdDiff_iter_eq_sum_shift] at h
  have hz : ∑ j ∈ range (2*k+1), term n k j = 0 := by
    refine Eq.trans (sum_congr rfl ?_) h
    intro j hj
    have hj' := mem_range.mp hj
    rw [sign_reflect (by omega : j ≤ 2*k)]
    simp only [term, zsmul_eq_mul, nsmul_eq_mul, mul_one, pow_mul]
    have he : (-(k:ℤ)+j)^2 = ((k:ℤ)-j)^2 := by ring
    rw [he]
    norm_cast
  rw [double_sum hn] at hz
  unfold row
  rw [show ∑ j ∈ range k, term n k j = 0 by omega, mul_zero]

private theorem padded {n K : ℕ} (hn : 0 < n) (hK : n ≤ K) :
    glaisherHPrime n = ∑ k ∈ range (K+1), row n k := by
  have h : glaisherHPrime n = ∑ k ∈ range (n+1), row n k := by
    unfold glaisherHPrime
    change (∑ k ∈ range (n+1), (-1:ℤ)^(n+k) *
      (∑ j ∈ range (2*k+1), term n k j)) / 2 = _
    simp_rw [double_sum hn]
    have hsum : (∑ k ∈ range (n+1), (-1:ℤ)^(n+k) *
        (2 * ∑ j ∈ range k, term n k j)) = 2 * ∑ k ∈ range (n+1), row n k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      unfold row
      ring
    rw [hsum]
    omega
  rw [h]
  apply sum_subset (range_mono (by omega))
  intro k _ hk
  apply row_zero hn
  simp only [mem_range, not_lt] at hk
  omega

private theorem row_powers (n k : ℕ) :
    row n k = ∑ j ∈ range k, (-1:ℤ)^(k+j) * ((2*k).choose j : ℤ) *
      (-(((k:ℤ)-j)^2))^n := by
  unfold row
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  unfold term
  rw [show -(((k:ℤ)-j)^2) = -1 * ((k:ℤ)-j)^2 by ring, mul_pow, pow_mul,
    pow_add, pow_add]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a002114.main := by
  intro m hm
  refine ⟨m.totient, m, Nat.totient_pos.mpr hm, dvd_rfl, hm, ?_⟩
  intro n hn
  rw [padded (K := n+m.totient) (by omega : 0 < n+m.totient) le_rfl,
    padded (K := n+m.totient) (by omega : 0 < n) (by omega)]
  apply (ZMod.intCast_eq_intCast_iff _ _ m).1
  push_cast
  apply sum_congr rfl
  intro k _
  rw [row_powers, row_powers]
  push_cast
  apply sum_congr rfl
  intro j _
  rw [powers_stabilize_mod hm hn]
