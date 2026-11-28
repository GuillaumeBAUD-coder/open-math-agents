import OMAStatements.S_oeis_a146564

-- Problem: A146564: a(n) is the number of solutions of the equation k*n/(k-n) = c. k,c integers.
-- Credit: @futurum-dev (the owner of the agent is credited as the solver)
-- Proof: k*n = (k-n)*n + n^2, so (k-n) ∣ k*n iff (k-n) ∣ n^2. The k > n are n + d for the
-- divisors d of n^2; the k < n are exactly the b of A063647 (c = b*n/(n-b)).

namespace OMA.P_oeis_a146564

open OMA.S_oeis_a146564

lemma key (k n : ℤ) : (k - n) ∣ k * n ↔ (k - n) ∣ n ^ 2 := by
  have h : k * n = (k - n) * n + n ^ 2 := by ring
  rw [h]
  exact dvd_add_right (dvd_mul_right _ _)

def U (n : ℕ) : Set ℕ := {k | n < k ∧ ((k : ℤ) - n) ∣ (n : ℤ) ^ 2}

def B (n : ℕ) : Set ℕ := {k | 0 < k ∧ k < n ∧ ((n : ℤ) - k) ∣ (n : ℤ) ^ 2}

lemma setA (n : ℕ) :
    {k : ℕ | 0 < k ∧ k ≠ n ∧ ((k : ℤ) - n) ∣ (k : ℤ) * n} = U n ∪ B n := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_union, U, B, key]
  have hneg : ((n : ℤ) - k) = -((k : ℤ) - n) := by ring
  rw [hneg, neg_dvd]
  constructor
  · rintro ⟨hk, hne, hd⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr ⟨hk, h, hd⟩
    · exact Or.inl ⟨h, hd⟩
  · rintro (⟨h, hd⟩ | ⟨hk, h, hd⟩)
    · exact ⟨by omega, by omega, hd⟩
    · exact ⟨hk, by omega, hd⟩

lemma U_eq (n : ℕ) (hn : 0 < n) :
    U n = (fun d => n + d) '' ((n ^ 2).divisors : Set ℕ) := by
  ext k
  simp only [U, Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, Nat.mem_divisors]
  constructor
  · rintro ⟨h, hd⟩
    refine ⟨k - n, ⟨?_, by positivity⟩, by omega⟩
    have hc : ((k : ℤ) - n) = ((k - n : ℕ) : ℤ) := by omega
    rw [hc] at hd
    exact_mod_cast hd
  · rintro ⟨d, ⟨hd, -⟩, rfl⟩
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by positivity)
    refine ⟨by omega, ?_⟩
    push_cast
    rw [add_sub_cancel_left]
    exact_mod_cast hd

lemma setB (n : ℕ) (hn : 0 < n) :
    {b : ℕ | 0 < b ∧ ∃ c : ℕ, b < c ∧ (1 : ℚ) / n = 1 / b - 1 / c} = B n := by
  ext b
  simp only [B, Set.mem_setOf_eq]
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  constructor
  · rintro ⟨hb, c, hbc, he⟩
    have hbq : (0 : ℚ) < b := by exact_mod_cast hb
    have hcq : (0 : ℚ) < c := by exact_mod_cast (hb.trans hbc)
    have hlt : b < n := by
      have h1 : (1 : ℚ) / n < 1 / b := by
        rw [he]; linarith [one_div_pos.mpr hcq]
      have : (b : ℚ) < n := by
        rwa [one_div_lt_one_div hnq hbq] at h1
      exact_mod_cast this
    refine ⟨hb, hlt, ?_⟩
    -- c * (n - b) = n * b
    have hq : (c : ℚ) * ((n : ℚ) - b) = n * b := by
      field_simp at he
      linear_combination -he
    have hz : (c : ℤ) * ((n : ℤ) - b) = n * b := by exact_mod_cast hq
    have h1 : ((n : ℤ) - b) ∣ (n : ℤ) * b := ⟨c, by rw [← hz]; ring⟩
    have h2 : (n : ℤ) ^ 2 = n * b + ((n : ℤ) - b) * n := by ring
    rw [h2]
    exact dvd_add h1 (dvd_mul_right _ _)
  · rintro ⟨hb, hlt, hd⟩
    have hc' : ((n : ℤ) - b) = ((n - b : ℕ) : ℤ) := by omega
    rw [hc'] at hd
    have hd' : (n - b) ∣ n ^ 2 := by exact_mod_cast hd
    obtain ⟨q, hq⟩ := hd'
    set e := n - b with he_def
    have hen : n = b + e := by omega
    have he0 : 0 < e := by omega
    -- e * q = n^2 = (b + e) * n, so q > b + n
    have hqn : b + n < q := by
      by_contra hcon
      push_neg at hcon
      have : e * q ≤ e * (b + n) := Nat.mul_le_mul_left e hcon
      have h3 : e * b < n * b := Nat.mul_lt_mul_of_pos_right (by omega) hb
      nlinarith
    refine ⟨hb, q - n, by omega, ?_⟩
    have hcq : ((q - n : ℕ) : ℚ) = (q : ℚ) - n := by
      rw [Nat.cast_sub (by omega)]
    rw [hcq]
    have hbq : (0 : ℚ) < b := by exact_mod_cast hb
    have heq : (e : ℚ) * q = (n : ℚ) ^ 2 := by exact_mod_cast hq.symm
    have hnq' : (n : ℚ) = b + e := by exact_mod_cast hen
    have hden : (q : ℚ) - n ≠ 0 := by
      have : (n : ℚ) < q := by exact_mod_cast (show n < q by omega)
      linarith
    field_simp
    rw [hnq'] at heq ⊢
    nlinarith [heq]

end OMA.P_oeis_a146564

open OMA.P_oeis_a146564 in
theorem OMA.solution : type_of% @OMA.S_oeis_a146564.main := by
  intro n hn
  unfold OMA.S_oeis_a146564.a OMA.S_oeis_a146564.A048691 OMA.S_oeis_a146564.A063647
  rw [setA, setB n hn]
  have hBfin : (B n).Finite :=
    (Set.finite_Iio n).subset (fun k hk => hk.2.1)
  have hUfin : (U n).Finite := by
    rw [U_eq n hn]; exact (Finset.finite_toSet _).image _
  have hdisj : Disjoint (U n) (B n) := by
    rw [Set.disjoint_left]
    intro k hU hB
    exact absurd hU.1 (by have := hB.2.1; omega)
  rw [Set.ncard_union_eq hdisj hUfin hBfin, U_eq n hn,
    Set.ncard_image_of_injective _ (fun x y h => by simpa using h), Set.ncard_coe_finset]
