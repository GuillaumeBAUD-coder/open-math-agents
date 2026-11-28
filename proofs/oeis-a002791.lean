import OMAStatements.S_oeis_a002791

-- Problem: A002791: a(n) = Sum{d|n, d <= 4} d^2 + 4*Sum{d|n, d>4} d.
-- Upstream: formal-conjectures statements/oeis-a002791.lean:0 (declaration OMA.S_oeis_a002791.main)
-- Credit: @jaxon-zhou

open OMA.S_oeis_a002791

theorem OMA.solution : type_of% @OMA.S_oeis_a002791.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  let L := n.divisors.filter fun d => d ≤ 4
  let H := n.divisors.filter fun d => 4 < d

  have hDisj : Disjoint L H := by
    rw [Finset.disjoint_left]
    intro d hl hh
    simp only [L, H, Finset.mem_filter] at hl hh
    omega
  have hUnion : n.divisors = L ∪ H := by
    ext d
    simp only [L, H, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hd
      by_cases h : d ≤ 4
      · left; exact ⟨hd, h⟩
      · right; exact ⟨hd, by omega⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1

  have hσ : (ArithmeticFunction.sigma 1 n : ℤ) = ∑ d ∈ n.divisors, (d : ℤ) := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum]

  have ha : (a n : ℤ) =
      (∑ d ∈ L, (d : ℤ) ^ 2) + 4 * ∑ d ∈ H, (d : ℤ) := by
    unfold a
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_sum]
    rfl

  have hAlg : 4 * (∑ d ∈ n.divisors, (d : ℤ)) -
        ((∑ d ∈ L, (d : ℤ) ^ 2) + 4 * ∑ d ∈ H, (d : ℤ)) =
      ∑ d ∈ L, (4 * (d : ℤ) - (d : ℤ) ^ 2) := by
    rw [hUnion, Finset.sum_union hDisj, mul_add, Finset.mul_sum, Finset.mul_sum]
    have h : (∑ i ∈ L, 4 * (i : ℤ)) + (∑ i ∈ H, 4 * (i : ℤ)) -
          ((∑ d ∈ L, (d : ℤ) ^ 2) + ∑ i ∈ H, 4 * (i : ℤ)) =
        (∑ i ∈ L, (4 * (i : ℤ) - (i : ℤ) ^ 2)) + ∑ i ∈ H, (4 * (i : ℤ) - 4 * (i : ℤ)) := by
      rw [Finset.sum_sub_distrib (s := L), Finset.sum_sub_distrib (s := H)]
      ring
    rw [h]
    simp only [sub_self, Finset.sum_const_zero, add_zero]

  have hEq : L = ({1, 2, 3, 4} : Finset ℕ).filter fun d => d ∣ n := by
    ext d
    simp only [L, Finset.mem_filter,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hdv, hle⟩
      have hdiv : d ∣ n := (Nat.mem_divisors.mp hdv).1
      have hpos : 0 < d := Nat.pos_of_mem_divisors hdv
      have hmem : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by
        interval_cases d <;> omega
      exact ⟨by tauto, hdiv⟩
    · rintro ⟨hmem, hdiv⟩
      have hle : d ≤ 4 := by
        rcases hmem with rfl | rfl | rfl | rfl <;> omega
      exact ⟨Nat.mem_divisors.mpr ⟨hdiv, hn0⟩, hle⟩

  have hSum : ∑ d ∈ L, (4 * (d : ℤ) - (d : ℤ) ^ 2) =
      3 + 4 * (if 2 ∣ n then (1 : ℤ) else 0) +
        3 * (if 3 ∣ n then (1 : ℤ) else 0) := by
    rw [hEq, Finset.sum_filter]
    have hset : ({1, 2, 3, 4} : Finset ℕ) = insert 1 (insert 2 (insert 3 {4})) := rfl
    rw [hset, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_singleton]
    simp only [one_dvd, if_true]
    split_ifs with h2 h3 h4 <;> norm_num

  have h2 : (2 ∣ n) ↔ n % 6 = 0 ∨ n % 6 = 2 ∨ n % 6 = 4 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    constructor
    · intro h; omega
    · intro h; omega
  have h3 : (3 ∣ n) ↔ n % 6 = 0 ∨ n % 6 = 3 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    constructor <;> omega
  have hmod : n % 6 < 6 := Nat.mod_lt n (by omega)

  have hMain : 4 * (ArithmeticFunction.sigma 1 n : ℤ) - (a n : ℤ) = f (n % 6) := by
    rw [hσ, ha, hAlg, hSum]
    interval_cases n % 6 <;> simp [h2, h3, f]

  have hFinal : (a n : ℤ) = 4 * (ArithmeticFunction.sigma 1 n : ℤ) - f (n % 6) := by
    linarith
  exact hFinal
