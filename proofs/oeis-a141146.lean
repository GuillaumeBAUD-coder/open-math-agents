import OMAStatements.S_oeis_a141146

namespace OMA.P141146

open OMA.S_oeis_a141146

lemma L1 (A B A' B' : ℕ) (hA : A' = A + 1) (hB : B' = B) :
    (Nat.choose A' B' : ℚ) * ((A' : ℚ) - (B' : ℚ)) = (A' : ℚ) * (Nat.choose A B : ℚ) := by
  rw [hA, hB]
  by_cases h : B ≤ A + 1
  · have h1 := Nat.choose_mul_succ_eq A B
    have q : (Nat.choose A B : ℚ) * ((A : ℚ) + 1)
        = (Nat.choose (A + 1) B : ℚ) * (((A + 1 - B : ℕ)) : ℚ) := by exact_mod_cast h1
    rw [Nat.cast_sub h] at q
    push_cast at q ⊢
    linear_combination -q
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma L2 (A B A' B' : ℕ) (hA : A' = A) (hB : B' = B + 1) :
    (Nat.choose A' B' : ℚ) * (B' : ℚ) = (Nat.choose A B : ℚ) * ((A : ℚ) - (B : ℚ)) := by
  rw [hA, hB]
  by_cases h : B ≤ A
  · have h1 := Nat.choose_succ_right_eq A B
    have q : (Nat.choose A (B + 1) : ℚ) * ((B : ℚ) + 1)
        = (Nat.choose A B : ℚ) * (((A - B : ℕ)) : ℚ) := by exact_mod_cast h1
    rw [Nat.cast_sub h] at q
    push_cast at q ⊢
    linear_combination q
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma L3 (A B A' B' : ℕ) (hA : A' = A + 1) (hB : B' = B + 1) :
    (Nat.choose A' B' : ℚ) * (B' : ℚ) = (A' : ℚ) * (Nat.choose A B : ℚ) := by
  rw [hA, hB]
  have h1 := Nat.add_one_mul_choose_eq A B
  have q : ((A : ℚ) + 1) * (Nat.choose A B : ℚ)
      = (Nat.choose (A + 1) (B + 1) : ℚ) * ((B : ℚ) + 1) := by exact_mod_cast h1
  push_cast at q ⊢
  linear_combination -q

namespace R1



/-- The summand, as a rational number. -/
def T (N k : ℕ) : ℚ :=
  (Nat.choose (N) (2 * k) : ℚ) * (Nat.choose (2 * k) (k) : ℚ) * (Nat.choose (N + k) (k + 1) : ℚ) * (2 : ℚ) ^ (N) * ((1 : ℚ) / 4) ^ (k)

/-- The telescoping certificate. -/
def G (m k : ℕ) : ℚ :=
  ((24 : ℚ) * (k : ℚ) ^ 2 * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + (m : ℚ)) * ((4 : ℚ) + ((3 : ℚ) * (m : ℚ)))) / (((2 : ℚ) + (m : ℚ)) * ((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)))
    * ((Nat.choose (m + 2) (2 * k) : ℚ) * (Nat.choose (2 * k) (k) : ℚ) * (Nat.choose (m + k + 2) (k + 1) : ℚ) * (2 : ℚ) ^ (m) * ((1 : ℚ) / 4) ^ (k))

lemma pt (m k : ℕ) :
    ((8 : ℚ) * ((1 : ℚ) + (m : ℚ)) ^ 2) * T (m) k + ((28 : ℚ) + ((7 : ℚ) * (m : ℚ) ^ 2) + ((29 : ℚ) * (m : ℚ))) * T (m + 1) k + ((-1 : ℚ) * ((1 : ℚ) + (m : ℚ)) * ((4 : ℚ) + (m : ℚ))) * T (m + 2) k
      = G m (k + 1) - G m k := by
  have he1 := L1 (m + 1) (2 * k) (m + 2) (2 * k) (by ring) (by ring)
  push_cast at he1
  have me1 : (Nat.choose (m + 1) (2 * k) : ℚ) * ((2 : ℚ) + (m : ℚ)) = ((2 : ℚ) + (m : ℚ) + ((-2 : ℚ) * (k : ℚ))) * (Nat.choose (m + 2) (2 * k) : ℚ) := by
    linear_combination ((-1 : ℚ)) * he1
  have me1c : (Nat.choose (m + 1) (2 * k) : ℚ) * ((2 : ℚ) + (m : ℚ)) = ((2 : ℚ) + (m : ℚ) + ((-2 : ℚ) * (k : ℚ))) * (Nat.choose (m + 2) (2 * k) : ℚ) := by
    have hx : ((2 : ℚ) + (m : ℚ)) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((2 : ℚ) + (m : ℚ))) * me1
  have e1 : (Nat.choose (m + 1) (2 * k) : ℚ) = ((2 : ℚ) + (m : ℚ) + ((-2 : ℚ) * (k : ℚ))) * (Nat.choose (m + 2) (2 * k) : ℚ) / ((2 : ℚ) + (m : ℚ)) := by
    have hx : ((2 : ℚ) + (m : ℚ)) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me1c
  have he2 := L1 (m) (2 * k) (m + 1) (2 * k) (by ring) (by ring)
  push_cast at he2
  have me2 : (Nat.choose (m) (2 * k) : ℚ) * (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ))) = (((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-2 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (m + 2) (2 * k) : ℚ) := by
    linear_combination (((-2 : ℚ) + ((-1 : ℚ) * (m : ℚ)))) * he2 + (((1 : ℚ) + (m : ℚ) + ((-2 : ℚ) * (k : ℚ)))) * me1c
  have me2c : (Nat.choose (m) (2 * k) : ℚ) * (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ))) = (((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-2 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (m + 2) (2 * k) : ℚ) := by
    have hx : (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination ((((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)))) * me2
  have e2 : (Nat.choose (m) (2 * k) : ℚ) = (((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-2 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (m + 2) (2 * k) : ℚ) / (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ))) := by
    have hx : (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me2c
  have he3 := L2 (m + 2) (2 * k) (m + 2) (2 * k + 1) (by ring) (by ring)
  push_cast at he3
  have me3 : (Nat.choose (m + 2) (2 * k + 1) : ℚ) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) = ((2 : ℚ) + (m : ℚ) + ((-2 : ℚ) * (k : ℚ))) * (Nat.choose (m + 2) (2 * k) : ℚ) := by
    linear_combination ((1 : ℚ)) * he3
  have me3c : (Nat.choose (m + 2) (2 * k + 1) : ℚ) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) = ((2 : ℚ) + (m : ℚ) + ((-2 : ℚ) * (k : ℚ))) * (Nat.choose (m + 2) (2 * k) : ℚ) := by
    have hx : ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) * me3
  have he4 := L2 (m + 2) (2 * k + 1) (m + 2) (2 * (k + 1)) (by ring) (by ring)
  push_cast at he4
  have me4 : (Nat.choose (m + 2) (2 * (k + 1)) : ℚ) * ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) = (((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-2 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (m + 2) (2 * k) : ℚ) := by
    linear_combination (((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) * he4 + (((1 : ℚ) + (m : ℚ) + ((-2 : ℚ) * (k : ℚ)))) * me3c
  have me4c : (Nat.choose (m + 2) (2 * (k + 1)) : ℚ) * ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) = (((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-2 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (m + 2) (2 * k) : ℚ) := by
    have hx : ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))))) * me4
  have e4 : (Nat.choose (m + 2) (2 * (k + 1)) : ℚ) = (((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-2 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (m + 2) (2 * k) : ℚ) / ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) := by
    have hx : ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me4c
  have he5 := L1 (2 * k) (k) (2 * k + 1) (k) (by ring) (by ring)
  push_cast at he5
  have me5 : (Nat.choose (2 * k + 1) (k) : ℚ) * ((1 : ℚ) + (k : ℚ)) = ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * (Nat.choose (2 * k) (k) : ℚ) := by
    linear_combination ((1 : ℚ)) * he5
  have me5c : (Nat.choose (2 * k + 1) (k) : ℚ) * ((1 : ℚ) + (k : ℚ)) = ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * (Nat.choose (2 * k) (k) : ℚ) := by
    have hx : ((1 : ℚ) + (k : ℚ)) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((1 : ℚ) + (k : ℚ))) * me5
  have he6 := L3 (2 * k + 1) (k) (2 * (k + 1)) (k + 1) (by ring) (by ring)
  push_cast at he6
  have me6 : (Nat.choose (2 * (k + 1)) (k + 1) : ℚ) * ((1 : ℚ) + (k : ℚ)) ^ 2 = ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (2 * k) (k) : ℚ) := by
    linear_combination (((1 : ℚ) + (k : ℚ))) * he6 + (((2 : ℚ) * ((1 : ℚ) + (k : ℚ)))) * me5c
  have me6c : (Nat.choose (2 * (k + 1)) (k + 1) : ℚ) * ((1 : ℚ) + (k : ℚ)) = ((2 : ℚ) + ((4 : ℚ) * (k : ℚ))) * (Nat.choose (2 * k) (k) : ℚ) := by
    have hx : ((1 : ℚ) + (k : ℚ)) ^ 2 ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((1 : ℚ) + (k : ℚ))) * me6
  have e6 : (Nat.choose (2 * (k + 1)) (k + 1) : ℚ) = ((2 : ℚ) + ((4 : ℚ) * (k : ℚ))) * (Nat.choose (2 * k) (k) : ℚ) / ((1 : ℚ) + (k : ℚ)) := by
    have hx : ((1 : ℚ) + (k : ℚ)) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me6c
  have he7 := L1 ((m + 1) + k) (k + 1) (m + k + 2) (k + 1) (by ring) (by ring)
  push_cast at he7
  have me7 : (Nat.choose ((m + 1) + k) (k + 1) : ℚ) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) = ((1 : ℚ) + (m : ℚ)) * (Nat.choose (m + k + 2) (k + 1) : ℚ) := by
    linear_combination ((-1 : ℚ)) * he7
  have me7c : (Nat.choose ((m + 1) + k) (k + 1) : ℚ) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) = ((1 : ℚ) + (m : ℚ)) * (Nat.choose (m + k + 2) (k + 1) : ℚ) := by
    have hx : ((2 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((2 : ℚ) + (k : ℚ) + (m : ℚ))) * me7
  have e7 : (Nat.choose ((m + 1) + k) (k + 1) : ℚ) = ((1 : ℚ) + (m : ℚ)) * (Nat.choose (m + k + 2) (k + 1) : ℚ) / ((2 : ℚ) + (k : ℚ) + (m : ℚ)) := by
    have hx : ((2 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me7c
  have he8 := L1 (m + k) (k + 1) ((m + 1) + k) (k + 1) (by ring) (by ring)
  push_cast at he8
  have me8 : (Nat.choose (m + k) (k + 1) : ℚ) * (((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ))) = ((m : ℚ) * ((1 : ℚ) + (m : ℚ))) * (Nat.choose (m + k + 2) (k + 1) : ℚ) := by
    linear_combination (((-2 : ℚ) + ((-1 : ℚ) * (k : ℚ)) + ((-1 : ℚ) * (m : ℚ)))) * he8 + ((m : ℚ)) * me7c
  have me8c : (Nat.choose (m + k) (k + 1) : ℚ) * (((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ))) = ((m : ℚ) * ((1 : ℚ) + (m : ℚ))) * (Nat.choose (m + k + 2) (k + 1) : ℚ) := by
    have hx : (((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination ((((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)))) * me8
  have e8 : (Nat.choose (m + k) (k + 1) : ℚ) = ((m : ℚ) * ((1 : ℚ) + (m : ℚ))) * (Nat.choose (m + k + 2) (k + 1) : ℚ) / (((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ))) := by
    have hx : (((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me8c
  have he9 := L3 (m + k + 2) (k + 1) (m + (k + 1) + 2) ((k + 1) + 1) (by ring) (by ring)
  push_cast at he9
  have me9 : (Nat.choose (m + (k + 1) + 2) ((k + 1) + 1) : ℚ) * ((2 : ℚ) + (k : ℚ)) = ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * (Nat.choose (m + k + 2) (k + 1) : ℚ) := by
    linear_combination ((1 : ℚ)) * he9
  have me9c : (Nat.choose (m + (k + 1) + 2) ((k + 1) + 1) : ℚ) * ((2 : ℚ) + (k : ℚ)) = ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * (Nat.choose (m + k + 2) (k + 1) : ℚ) := by
    have hx : ((2 : ℚ) + (k : ℚ)) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((2 : ℚ) + (k : ℚ))) * me9
  have e9 : (Nat.choose (m + (k + 1) + 2) ((k + 1) + 1) : ℚ) = ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * (Nat.choose (m + k + 2) (k + 1) : ℚ) / ((2 : ℚ) + (k : ℚ)) := by
    have hx : ((2 : ℚ) + (k : ℚ)) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me9c
  have e10 : (Nat.choose ((m + 2) + k) (k + 1) : ℚ) = (Nat.choose (m + k + 2) (k + 1) : ℚ) := by
    rw [show (m + 2) + k = m + k + 2 from by ring]
  have hd0 : ((2 : ℚ) + (m : ℚ)) ≠ 0 := by positivity
  have hd1 : ((1 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
  have hd1b : ((2 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
  have hd2 : ((2 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
  have hd2b : ((3 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
  simp only [T, G]
  rw [e1, e2, e4, e6, e7, e8, e9, e10]
  push_cast
  field_simp
  ring

lemma aq (N : ℕ) : ((a (N + 1) : ℤ) : ℚ) = ∑ k ∈ Finset.range (N + 1), T N k := by
  have tz : ∀ x, N < 2 * x → T N x = 0 := by
    intro x hx
    have z : Nat.choose N (2 * x) = 0 := Nat.choose_eq_zero_of_lt hx
    unfold T
    rw [z]
    simp
  have hsub : Finset.range ((N + 1) / 2 + 1) ⊆ Finset.range (N + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  rw [← Finset.sum_subset hsub (fun x _ hx => tz x (by rw [Finset.mem_range] at hx; omega))]
  unfold a
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  simp only [Nat.add_sub_cancel]
  push_cast
  by_cases h2 : 2 * k ≤ N
  · have hp : (2 : ℚ) ^ (N - 2 * k) = 2 ^ N * (1 / 4) ^ k := by
      have h3 : (2 : ℚ) ^ N = 2 ^ (N - 2 * k) * 4 ^ k := by
        rw [show (4 : ℚ) = 2 ^ 2 from by norm_num, ← pow_mul, ← pow_add]
        congr 1
        omega
      rw [h3, mul_assoc, ← mul_pow]
      norm_num
    rw [hp, T]
    ring
  · rw [tz k (by omega)]
    have z : Nat.choose N (2 * k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [z]
    simp

lemma Tz (N k : ℕ) (h : N < k) : T N k = 0 := by
  have z : Nat.choose (N) (2 * k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  unfold T
  rw [z]
  simp

lemma aqe (N M : ℕ) (h : N + 1 ≤ M) : ((a (N + 1) : ℤ) : ℚ) = ∑ k ∈ Finset.range M, T N k := by
  rw [aq]
  apply Finset.sum_subset
  · intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  · intro x _ hx
    rw [Finset.mem_range] at hx
    exact Tz N x (by omega)

lemma G0 (m : ℕ) : G m 0 = 0 := by
  unfold G
  simp

lemma Gtop (m : ℕ) : G m (m + 2 + 1) = 0 := by
  have z : Nat.choose (m + 2) (2 * (m + 2 + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  unfold G
  rw [z]
  simp

lemma recQ (m : ℕ) :
    ((8 : ℚ) * ((1 : ℚ) + (m : ℚ)) ^ 2) * ((a (m + 1) : ℤ) : ℚ) + ((28 : ℚ) + ((7 : ℚ) * (m : ℚ) ^ 2) + ((29 : ℚ) * (m : ℚ))) * ((a (m + 1 + 1) : ℤ) : ℚ) + ((-1 : ℚ) * ((1 : ℚ) + (m : ℚ)) * ((4 : ℚ) + (m : ℚ))) * ((a (m + 2 + 1) : ℤ) : ℚ) = 0 := by
  have h := Finset.sum_congr (rfl : Finset.range (m + 2 + 1) = Finset.range (m + 2 + 1))
    (fun k _ => pt m k)
  rw [Finset.sum_range_sub, G0, Gtop] at h
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [aqe (m) (m + 2 + 1) (by omega), aqe (m + 1) (m + 2 + 1) (by omega), aqe (m + 2) (m + 2 + 1) (by omega)]
  linear_combination h

end R1

end OMA.P141146

open OMA.S_oeis_a141146 OMA.P141146 in
theorem OMA.solution : type_of% @OMA.S_oeis_a141146.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 1 + 1 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  rw [e1, e2]
  have r := R1.recQ m
  apply Int.cast_injective (α := ℚ)
  push_cast
  linear_combination r
