import OMAStatements.S_oeis_a268542

namespace OMA.P268542

open OMA.S_oeis_a268542

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
  (Nat.choose (N) (k) : ℚ) * (Nat.choose (N + k) (k) : ℚ) * (Nat.choose (2 * k) (N) : ℚ)

/-- The telescoping certificate. -/
def G (m k : ℕ) : ℚ :=
  ((-2 : ℚ) * (k : ℚ) * ((1212 : ℚ) + ((-1770 : ℚ) * (k : ℚ)) + ((63 : ℚ) * (m : ℚ) ^ 4) + ((78 : ℚ) * (k : ℚ) ^ 3) + ((554 : ℚ) * (m : ℚ) ^ 3) + ((1608 : ℚ) * (k : ℚ) ^ 2) + ((1775 : ℚ) * (m : ℚ) ^ 2) + ((2444 : ℚ) * (m : ℚ)) + ((-3213 : ℚ) * (k : ℚ) * (m : ℚ)) + ((-2064 : ℚ) * (k : ℚ) * (m : ℚ) ^ 2) + ((-582 : ℚ) * (k : ℚ) * (m : ℚ) ^ 3) + ((-63 : ℚ) * (k : ℚ) * (m : ℚ) ^ 4) + ((21 : ℚ) * (k : ℚ) ^ 3 * (m : ℚ) ^ 2) + ((89 : ℚ) * (m : ℚ) * (k : ℚ) ^ 3) + ((210 : ℚ) * (k : ℚ) ^ 2 * (m : ℚ) ^ 3) + ((1310 : ℚ) * (k : ℚ) ^ 2 * (m : ℚ) ^ 2) + ((2600 : ℚ) * (m : ℚ) * (k : ℚ) ^ 2))) / (((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)))
    * ((Nat.choose (m + 3) (k) : ℚ) * (Nat.choose (m + k + 3) (k) : ℚ) * (Nat.choose (2 * k) (m + 2) : ℚ))

set_option maxHeartbeats 4000000 in
lemma pt (m k : ℕ) :
    ((-3 : ℚ) * ((2 : ℚ) + ((3 : ℚ) * (m : ℚ))) * ((4 : ℚ) + ((3 : ℚ) * (m : ℚ))) * ((47 : ℚ) + ((21 : ℚ) * (m : ℚ)))) * T (m) k + ((-6126 : ℚ) + ((-11283 : ℚ) * (m : ℚ)) + ((-6710 : ℚ) * (m : ℚ) ^ 2) + ((-1281 : ℚ) * (m : ℚ) ^ 3)) * T (m + 1) k + ((-32 : ℚ) * ((18 : ℚ) + ((7 : ℚ) * (m : ℚ))) * ((9 : ℚ) + ((3 : ℚ) * (m : ℚ) ^ 2) + ((11 : ℚ) * (m : ℚ)))) * T (m + 2) k + ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) ^ 2 * ((26 : ℚ) + ((21 : ℚ) * (m : ℚ)))) * T (m + 3) k
      = G m (k + 1) - G m k := by
  have he1 := L1 (m + 2) (k) (m + 3) (k) (by ring) (by ring)
  push_cast at he1
  have me1 : (Nat.choose (m + 2) (k) : ℚ) * ((3 : ℚ) + (m : ℚ)) = ((3 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ))) * (Nat.choose (m + 3) (k) : ℚ) := by
    linear_combination ((-1 : ℚ)) * he1
  have me1c : (Nat.choose (m + 2) (k) : ℚ) * ((3 : ℚ) + (m : ℚ)) = ((3 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ))) * (Nat.choose (m + 3) (k) : ℚ) := by
    have hx : ((3 : ℚ) + (m : ℚ)) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((3 : ℚ) + (m : ℚ))) * me1
  have e1 : (Nat.choose (m + 2) (k) : ℚ) = ((3 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ))) * (Nat.choose (m + 3) (k) : ℚ) / ((3 : ℚ) + (m : ℚ)) := by
    have hx : ((3 : ℚ) + (m : ℚ)) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me1c
  have he2 := L1 (m + 1) (k) (m + 2) (k) (by ring) (by ring)
  push_cast at he2
  have me2 : (Nat.choose (m + 1) (k) : ℚ) * (((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) = (((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ)))) * (Nat.choose (m + 3) (k) : ℚ) := by
    linear_combination (((-3 : ℚ) + ((-1 : ℚ) * (m : ℚ)))) * he2 + (((2 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ)))) * me1c
  have me2c : (Nat.choose (m + 1) (k) : ℚ) * (((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) = (((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ)))) * (Nat.choose (m + 3) (k) : ℚ) := by
    have hx : (((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination ((((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)))) * me2
  have e2 : (Nat.choose (m + 1) (k) : ℚ) = (((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ)))) * (Nat.choose (m + 3) (k) : ℚ) / (((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) := by
    have hx : (((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me2c
  have he3 := L1 (m) (k) (m + 1) (k) (by ring) (by ring)
  push_cast at he3
  have me3 : (Nat.choose (m) (k) : ℚ) * (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) = ((-1 : ℚ) * ((-1 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ)))) * (Nat.choose (m + 3) (k) : ℚ) := by
    linear_combination (((-1 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)))) * he3 + (((1 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ)))) * me2c
  have me3c : (Nat.choose (m) (k) : ℚ) * (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) = ((-1 : ℚ) * ((-1 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ)))) * (Nat.choose (m + 3) (k) : ℚ) := by
    have hx : (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination ((((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)))) * me3
  have e3 : (Nat.choose (m) (k) : ℚ) = ((-1 : ℚ) * ((-1 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ)))) * (Nat.choose (m + 3) (k) : ℚ) / (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) := by
    have hx : (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me3c
  have he4 := L2 (m + 3) (k) (m + 3) (k + 1) (by ring) (by ring)
  push_cast at he4
  have me4 : (Nat.choose (m + 3) (k + 1) : ℚ) * ((1 : ℚ) + (k : ℚ)) = ((3 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ))) * (Nat.choose (m + 3) (k) : ℚ) := by
    linear_combination ((1 : ℚ)) * he4
  have me4c : (Nat.choose (m + 3) (k + 1) : ℚ) * ((1 : ℚ) + (k : ℚ)) = ((3 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ))) * (Nat.choose (m + 3) (k) : ℚ) := by
    have hx : ((1 : ℚ) + (k : ℚ)) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((1 : ℚ) + (k : ℚ))) * me4
  have e4 : (Nat.choose (m + 3) (k + 1) : ℚ) = ((3 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ))) * (Nat.choose (m + 3) (k) : ℚ) / ((1 : ℚ) + (k : ℚ)) := by
    have hx : ((1 : ℚ) + (k : ℚ)) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me4c
  have he5 := L1 ((m + 2) + k) (k) (m + k + 3) (k) (by ring) (by ring)
  push_cast at he5
  have me5 : (Nat.choose ((m + 2) + k) (k) : ℚ) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)) = ((3 : ℚ) + (m : ℚ)) * (Nat.choose (m + k + 3) (k) : ℚ) := by
    linear_combination ((-1 : ℚ)) * he5
  have me5c : (Nat.choose ((m + 2) + k) (k) : ℚ) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)) = ((3 : ℚ) + (m : ℚ)) * (Nat.choose (m + k + 3) (k) : ℚ) := by
    have hx : ((3 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((3 : ℚ) + (k : ℚ) + (m : ℚ))) * me5
  have e5 : (Nat.choose ((m + 2) + k) (k) : ℚ) = ((3 : ℚ) + (m : ℚ)) * (Nat.choose (m + k + 3) (k) : ℚ) / ((3 : ℚ) + (k : ℚ) + (m : ℚ)) := by
    have hx : ((3 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me5c
  have he6 := L1 ((m + 1) + k) (k) ((m + 2) + k) (k) (by ring) (by ring)
  push_cast at he6
  have me6 : (Nat.choose ((m + 1) + k) (k) : ℚ) * (((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) = (((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) * (Nat.choose (m + k + 3) (k) : ℚ) := by
    linear_combination (((-3 : ℚ) + ((-1 : ℚ) * (k : ℚ)) + ((-1 : ℚ) * (m : ℚ)))) * he6 + (((2 : ℚ) + (m : ℚ))) * me5c
  have me6c : (Nat.choose ((m + 1) + k) (k) : ℚ) * (((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) = (((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) * (Nat.choose (m + k + 3) (k) : ℚ) := by
    have hx : (((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination ((((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)))) * me6
  have e6 : (Nat.choose ((m + 1) + k) (k) : ℚ) = (((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) * (Nat.choose (m + k + 3) (k) : ℚ) / (((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) := by
    have hx : (((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me6c
  have he7 := L1 (m + k) (k) ((m + 1) + k) (k) (by ring) (by ring)
  push_cast at he7
  have me7 : (Nat.choose (m + k) (k) : ℚ) * (((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) = (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) * (Nat.choose (m + k + 3) (k) : ℚ) := by
    linear_combination (((-1 : ℚ) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)))) * he7 + (((1 : ℚ) + (m : ℚ))) * me6c
  have me7c : (Nat.choose (m + k) (k) : ℚ) * (((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) = (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) * (Nat.choose (m + k + 3) (k) : ℚ) := by
    have hx : (((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination ((((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)))) * me7
  have e7 : (Nat.choose (m + k) (k) : ℚ) = (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ))) * (Nat.choose (m + k + 3) (k) : ℚ) / (((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) := by
    have hx : (((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me7c
  have he8 := L3 (m + k + 3) (k) (m + (k + 1) + 3) (k + 1) (by ring) (by ring)
  push_cast at he8
  have me8 : (Nat.choose (m + (k + 1) + 3) (k + 1) : ℚ) * ((1 : ℚ) + (k : ℚ)) = ((4 : ℚ) + (k : ℚ) + (m : ℚ)) * (Nat.choose (m + k + 3) (k) : ℚ) := by
    linear_combination ((1 : ℚ)) * he8
  have me8c : (Nat.choose (m + (k + 1) + 3) (k + 1) : ℚ) * ((1 : ℚ) + (k : ℚ)) = ((4 : ℚ) + (k : ℚ) + (m : ℚ)) * (Nat.choose (m + k + 3) (k) : ℚ) := by
    have hx : ((1 : ℚ) + (k : ℚ)) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((1 : ℚ) + (k : ℚ))) * me8
  have e8 : (Nat.choose (m + (k + 1) + 3) (k + 1) : ℚ) = ((4 : ℚ) + (k : ℚ) + (m : ℚ)) * (Nat.choose (m + k + 3) (k) : ℚ) / ((1 : ℚ) + (k : ℚ)) := by
    have hx : ((1 : ℚ) + (k : ℚ)) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me8c
  have e9 : (Nat.choose ((m + 3) + k) (k) : ℚ) = (Nat.choose (m + k + 3) (k) : ℚ) := by
    rw [show (m + 3) + k = m + k + 3 from by ring]
  have he10 := L3 (2 * k + 1) (m + 1) (2 * (k + 1)) (m + 2) (by ring) (by ring)
  push_cast at he10
  have me10 : (Nat.choose (2 * k + 1) (m + 1) : ℚ) * ((2 : ℚ) * ((1 : ℚ) + (k : ℚ))) = ((2 : ℚ) + (m : ℚ)) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) := by
    linear_combination ((-1 : ℚ)) * he10
  have me10c : (Nat.choose (2 * k + 1) (m + 1) : ℚ) * ((2 : ℚ) + ((2 : ℚ) * (k : ℚ))) = ((2 : ℚ) + (m : ℚ)) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) := by
    have hx : ((2 : ℚ) * ((1 : ℚ) + (k : ℚ))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((2 : ℚ) + ((2 : ℚ) * (k : ℚ)))) * me10
  have he11 := L3 (2 * k) (m) (2 * k + 1) (m + 1) (by ring) (by ring)
  push_cast at he11
  have me11 : (Nat.choose (2 * k) (m) : ℚ) * ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) = (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ))) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) := by
    linear_combination (((-2 : ℚ) + ((-2 : ℚ) * (k : ℚ)))) * he11 + (((1 : ℚ) + (m : ℚ))) * me10c
  have me11c : (Nat.choose (2 * k) (m) : ℚ) * ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) = (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ))) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) := by
    have hx : ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))))) * me11
  have e11 : (Nat.choose (2 * k) (m) : ℚ) = (((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ))) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) / ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) := by
    have hx : ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me11c
  have he12 := L1 (2 * k + 1) (m + 2) (2 * (k + 1)) (m + 2) (by ring) (by ring)
  push_cast at he12
  have me12 : (Nat.choose (2 * k + 1) (m + 2) : ℚ) * ((2 : ℚ) * ((1 : ℚ) + (k : ℚ))) = (((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) := by
    linear_combination ((-1 : ℚ)) * he12
  have me12c : (Nat.choose (2 * k + 1) (m + 2) : ℚ) * ((2 : ℚ) + ((2 : ℚ) * (k : ℚ))) = (((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) := by
    have hx : ((2 : ℚ) * ((1 : ℚ) + (k : ℚ))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((2 : ℚ) + ((2 : ℚ) * (k : ℚ)))) * me12
  have he13 := L3 (2 * k) (m + 1) (2 * k + 1) (m + 2) (by ring) (by ring)
  push_cast at he13
  have me13 : (Nat.choose (2 * k) (m + 1) : ℚ) * ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) = (((2 : ℚ) + (m : ℚ)) * (((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) := by
    linear_combination (((-2 : ℚ) + ((-2 : ℚ) * (k : ℚ)))) * he13 + (((2 : ℚ) + (m : ℚ))) * me12c
  have me13c : (Nat.choose (2 * k) (m + 1) : ℚ) * ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) = (((2 : ℚ) + (m : ℚ)) * (((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) := by
    have hx : ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))))) * me13
  have e13 : (Nat.choose (2 * k) (m + 1) : ℚ) = (((2 : ℚ) + (m : ℚ)) * (((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) / ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) := by
    have hx : ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me13c
  have he14 := L1 (2 * k) (m + 2) (2 * k + 1) (m + 2) (by ring) (by ring)
  push_cast at he14
  have me14 : (Nat.choose (2 * k) (m + 2) : ℚ) * ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) = ((((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) := by
    linear_combination (((-2 : ℚ) + ((-2 : ℚ) * (k : ℚ)))) * he14 + (((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * me12c
  have me14c : (Nat.choose (2 * k) (m + 2) : ℚ) * ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) = ((((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) := by
    have hx : ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))))) * me14
  have e14 : (Nat.choose (2 * k) (m + 2) : ℚ) = ((((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) / ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) := by
    have hx : ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ)))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me14c
  have he15 := L2 (2 * k) (m + 2) (2 * k) (m + 3) (by ring) (by ring)
  push_cast at he15
  have me15 : (Nat.choose (2 * k) (m + 3) : ℚ) * ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ))) = ((((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-2 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) := by
    linear_combination (((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))))) * he15 + (((-2 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * me14c
  have me15c : (Nat.choose (2 * k) (m + 3) : ℚ) * ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ))) = ((((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-2 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) := by
    have hx : ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ)))) * me15
  have e15 : (Nat.choose (2 * k) (m + 3) : ℚ) = ((((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-2 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ) / ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ))) := by
    have hx : ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me15c
  have hd0 : ((1 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
  have hd0b : ((2 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
  have hd1 : ((2 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
  have hd1b : ((3 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
  have hd2 : ((3 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
  have hd2b : ((4 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
  have hD : ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ)) * ((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) ≠ 0 := by positivity
  have hF0 : T (m) k = ((-1 : ℚ) * ((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((-1 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ)))) * ((Nat.choose (m + 3) (k) : ℚ) * (Nat.choose (m + k + 3) (k) : ℚ) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ)) / ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ)) * ((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) := by
    simp only [T, e3, e7, e11]
    push_cast
    field
  have hF1 : T (m + 1) k = (((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * (((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ)))) * ((Nat.choose (m + 3) (k) : ℚ) * (Nat.choose (m + k + 3) (k) : ℚ) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ)) / ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ)) * ((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) := by
    simp only [T, e2, e6, e13]
    push_cast
    field
  have hF2 : T (m + 2) k = ((-1 : ℚ) * ((3 : ℚ) + (m : ℚ)) * (((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((2 : ℚ) + (k : ℚ) + (m : ℚ))) * ((Nat.choose (m + 3) (k) : ℚ) * (Nat.choose (m + k + 3) (k) : ℚ) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ)) / ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ)) * ((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) := by
    simp only [T, e1, e5, e14]
    push_cast
    field
  have hF3 : T (m + 3) k = ((((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-2 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) * ((Nat.choose (m + 3) (k) : ℚ) * (Nat.choose (m + k + 3) (k) : ℚ) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ)) / ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ)) * ((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) := by
    simp only [T, e9, e15]
    push_cast
    field
  have hG0 : G m k = ((-2 : ℚ) * (k : ℚ) * ((3 : ℚ) + (m : ℚ)) * (((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((-1 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((2 : ℚ) * (k : ℚ))) * ((1212 : ℚ) + ((-1770 : ℚ) * (k : ℚ)) + ((63 : ℚ) * (m : ℚ) ^ 4) + ((78 : ℚ) * (k : ℚ) ^ 3) + ((554 : ℚ) * (m : ℚ) ^ 3) + ((1608 : ℚ) * (k : ℚ) ^ 2) + ((1775 : ℚ) * (m : ℚ) ^ 2) + ((2444 : ℚ) * (m : ℚ)) + ((-3213 : ℚ) * (k : ℚ) * (m : ℚ)) + ((-2064 : ℚ) * (k : ℚ) * (m : ℚ) ^ 2) + ((-582 : ℚ) * (k : ℚ) * (m : ℚ) ^ 3) + ((-63 : ℚ) * (k : ℚ) * (m : ℚ) ^ 4) + ((21 : ℚ) * (k : ℚ) ^ 3 * (m : ℚ) ^ 2) + ((89 : ℚ) * (m : ℚ) * (k : ℚ) ^ 3) + ((210 : ℚ) * (k : ℚ) ^ 2 * (m : ℚ) ^ 3) + ((1310 : ℚ) * (k : ℚ) ^ 2 * (m : ℚ) ^ 2) + ((2600 : ℚ) * (m : ℚ) * (k : ℚ) ^ 2))) * ((Nat.choose (m + 3) (k) : ℚ) * (Nat.choose (m + k + 3) (k) : ℚ) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ)) / ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ)) * ((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) := by
    simp only [G, e14]
    push_cast
    field
  have hG1 : G m (k + 1) = ((4 : ℚ) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ)) * ((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((1128 : ℚ) + ((78 : ℚ) * (k : ℚ) ^ 3) + ((182 : ℚ) * (m : ℚ) ^ 3) + ((1042 : ℚ) * (m : ℚ) ^ 2) + ((1680 : ℚ) * (k : ℚ)) + ((1842 : ℚ) * (k : ℚ) ^ 2) + ((1920 : ℚ) * (m : ℚ)) + ((-162 : ℚ) * (k : ℚ) * (m : ℚ) ^ 3) + ((-63 : ℚ) * (k : ℚ) * (m : ℚ) ^ 4) + ((21 : ℚ) * (k : ℚ) ^ 3 * (m : ℚ) ^ 2) + ((89 : ℚ) * (m : ℚ) * (k : ℚ) ^ 3) + ((210 : ℚ) * (k : ℚ) ^ 2 * (m : ℚ) ^ 3) + ((619 : ℚ) * (k : ℚ) * (m : ℚ) ^ 2) + ((1373 : ℚ) * (k : ℚ) ^ 2 * (m : ℚ) ^ 2) + ((2254 : ℚ) * (k : ℚ) * (m : ℚ)) + ((2867 : ℚ) * (m : ℚ) * (k : ℚ) ^ 2))) * ((Nat.choose (m + 3) (k) : ℚ) * (Nat.choose (m + k + 3) (k) : ℚ) * (Nat.choose (2 * (k + 1)) (m + 2) : ℚ)) / ((2 : ℚ) * ((1 : ℚ) + (k : ℚ)) * ((1 : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ)) * ((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) := by
    simp only [G, e4, e8]
    push_cast
    field
  rw [hF0, hF1, hF2, hF3, hG1, hG0]
  ring

lemma aq (N : ℕ) : ((a (N) : ℤ) : ℚ) = ∑ k ∈ Finset.range (N + 1), T N k := by
  unfold a
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast, T]

lemma Tz (N k : ℕ) (h : N < k) : T N k = 0 := by
  have z : Nat.choose (N) (k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  unfold T
  rw [z]
  simp

lemma aqe (N M : ℕ) (h : N + 1 ≤ M) : ((a (N) : ℤ) : ℚ) = ∑ k ∈ Finset.range M, T N k := by
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

lemma Gtop (m : ℕ) : G m (m + 3 + 1) = 0 := by
  have z : Nat.choose (m + 3) (m + 3 + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  unfold G
  rw [z]
  simp

lemma recQ (m : ℕ) :
    ((-3 : ℚ) * ((2 : ℚ) + ((3 : ℚ) * (m : ℚ))) * ((4 : ℚ) + ((3 : ℚ) * (m : ℚ))) * ((47 : ℚ) + ((21 : ℚ) * (m : ℚ)))) * ((a (m) : ℤ) : ℚ) + ((-6126 : ℚ) + ((-11283 : ℚ) * (m : ℚ)) + ((-6710 : ℚ) * (m : ℚ) ^ 2) + ((-1281 : ℚ) * (m : ℚ) ^ 3)) * ((a (m + 1) : ℤ) : ℚ) + ((-32 : ℚ) * ((18 : ℚ) + ((7 : ℚ) * (m : ℚ))) * ((9 : ℚ) + ((3 : ℚ) * (m : ℚ) ^ 2) + ((11 : ℚ) * (m : ℚ)))) * ((a (m + 2) : ℤ) : ℚ) + ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) ^ 2 * ((26 : ℚ) + ((21 : ℚ) * (m : ℚ)))) * ((a (m + 3) : ℤ) : ℚ) = 0 := by
  have h := Finset.sum_congr (rfl : Finset.range (m + 3 + 1) = Finset.range (m + 3 + 1))
    (fun k _ => pt m k)
  rw [Finset.sum_range_sub, G0, Gtop] at h
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [aqe (m) (m + 3 + 1) (by omega), aqe (m + 1) (m + 3 + 1) (by omega), aqe (m + 2) (m + 3 + 1) (by omega), aqe (m + 3) (m + 3 + 1) (by omega)]
  linear_combination h

end R1

end OMA.P268542

open OMA.S_oeis_a268542 OMA.P268542 in
theorem OMA.solution : type_of% @OMA.S_oeis_a268542.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e3 : m + 3 - 3 = m := by omega
  rw [e1, e2, e3]
  have r := R1.recQ m
  apply Int.cast_injective (α := ℚ)
  push_cast
  linear_combination r
