import OMAReductions.R_oeis_a070247_R1

-- A proper divisor for each exponent. Larger divisors were obtained from FactorDB
-- and are checked here by natural-number arithmetic.
namespace DecimalFermat

def repeatedSquare : Nat → Nat
  | 0 => 10
  | k + 1 => let v := repeatedSquare k; v * v

theorem power_eq (k : Nat) : 10 ^ (2 ^ k) = repeatedSquare k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ (2 : Nat), pow_mul, ih, pow_two]; rfl

theorem composite_of_factor (n d : Nat) (hd : d ∣ n) (h1 : d ≠ 1) (hn : d ≠ n) : ¬ Nat.Prime n :=
  Nat.not_prime_of_dvd_of_ne hd h1 hn

end DecimalFermat

set_option maxRecDepth 8192 in
theorem OMA.solution : OMA.R_oeis_a070247_R1.H1 := by
  intro k hk hk'
  rw [DecimalFermat.power_eq]
  interval_cases k
  · exact DecimalFermat.composite_of_factor _ 73 (by decide) (by decide) (by decide)
  · exact DecimalFermat.composite_of_factor _ 17 (by decide) (by decide) (by decide)
  · exact DecimalFermat.composite_of_factor _ 353 (by decide) (by decide) (by decide)
  · exact DecimalFermat.composite_of_factor _ 19841 (by decide) (by decide) (by decide)
  · exact DecimalFermat.composite_of_factor _ 1265011073 (by decide) (by decide) (by decide)
  · exact DecimalFermat.composite_of_factor _ 257 (by decide) (by decide) (by decide)
  · exact DecimalFermat.composite_of_factor _ 10753 (by decide) (by decide) (by decide)
  · exact DecimalFermat.composite_of_factor _ 1514497 (by decide) (by decide) (by decide)
  · exact DecimalFermat.composite_of_factor _ 1856104284667693057 (by decide) (by decide) (by decide)
  · exact DecimalFermat.composite_of_factor _ 106907803649 (by decide) (by decide) (by decide)
  · exact DecimalFermat.composite_of_factor _ 458924033 (by decide) (by decide) (by decide)
  · exact DecimalFermat.composite_of_factor _ 3635898263938497962802538435084289 (by decide) (by decide) (by decide)
  · exact DecimalFermat.composite_of_factor _ 1702047085242613845984907230501142529 (by decide) (by decide) (by decide)
