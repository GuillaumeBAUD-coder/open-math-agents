import FormalConjectures.Wikipedia.Fermat

-- Reduction Fermat.fermat_number_are_composite.R1 of the question whether all Fermat numbers beyond F4 are composite
-- Credit: @marcusbuffett

/-!
# Composite Fermat numbers: the cases with a known factor from `F_5` to `F_19`, and the open rest

The question is whether `F_n = 2^(2^n) + 1` is composite for every `n > 4`.

* `H1` (known): `F_5, ..., F_19` are composite. Each has a known prime factor: `641 ∣ F_5` (Euler
  1732), `274177 ∣ F_6` (Landry 1880), and so on up to `70525124609 ∣ F_19` (Riesel 1962); the
  factor of `F_14` was only found in 2010. Proving `H1` means checking fifteen divisibilities.
* `H2`: `F_n` is composite for every `n ≥ 20`. This is open. (`F_20` is known to be composite by
  Pépin's test although no factor is known, and factors are known for many larger `n`, but no
  argument covers all `n`.)
-/

namespace OMA.R_Fermat_fermat_number_are_composite_R1

/-- `F_5, ..., F_19` are composite. -/
def H1 : Prop :=
  ∀ n : ℕ, 4 < n → n ≤ 19 → ¬ Prime n.fermatNumber

/-- The open part: `F_n` is composite for `n ≥ 20`. -/
def H2 : Prop :=
  ∀ n : ℕ, 20 ≤ n → ¬ Prime n.fermatNumber

theorem main : H1 → H2 → type_of% @Fermat.fermat_number_are_composite := by
  intro h1 h2 n hn
  by_cases hle : n ≤ 19
  · exact h1 n hn hle
  · exact h2 n (by omega)

end OMA.R_Fermat_fermat_number_are_composite_R1
