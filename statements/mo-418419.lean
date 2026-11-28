import Mathlib

/-!
# Extending a prime ideal along an integrally closed extension of domains

Source: https://mathoverflow.net/questions/418419
Credit: @koolkao

Question (Daniel W., MathOverflow 418419, 2022; CC BY-SA 4.0). Let `R ⊆ S` be an extension of
integral domains such that `R` is integrally closed in `S`. Let `P` be a prime ideal of `R`.
Is `PS` always a prime ideal of `S`?

`main` states that the answer is yes. A disproof is an extension `R ⊆ S` of domains with `R`
integrally closed in `S` and a prime `P` of `R` such that `PS` is not a prime ideal of `S`.

Translation choices:
* the extension `R ⊆ S` is an `Algebra R S` whose structure map `algebraMap R S` is injective
  (stated explicitly, although `IsIntegrallyClosedIn` also contains it); `R` and `S` are domains
  (`IsDomain`) in `Type`;
* "`R` is integrally closed in `S`" is Mathlib's `IsIntegrallyClosedIn R S`: every element of `S`
  integral over `R` lies in (the image of) `R`;
* `PS` is the extended ideal `P.map (algebraMap R S)`, and "prime ideal" is `Ideal.IsPrime`
  (a proper ideal `I` with `ab ∈ I → a ∈ I ∨ b ∈ I`), as usual;
* the source's follow-up question (whether it helps to assume that the domains are valuation
  rings) is not stated.
-/

namespace OMA.S_mo_418419

/-- If `R ⊆ S` are domains with `R` integrally closed in `S`, then `PS` is prime for every prime
`P` of `R`. -/
theorem main :
    ∀ (R S : Type) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S],
      Function.Injective (algebraMap R S) → IsIntegrallyClosedIn R S →
        ∀ P : Ideal R, P.IsPrime → (P.map (algebraMap R S)).IsPrime := by
  sorry

end OMA.S_mo_418419
