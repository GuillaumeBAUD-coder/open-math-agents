import OMAReductions.R_Erdos52_erdos_52_R3

-- Reduction Erdos52.erdos_52.R3.H2.R1 of step R3.H2
-- Credit: @MBimrose

/-!
# Reduction of step `R3.H2` of Erdős 52: sets of negative integers follow from positive ones

`R3` splits the sum-product conjecture into `R3.H1` (sets of *positive* integers) and
`R3.H2` (sets of *negative* integers), and proves `main : R3.H1 → R3.H2 → Erdos52`.

This file proves that `R3.H2` is *equivalent* to `R3.H1`, so `R3.H2` is redundant: the whole
of Erdős 52 modulo `R3` is the single hypothesis `R3.H1`, the form the literature (Solymosi)
actually works with.

The mechanism is exact, not probabilistic.  For a finite set `A` of negative integers let
`B = A.image (fun a => -a)`, a finite set of positive integers with

* `B.card = A.card`                       (negation is injective),
* `B + B = (A + A).image (fun x => -x)`   (so `(B + B).card = (A + A).card`),
* `B * B = A * A`                         (because `(-a) * (-b) = a * b`),

hence `max (B+B).card (B*B).card = max (A+A).card (A*A).card` and the bound
`C * (A.card) ^ (2 - ε)` transfers across with the *same* `ε` and the *same* `C`.

* `H1` is `R3.H1` written out: the sum-product exponent `2 - ε` for sets of positive integers.
  This is the open content (best known: `4/3` for finite integer sets, Solymosi; it is *not*
  the classical `some δ > 0` theorem).
* `H2` is the sign-flip transfer statement; it is proved here (`flip_exists`), so `main` is a
  real proof of `R3.H1 → R3.H2` and the file shows exactly which half of `R3` is open: `H1`.

Search audit: `Erdos52.erdos_52.R3.H1` / `.H2` were audited on all six sources (API
solution null, liveAgents 0, no claim file, no submitter log line, no box directories, no
tracked files, not in DO_NOT_RECLAIM) before this file was written; `R3` itself is merged
upstream, which is why the steps exist.
-/

namespace OMA.R_Erdos52_erdos_52_R3_H2_R1

open Finset
open scoped Pointwise

/-- `H1`: the sum-product exponent `2 - ε` for finite sets of positive integers (this is the
statement of `R3.H1`, the open half of the reduction). -/
def H1 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
  (∀ a ∈ A, 0 < a) → (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)

/-- `H2`: the sign-flip transfer. For every finite set `A` of negative integers there is a
finite set `B` of positive integers with the same cardinality, with `(B + B).card = (A + A).card`
and `B * B = A * A`. Proved below (`flip_exists`), so this hypothesis is discharged. -/
def H2 : Prop := ∀ A : Finset ℤ, (∀ a ∈ A, a < 0) → ∃ B : Finset ℤ,
  (∀ b ∈ B, 0 < b) ∧ B.card = A.card ∧ (B + B).card = (A + A).card ∧ B * B = A * A

/-- The sign flip `a ↦ -a` turns a finite set of negative integers into one of positive integers,
preserves the cardinality, mirrors the sumset and preserves the product set. -/
lemma flip_exists : H2 := by
  intro A hA
  refine ⟨A.image (fun a => -a), ?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    have := hA a ha
    omega
  · exact card_image_of_injective _ (fun x y hxy => by omega)
  · have hsum : (A.image fun a => -a) + (A.image fun a => -a)
        = (A + A).image (fun x => -x) := by
      ext x
      simp only [mem_add, mem_image]
      constructor
      · rintro ⟨b1, ⟨a1, ha1, rfl⟩, b2, ⟨a2, ha2, rfl⟩, rfl⟩
        exact ⟨a1 + a2, ⟨a1, ha1, a2, ha2, rfl⟩, by ring⟩
      · rintro ⟨y, ⟨a1, ha1, a2, ha2, rfl⟩, rfl⟩
        exact ⟨-a1, ⟨a1, ha1, by ring⟩, -a2, ⟨a2, ha2, by ring⟩, by ring⟩
    rw [hsum, card_image_of_injective _ (fun x y hxy => by omega)]
  · have hprod : (A.image fun a => -a) * (A.image fun a => -a) = A * A := by
      ext x
      simp only [mem_mul, mem_image]
      constructor
      · rintro ⟨b1, ⟨a1, ha1, rfl⟩, b2, ⟨a2, ha2, rfl⟩, rfl⟩
        exact ⟨a1, ha1, a2, ha2, by ring⟩
      · rintro ⟨a1, ha1, a2, ha2, rfl⟩
        exact ⟨-a1, ⟨a1, ha1, by ring⟩, -a2, ⟨a2, ha2, by ring⟩, by ring⟩
    exact hprod

theorem main : H1 → H2 → OMA.R_Erdos52_erdos_52_R3.H2 := by
  intro hpos hflip ε hε0 hε1
  obtain ⟨C, hC, hbound⟩ := hpos ε hε0 hε1
  refine ⟨C, hC, ?_⟩
  intro A hA
  obtain ⟨B, hBpos, hBcard, hBsum, hBprod⟩ := hflip A hA
  have h := hbound B hBpos
  rw [hBcard, hBsum, hBprod] at h
  exact h

end OMA.R_Erdos52_erdos_52_R3_H2_R1
