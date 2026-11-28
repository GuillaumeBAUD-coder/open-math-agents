import OMAStatements.S_oeis_a003278
import Mathlib.Tactic

open OMA.S_oeis_a003278

namespace SzekeresDigits

private lemma generated_of_digits {s : ℕ} (h : Digits01 s) : Generated (3*s+1) := by
  induction h with
  | zero => exact Generated.seed
  | append0 _ ih =>
    convert Generated.low ih using 1
    omega
  | append1 _ ih => exact Generated.high ih

private lemma generated_iff (x : ℕ) :
    Generated x ↔ ∃ s, Digits01 s ∧ x = 3*s+1 := by
  constructor
  · intro hx
    induction hx with
    | seed => exact ⟨0, Digits01.zero, rfl⟩
    | low _ ih =>
      obtain ⟨s, hs, rfl⟩ := ih
      exact ⟨_, Digits01.append0 hs, by omega⟩
    | high _ ih =>
      obtain ⟨s, hs, rfl⟩ := ih
      exact ⟨_, Digits01.append1 hs, by omega⟩
  · rintro ⟨s, hs, rfl⟩
    exact generated_of_digits hs

private lemma parent_of_digits {s : ℕ} (h : Digits01 s) : CantorParent (2*s) := by
  induction h with
  | zero => exact CantorParent.root
  | append0 _ ih =>
    convert CantorParent.left ih using 1
    omega
  | append1 _ ih =>
    convert CantorParent.right ih using 1
    omega

private lemma digits_of_parent {p : ℕ} (h : CantorParent p) : ∃ s, Digits01 s ∧ p = 2*s := by
  induction h with
  | root => exact ⟨0, Digits01.zero, rfl⟩
  | left _ ih =>
    obtain ⟨s, hs, rfl⟩ := ih
    exact ⟨_, Digits01.append0 hs, by omega⟩
  | right _ ih =>
    obtain ⟨s, hs, rfl⟩ := ih
    exact ⟨_, Digits01.append1 hs, by omega⟩

private lemma gap_iff (x : ℕ) : gap x ↔ ∃ s, Digits01 s ∧ x = 6*s+1 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨s, hs, rfl⟩ := digits_of_parent hp
    exact ⟨s, hs, by omega⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨_, parent_of_digits hs, by omega⟩

private lemma digit_power (n : ℕ) : Digits01 (3^n) := by
  induction n with
  | zero => exact Digits01.append1 Digits01.zero
  | succ n ih => simpa [pow_succ, mul_comm] using Digits01.append0 ih

private lemma nth_image {q : ℕ → Prop} (f : ℕ → ℕ) (hf : StrictMono f)
    (hq : ∀ x, q x ↔ ∃ s, Digits01 s ∧ x = f s) (i : ℕ) :
    Nat.nth q i = f (Nat.nth Digits01 i) := by
  have powers : StrictMono (fun k : ℕ => (3 : ℕ)^k) := pow_right_strictMono₀ (by decide)
  have infinite : (Set.ofPred q).Infinite := by
    refine (Set.infinite_range_of_injective (hf.comp powers).injective).mono ?_
    rintro _ ⟨k, rfl⟩
    exact (hq _).2 ⟨_, digit_power k, rfl⟩
  have allRange (k : ℕ) (hk : q k) : k ∈ Set.range f := by
    obtain ⟨s, _, rfl⟩ := (hq k).1 hk
    exact ⟨s, rfl⟩
  have preimage : (fun s => q (f s)) = Digits01 := by
    funext s
    apply propext
    rw [hq]
    constructor
    · rintro ⟨t, ht, hst⟩
      rwa [hf.injective hst]
    · exact fun h => ⟨s, h, rfl⟩
  have eqn := Nat.nth_comp_of_strictMono (p := q) (n := i) hf allRange
    (fun fin => (infinite fin).elim)
  rw [preimage] at eqn
  exact eqn.symm

end SzekeresDigits

theorem OMA.solution : type_of% @OMA.S_oeis_a003278.main := by
  intro i
  dsimp only
  have h₁ := SzekeresDigits.nth_image (fun s => 3*s+1) (fun _ _ h => by dsimp; omega)
    SzekeresDigits.generated_iff i
  have h₂ := SzekeresDigits.nth_image (fun s => 6*s+1) (fun _ _ h => by dsimp; omega)
    SzekeresDigits.gap_iff i
  omega
