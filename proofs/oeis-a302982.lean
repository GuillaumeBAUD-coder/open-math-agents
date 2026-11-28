import OMAStatements.S_oeis_a302982

-- Problem: A302982: Number of ways to write n as x^2 + 5*y^2 + 2^z + 3*2^w with x,y,z,w nonnegative integers.
-- Credit: @sobrien032

/- Joey Lu's counterexample to Zhi-Wei Sun's A302982 conjecture.
   Alexander Berkovich and Hamza Yesilyurt, Corollary 3.3 of Ramanujan's
   identities and representation of integers by certain binary and
   quaternary quadratic forms, give the representation count for each
   remainder. Here we check the witness with congruences and prime divisors. -/

namespace SunWitnessFive

/-- At a prime where negative five is a nonsquare, a zero of the form has both coordinates zero. -/
theorem bad_norm {p m : ℕ} (hp : p.Prime) (hj : jacobiSym (-5) p = -1)
    (hp1 : p ∣ m) (hp2 : ¬ p ^ 2 ∣ m) (x y : ℕ) : x ^ 2 + 5 * y ^ 2 ≠ m := by
  rintro rfl
  let : Fact p.Prime := ⟨hp⟩
  have h := (ZMod.natCast_eq_zero_iff _ p).2 hp1
  push_cast at h
  have hy : (y : ZMod p) = 0 := by
    by_contra hne
    have hs : IsSquare (-5 : ZMod p) := by
      refine ⟨(x : ZMod p) / y, ?_⟩
      field_simp [hne]
      linear_combination -h
    exact ZMod.nonsquare_of_jacobiSym_eq_neg_one hj (by simpa using hs)
  have hx : (x : ZMod p) = 0 := by simpa [hy] using h
  obtain ⟨u, hu⟩ := (ZMod.natCast_eq_zero_iff _ p).1 hx
  obtain ⟨v, hv⟩ := (ZMod.natCast_eq_zero_iff _ p).1 hy
  apply hp2
  exact ⟨u ^ 2 + 5 * v ^ 2, by rw [hu, hv]; ring⟩

end SunWitnessFive

namespace SunWitnessFive

private def residues : List ℕ :=
  [0, 1, 4, 5, 6, 9, 13, 14, 16, 17, 20, 21, 22, 24, 25, 29, 30]

private theorem residue32 (x y : ℕ) : (x^2 + 5*y^2) % 32 ∈ residues := by
  have h : ∀ i j : Fin 32, ((i : ℕ)^2 + 5*(j : ℕ)^2) % 32 ∈ residues := by decide
  have hxy := h ⟨x % 32, Nat.mod_lt _ (by decide)⟩ ⟨y % 32, Nat.mod_lt _ (by decide)⟩
  have he : (x % 32)^2 + 5*(y % 32)^2 ≡ x^2+5*y^2 [MOD 32] :=
    ((Nat.mod_modEq x 32).pow 2).add (((Nat.mod_modEq y 32).pow 2).mul_left 5)
  exact he ▸ hxy

-- The first nonzero base-five digit of a represented number cannot be two or three.
private def good5 (r : ℕ) : Bool :=
  r % 5 != 2 && r % 5 != 3 && r % 25 != 10 && r % 25 != 15 && r != 50 && r != 75

set_option maxRecDepth 10000 in
private theorem residue125 (x y : ℕ) : good5 ((x^2 + 5*y^2) % 125) = true := by
  have h : ∀ (i : Fin 125) (j : Fin 25),
      good5 (((i : ℕ)^2 + 5*(j : ℕ)^2) % 125) = true := by decide
  have hxy := h ⟨x % 125, Nat.mod_lt _ (by decide)⟩ ⟨y % 25, Nat.mod_lt _ (by decide)⟩
  have he : (x % 125)^2 + 5*(y % 25)^2 ≡ x^2+5*y^2 [MOD 125] :=
    ((Nat.mod_modEq x 125).pow 2).add (((Nat.mod_modEq y 25).pow 2).mul_left' 5)
  exact he ▸ hxy

private def candidates : List ℕ :=
  [11, 13, 17, 19, 31, 37, 53, 59, 151, 191, 271, 617, 739, 2333, 2351, 3593, 6553, 7639]

private theorem candidate_prime {p : ℕ} (hp : p ∈ candidates) :
    p.Prime ∧ jacobiSym (-5) p = -1 := by
  simp [candidates] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private def offset (z : Fin 30) (w : Fin 28) : ℕ := 2 ^ (z : ℕ) + 3 * 2 ^ (w : ℕ)

private def test (m p : ℕ) : Bool := decide (p ∣ m ∧ ¬ p^2 ∣ m)

private theorem table :
    ∀ (z : Fin 30) (w : Fin 28), offset z w ≤ 558556427 →
      (558556427 - offset z w) % 32 ∈ residues →
      good5 ((558556427 - offset z w) % 125) = true →
      candidates.any (test (558556427 - offset z w)) = true := by decide

theorem obstruction (z : Fin 30) (w : Fin 28)
    (h : 2 ^ (z : ℕ) + 3 * 2 ^ (w : ℕ) ≤ 558556427) (x y : ℕ)
    (he : x^2+5*y^2 = 558556427 - (2^(z:ℕ)+3*2^(w:ℕ))) :
    ∃ p : ℕ, p.Prime ∧ jacobiSym (-5) p = -1 ∧
      p ∣ x^2+5*y^2 ∧ ¬ p^2 ∣ x^2+5*y^2 := by
  have hr := residue32 x y
  have hs := residue125 x y
  rw [he] at hr hs ⊢
  obtain ⟨p, hp, ht⟩ := List.any_eq_true.mp (table z w h hr hs)
  exact ⟨p, (candidate_prime hp).1, (candidate_prime hp).2, of_decide_eq_true ht⟩

end SunWitnessFive

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a302982.main) := by
  intro claim
  obtain ⟨x, y, z, w, h⟩ := claim 558556427 (by decide)
  have hzCost : 2 ^ z ≤ 558556427 := by
    rw [h]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  have hwCost : 3 * 2 ^ w ≤ 558556427 := by
    rw [h]
    exact Nat.le_add_left _ _
  have hz : z < 30 := by
    by_contra! hlarge
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hlarge
    change 1073741824 ≤ 2 ^ z at hpow
    omega
  have hw : w < 28 := by
    by_contra! hlarge
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hlarge
    change 268435456 ≤ 2 ^ w at hpow
    omega
  have hbound : 2 ^ z + 3 * 2 ^ w ≤ 558556427 := by
    rw [h, Nat.add_assoc]
    exact Nat.le_add_left _ _
  have hdiff : x ^ 2 + 5 * y ^ 2 = 558556427 - (2 ^ z + 3 * 2 ^ w) := by
    rw [h, Nat.add_assoc, Nat.add_sub_cancel]
  obtain ⟨p, hp, hj, hdiv, hndiv⟩ :=
    SunWitnessFive.obstruction ⟨z, hz⟩ ⟨w, hw⟩ hbound x y hdiff
  exact SunWitnessFive.bad_norm hp hj hdiv hndiv x y rfl
