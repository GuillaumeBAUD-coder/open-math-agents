import OMAStatements.S_oeis_a302984

-- Problem: A302984: Number of ways to write n as x^2 + 2*y^2 + 2^z + 5*2^w with x,y,z,w nonnegative integers.
-- Credit: @sobrien032

/- Zhi-Wei Sun asked whether every natural number greater than five has such
   a representation. Joey Lu reported this counterexample on November 26, 2026.
   Majdi Shadi Khaleel independently deposited it with a factor certificate
   on November 27, 2026, Zenodo 24599782. We check the witness by reducing
   modulo sixteen and checking twenty-one possible prime obstructions. -/

namespace SunWitness

/-- A prime inert in the quadratic form divides both coordinates of any zero modulo that prime. -/
theorem bad_norm {p m : ℕ} (hp : p.Prime) (hmod : p % 8 = 5 ∨ p % 8 = 7)
    (hp1 : p ∣ m) (hp2 : ¬ p ^ 2 ∣ m) (x y : ℕ) : x ^ 2 + 2 * y ^ 2 ≠ m := by
  rintro rfl
  let : Fact p.Prime := ⟨hp⟩
  have h := (ZMod.natCast_eq_zero_iff _ p).2 hp1
  push_cast at h
  have hy : (y : ZMod p) = 0 := by
    by_contra hne
    have hs : IsSquare (-2 : ZMod p) := by
      refine ⟨(x : ZMod p) / y, ?_⟩
      field_simp [hne]
      linear_combination -h
    have hres := (ZMod.exists_sq_eq_neg_two_iff (p := p) (by omega)).1 hs
    omega
  have hx : (x : ZMod p) = 0 := by simpa [hy] using h
  obtain ⟨u, hu⟩ := (ZMod.natCast_eq_zero_iff _ p).1 hx
  obtain ⟨v, hv⟩ := (ZMod.natCast_eq_zero_iff _ p).1 hy
  apply hp2
  exact ⟨u ^ 2 + 2 * v ^ 2, by rw [hu, hv]; ring⟩

end SunWitness

namespace SunWitness

private def residues : List ℕ := [0, 1, 2, 3, 4, 6, 8, 9, 11, 12]

private theorem represented_residue (x y : ℕ) : (x^2 + 2*y^2) % 16 ∈ residues := by
  have h : ∀ i j : Fin 16, ((i : ℕ)^2 + 2*(j : ℕ)^2) % 16 ∈ residues := by decide
  have hxy := h ⟨x % 16, Nat.mod_lt _ (by decide)⟩ ⟨y % 16, Nat.mod_lt _ (by decide)⟩
  have he : (x % 16)^2 + 2*(y % 16)^2 ≡ x^2+2*y^2 [MOD 16] :=
    ((Nat.mod_modEq x 16).pow 2).add (((Nat.mod_modEq y 16).pow 2).mul_left 2)
  exact he ▸ hxy

private def candidates : List ℕ :=
  [5, 7, 13, 23, 29, 37, 53, 61, 149, 181, 197, 263, 359, 773, 829, 1567, 2357,
    2677, 25391, 26293, 1417301]

private theorem candidate_prime {p : ℕ} (hp : p ∈ candidates) :
    p.Prime ∧ (p % 8 = 5 ∨ p % 8 = 7) := by
  simp [candidates] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private def offset (z : Fin 33) (w : Fin 30) : ℕ := 2 ^ (z : ℕ) + 5 * 2 ^ (w : ℕ)

private def test (m p : ℕ) : Bool := decide (p ∣ m ∧ ¬ p^2 ∣ m)

private theorem table :
    ∀ (z : Fin 33) (w : Fin 30), offset z w ≤ 4375339279 →
      (4375339279 - offset z w) % 16 ∈ residues →
      candidates.any (test (4375339279 - offset z w)) = true := by decide

theorem obstruction (z : Fin 33) (w : Fin 30)
    (h : 2 ^ (z : ℕ) + 5 * 2 ^ (w : ℕ) ≤ 4375339279) (x y : ℕ)
    (he : x^2+2*y^2 = 4375339279 - (2^(z:ℕ)+5*2^(w:ℕ))) :
    ∃ p : ℕ, p.Prime ∧ (p % 8 = 5 ∨ p % 8 = 7) ∧
      p ∣ x^2+2*y^2 ∧ ¬ p^2 ∣ x^2+2*y^2 := by
  have hr := represented_residue x y
  rw [he] at hr ⊢
  obtain ⟨p, hp, ht⟩ := List.any_eq_true.mp (table z w h hr)
  exact ⟨p, (candidate_prime hp).1, (candidate_prime hp).2, of_decide_eq_true ht⟩

end SunWitness

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a302984.main) := by
  intro claim
  obtain ⟨x, y, z, w, h⟩ := claim 4375339279 (by decide)
  have hz : z < 33 := by
    by_contra! hlarge
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hlarge
    change 8589934592 ≤ 2 ^ z at hpow
    omega
  have hcost : 5 * 2 ^ w ≤ 4375339279 := by
    rw [h]
    exact Nat.le_add_left _ _
  have hw : w < 30 := by
    by_contra! hlarge
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hlarge
    change 1073741824 ≤ 2 ^ w at hpow
    omega
  have hbound : 2 ^ z + 5 * 2 ^ w ≤ 4375339279 := by omega
  have hdiff : x ^ 2 + 2 * y ^ 2 = 4375339279 - (2 ^ z + 5 * 2 ^ w) := by omega
  obtain ⟨p, hp, hmod, hdiv, hndiv⟩ :=
    SunWitness.obstruction ⟨z, hz⟩ ⟨w, hw⟩ hbound x y hdiff
  exact SunWitness.bad_norm hp hmod hdiv hndiv x y rfl
