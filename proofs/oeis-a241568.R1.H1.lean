import OMAReductions.R_oeis_a241568_R1
import Mathlib
-- Credit: @LordMike

theorem qs_nr3a : ¬ IsSquare ((2 : ℕ) : ZMod 3) := by decide

theorem qs_nr3b : ¬ ¬ IsSquare ((1 : ℕ) : ZMod 3) := by decide

theorem qs_nr5 : ∀ r : ℕ, (r = 2 ∨ r = 3) → ¬ IsSquare ((r : ℕ) : ZMod 5) := by
  intro r hr
  rcases hr with rfl | rfl <;> decide

theorem qs_nr13 : ∀ r : ℕ, (r = 2 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 11) →
    ¬ IsSquare ((r : ℕ) : ZMod 13) := by
  intro r hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem qs_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (h : p % 8 = 3 ∨ p % 8 = 5) :
    ¬ IsSquare (2 : ZMod p) := by
  rw [ZMod.exists_sq_eq_two_iff hp]
  omega

theorem qs_three (p : ℕ) [Fact p.Prime] (hp : p ≠ 3) (h : p % 12 = 5 ∨ p % 12 = 7) :
    ¬ IsSquare (3 : ZMod p) := by
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have e : (p : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod p 3).symm
  have h4 : ((3 : ℕ) : ZMod p) = 3 := by norm_num
  rcases h with h | h
  · have h1 : p % 4 = 1 := by omega
    have := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := 3) h1 (by norm_num)
    have h2 : p % 3 = 2 := by omega
    rw [← h4, this, e, h2]
    exact qs_nr3a
  · have h1 : p % 4 = 3 := by omega
    have := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := p) (q := 3) h1 (by norm_num)
      (by omega)
    have h2 : p % 3 = 1 := by omega
    rw [← h4, this, e, h2]
    exact qs_nr3b

theorem qs_five (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (h : p % 5 = 2 ∨ p % 5 = 3) :
    ¬ IsSquare (5 : ZMod p) := by
  have h3 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have e : (p : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod p 5).symm
  have := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) hp2
  have h4 : ((5 : ℕ) : ZMod p) = 5 := by norm_num
  rw [← h4, ← this, e]
  exact qs_nr5 _ h

theorem qs_thirteen (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (h : p % 13 = 2 ∨ p % 13 = 5 ∨ p % 13 = 6 ∨ p % 13 = 7 ∨ p % 13 = 8 ∨ p % 13 = 11) :
    ¬ IsSquare (13 : ZMod p) := by
  have h3 : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have e : (p : ZMod 13) = ((p % 13 : ℕ) : ZMod 13) := (ZMod.natCast_mod p 13).symm
  have := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 13) (q := p) (by norm_num) hp2
  have h4 : ((13 : ℕ) : ZMod p) = 13 := by norm_num
  rw [← h4, ← this, e]
  exact qs_nr13 _ h

theorem qs_fin : ∀ r : Fin 1560, (r : ℕ) % 2 = 1 → (r : ℕ) % 3 ≠ 0 → (r : ℕ) % 5 ≠ 0 → (r : ℕ) % 13 ≠ 0 →
    ¬ (((r : ℕ) % 24 = 1 ∨ (r : ℕ) % 24 = 23) ∧ ((r : ℕ) % 5 = 1 ∨ (r : ℕ) % 5 = 4) ∧
      ((r : ℕ) % 13 = 1 ∨ (r : ℕ) % 13 = 3 ∨ (r : ℕ) % 13 = 4 ∨ (r : ℕ) % 13 = 9 ∨ (r : ℕ) % 13 = 10 ∨ (r : ℕ) % 13 = 12)) →
    ((r : ℕ) % 8 = 3 ∨ (r : ℕ) % 8 = 5) ∨ ((r : ℕ) % 12 = 5 ∨ (r : ℕ) % 12 = 7) ∨ ((r : ℕ) % 5 = 2 ∨ (r : ℕ) % 5 = 3) ∨
      ((r : ℕ) % 13 = 2 ∨ (r : ℕ) % 13 = 5 ∨ (r : ℕ) % 13 = 6 ∨ (r : ℕ) % 13 = 7 ∨ (r : ℕ) % 13 = 8 ∨ (r : ℕ) % 13 = 11) := by
  decide +kernel

theorem qs_large (p : ℕ) (hp : p.Prime) (h27 : 27 ≤ p)
    (hn : ¬ ((p % 24 = 1 ∨ p % 24 = 23) ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧
      p % 13 ∈ ([1, 3, 4, 9, 10, 12] : List ℕ))) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ (p - 1) / 2 ∧ (∃ m : ℕ, Nat.fib m = k) ∧ ¬ IsSquare (k : ZMod p) := by
  have := Fact.mk hp
  have h2 : p ≠ 2 := by omega
  have hodd := hp.eq_two_or_odd.resolve_left h2
  have h3 : p % 3 ≠ 0 := by
    intro h0
    have : 3 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 this
    omega
  have h5 : p % 5 ≠ 0 := by
    intro h0
    have : 5 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 this
    omega
  have h13 : p % 13 ≠ 0 := by
    intro h0
    have : 13 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 this
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  have e8 : (p % 1560) % 8 = p % 8 := Nat.mod_mod_of_dvd p (by norm_num)
  have e12 : (p % 1560) % 12 = p % 12 := Nat.mod_mod_of_dvd p (by norm_num)
  have e24 : (p % 1560) % 24 = p % 24 := Nat.mod_mod_of_dvd p (by norm_num)
  have e5 : (p % 1560) % 5 = p % 5 := Nat.mod_mod_of_dvd p (by norm_num)
  have e13 : (p % 1560) % 13 = p % 13 := Nat.mod_mod_of_dvd p (by norm_num)
  have e3 : (p % 1560) % 3 = p % 3 := Nat.mod_mod_of_dvd p (by norm_num)
  have e2 : (p % 1560) % 2 = p % 2 := Nat.mod_mod_of_dvd p (by norm_num)
  have hr := qs_fin ⟨p % 1560, Nat.mod_lt _ (by norm_num)⟩
  simp only [e8, e12, e24, e5, e13, e3, e2] at hr
  have key := hr hodd h3 h5 h13 hn
  rcases key with k | k | k | k
  · exact ⟨2, by norm_num, by omega, ⟨3, by decide⟩, by exact_mod_cast qs_two p h2 k⟩
  · exact ⟨3, by norm_num, by omega, ⟨4, by decide⟩, by
      have := qs_three p (by omega) k
      exact_mod_cast this⟩
  · exact ⟨5, by norm_num, by omega, ⟨5, by decide⟩, by
      have := qs_five p h2 k
      exact_mod_cast this⟩
  · exact ⟨13, by norm_num, by omega, ⟨7, by decide⟩, by
      have := qs_thirteen p h2 k
      exact_mod_cast this⟩

theorem OMA.solution : OMA.R_oeis_a241568_R1.H1 := by
  intro p hp h3 hn
  by_cases h27 : 27 ≤ p
  · exact qs_large p hp h27 hn
  · have hlt : p < 27 := by omega
    interval_cases p <;> first | (exfalso; revert hp; norm_num; done) | skip
    · exact ⟨2, by norm_num, by norm_num, ⟨3, by decide⟩, by decide⟩
    · exact ⟨3, by norm_num, by norm_num, ⟨4, by decide⟩, by decide⟩
    · exact ⟨2, by norm_num, by norm_num, ⟨3, by decide⟩, by decide⟩
    · exact ⟨2, by norm_num, by norm_num, ⟨3, by decide⟩, by decide⟩
    · exact ⟨3, by norm_num, by norm_num, ⟨4, by decide⟩, by decide⟩
    · exact ⟨2, by norm_num, by norm_num, ⟨3, by decide⟩, by decide⟩
    · exact ⟨5, by norm_num, by norm_num, ⟨5, by decide⟩, by decide⟩
