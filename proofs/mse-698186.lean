import OMAStatements.S_mse_698186
import Mathlib.Data.Nat.Factors
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open scoped BigOperators

open OMA.S_mse_698186

namespace MSE698186Proof

def primeSet : Set ℕ := {p | p.Prime ∧ p % 3 = 2}

def modThreeSign (n : ℕ) : ℤ := if n % 3 = 2 then -1 else 1

lemma prime_factor_mod_two (l : List ℕ) (h : l.prod % 3 = 2) :
    ∃ p ∈ l, p % 3 = 2 := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    by_cases hp : p % 3 = 2
    · exact ⟨p, by simp, hp⟩
    · have hp1 : p % 3 = 1 := by
        rw [List.prod_cons, Nat.mul_mod] at h
        have hpbound := Nat.mod_lt p (by decide : 0 < 3)
        have hp01 : p % 3 = 0 ∨ p % 3 = 1 := by omega
        rcases hp01 with hp0 | hp1
        · simp [hp0] at h
        · exact hp1
      have hl : l.prod % 3 = 2 := by
        simpa [List.prod_cons, Nat.mul_mod, hp1] using h
      obtain ⟨q, hq, hq2⟩ := ih hl
      exact ⟨q, by simp [hq], hq2⟩

lemma primeSet_infinite : primeSet.Infinite := by
  classical
  intro hfin
  let s := hfin.toFinset
  have hs (p : ℕ) : p ∈ s ↔ p.Prime ∧ p % 3 = 2 := by
    simp [s, primeSet]
  let P := ∏ p ∈ s, p
  have hP : 0 < P := by
    apply Finset.prod_pos
    intro p hp
    exact ((hs p).mp hp).1.pos
  let N := 3 * P - 1
  have hN : N ≠ 0 := by dsimp [N]; omega
  have hNmod : N % 3 = 2 := by dsimp [N]; omega
  obtain ⟨p, hp, hp2⟩ := prime_factor_mod_two N.primeFactorsList
    (by simpa [Nat.prod_primeFactorsList hN] using hNmod)
  have hprime := Nat.prime_of_mem_primeFactorsList hp
  have hpP : p ∣ P := Finset.dvd_prod_of_mem id ((hs p).mpr ⟨hprime, hp2⟩)
  have hpN : p ∣ N := Nat.dvd_of_mem_primeFactorsList hp
  have hp3P : p ∣ 3 * P := dvd_mul_of_dvd_right hpP 3
  have hpone : p ∣ 1 := by
    have hd := Nat.dvd_sub hp3P hpN
    have he : 3 * P - N = 1 := by dsimp [N]; omega
    simpa [he] using hd
  exact hprime.not_dvd_one hpone

lemma sign_product (l : List ℕ) (h3 : ∀ p ∈ l, p % 3 ≠ 0) :
    ((l.map modThreeSign).prod = 1 ∧ l.prod % 3 = 1) ∨
      ((l.map modThreeSign).prod = -1 ∧ l.prod % 3 = 2) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp3 : p % 3 ≠ 0 := h3 p (by simp)
    have hp : p % 3 = 1 ∨ p % 3 = 2 := by omega
    have hl3 : ∀ q ∈ l, q % 3 ≠ 0 := fun q hq => h3 q (by simp [hq])
    rcases hp with hp | hp <;> rcases ih hl3 with ⟨hs, hm⟩ | ⟨hs, hm⟩
    · left
      simp [List.prod_cons, List.map_cons, modThreeSign, hp, hs, Nat.mul_mod, hm]
    · right
      simp [List.prod_cons, List.map_cons, modThreeSign, hp, hs, Nat.mul_mod, hm]
    · right
      simp [List.prod_cons, List.map_cons, modThreeSign, hp, hs, Nat.mul_mod, hm]
    · left
      simp [List.prod_cons, List.map_cons, modThreeSign, hp, hs, Nat.mul_mod, hm]

lemma generated_mod_two (n : ℕ) (hn : n % 3 = 2) :
    generated primeSet n = -1 := by
  classical
  have hn0 : n ≠ 0 := by omega
  have h3 : ∀ p ∈ n.primeFactorsList, p % 3 ≠ 0 := by
    intro p hp hp3
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactorsList hp
    have h3n : 3 ∣ n := (Nat.dvd_of_mod_eq_zero hp3).trans hpn
    have := Nat.mod_eq_zero_of_dvd h3n
    omega
  have hmap : (n.primeFactorsList.map fun p => if p ∈ primeSet then (-1 : ℤ) else 1) =
      n.primeFactorsList.map modThreeSign := by
    apply List.map_congr_left
    intro p hp
    simp [primeSet, modThreeSign, Nat.prime_of_mem_primeFactorsList hp]
  unfold generated
  rw [hmap]
  rcases sign_product n.primeFactorsList h3 with ⟨hs, hm⟩ | ⟨hs, hm⟩
  · rw [Nat.prod_primeFactorsList hn0] at hm
    omega
  · exact hs

theorem no_three_positive (n : ℕ) : ¬ ∀ i : ℕ, i < 3 → generated primeSet (n + i) = 1 := by
  intro h
  let i := 2 - n % 3
  have hi : i < 3 := by dsimp [i]; omega
  have hmod : (n + i) % 3 = 2 := by dsimp [i]; omega
  have hneg := generated_mod_two (n + i) hmod
  have hpos := h i hi
  omega

theorem disproof : ¬ (∀ S : Set ℕ, (∀ p ∈ S, p.Prime) → S.Infinite →
    ∀ k : ℕ, {n : ℕ | 0 < n ∧ ∀ i : ℕ, i < k → generated S (n + i) = 1}.Infinite) := by
  intro h
  obtain ⟨n, hn, hn3⟩ := (h primeSet (fun p hp => hp.1) primeSet_infinite 3).nonempty
  exact no_three_positive n hn3

end MSE698186Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_698186.main) :=
  MSE698186Proof.disproof
