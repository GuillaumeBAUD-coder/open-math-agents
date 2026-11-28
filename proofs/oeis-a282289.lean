import OMAStatements.S_oeis_a282289

-- Problem: A282289, (Sum_{p prime, k>=2} x^(p^k))^4: the conjecture a(n) > 0 for all n > 27 is FALSE.
-- Credit: @EmircanEsen (agent: claude-code, model claude-opus-5-5)
--
-- Counterexample: 340473 is not a sum of four prime powers p^k with k >= 2, so a(340473) = 0.
-- * Every such p^k <= 340473 lies in an explicit list of 161 numbers (p < 584, k < 19: a finite
--   check by `decide +kernel`).
-- * All sums of two listed numbers up to 340473 are recorded as the set bits of one natural number
--   `mask`; the kernel checks that 340473 - t is never such a sum when t is one.
-- * A quadruple q0 + q1 + q2 + q3 = 340473 would make q0 + q1 and q2 + q3 two such sums.

namespace OMA.A282289Disproof

open OMA.S_oeis_a282289

/-- All prime powers `p^k` with `k ≥ 2` up to `340473`, in increasing order. -/
def pp : List ℕ := [4, 8, 9, 16, 25, 27, 32, 49, 64, 81, 121, 125, 128, 169, 243, 256, 289, 343, 361, 512, 529, 625, 729, 841, 961, 1024, 1331, 1369, 1681, 1849, 2048, 2187, 2197, 2209, 2401, 2809, 3125, 3481, 3721, 4096, 4489, 4913, 5041, 5329, 6241, 6561, 6859, 6889, 7921, 8192, 9409, 10201, 10609, 11449, 11881, 12167, 12769, 14641, 15625, 16129, 16384, 16807, 17161, 18769, 19321, 19683, 22201, 22801, 24389, 24649, 26569, 27889, 28561, 29791, 29929, 32041, 32761, 32768, 36481, 37249, 38809, 39601, 44521, 49729, 50653, 51529, 52441, 54289, 57121, 58081, 59049, 63001, 65536, 66049, 68921, 69169, 72361, 73441, 76729, 78125, 78961, 79507, 80089, 83521, 85849, 94249, 96721, 97969, 100489, 103823, 109561, 113569, 117649, 120409, 121801, 124609, 128881, 130321, 131072, 134689, 139129, 143641, 146689, 148877, 151321, 157609, 160801, 161051, 167281, 175561, 177147, 177241, 185761, 187489, 192721, 196249, 201601, 205379, 208849, 212521, 214369, 218089, 226981, 229441, 237169, 241081, 249001, 253009, 259081, 262144, 271441, 273529, 279841, 292681, 299209, 300763, 310249, 316969, 323761, 326041, 332929]

/-- Every prime power `p^k`, `k ≥ 2`, up to `340473` is listed (a finite check). -/
lemma listed_bool : ((List.range 584).all fun p => (List.range 19).all fun k =>
    !(decide (p ^ k ≤ 340473) && decide (2 ≤ k) && decide p.Prime) || pp.contains (p ^ k)) = true := by
  decide +kernel

lemma listed_aux : ∀ p < 584, ∀ k < 19, p ^ k ≤ 340473 → 2 ≤ k → p.Prime → p ^ k ∈ pp := by
  intro p hp k hk h1 h2 h3
  have := List.all_eq_true.1 (List.all_eq_true.1 listed_bool p (List.mem_range.2 hp)) k
    (List.mem_range.2 hk)
  simpa [h1, h2, h3] using this

lemma mem_pp {q : ℕ} (hq : IsHigherPrimePower q) (hle : q ≤ 340473) : q ∈ pp := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  have h2 : 2 ≤ p := hp.two_le
  have hsq : p * p ≤ 340473 := by
    calc p * p = p ^ 2 := by ring
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
      _ ≤ 340473 := hle
  have hp584 : p < 584 := by nlinarith
  have hk19 : k < 19 := by
    by_contra hk'
    have : 2 ^ 19 ≤ p ^ k :=
      (Nat.pow_le_pow_left h2 19).trans (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  exact listed_aux p hp584 k hk19 hle hk hp

/-- Sums of two listed prime powers, up to `340473`. -/
def pairSums : List ℕ := (pp.flatMap fun a => pp.map (a + ·)).filter (· ≤ 340473)

/-- Bit `s` is set exactly for the pair sums `s`. -/
def mask : ℕ := pairSums.foldr (fun s acc => acc ||| 2 ^ s) 0

lemma testBit_foldr {L : List ℕ} {s : ℕ} (h : s ∈ L) :
    (L.foldr (fun s acc => acc ||| 2 ^ s) 0).testBit s = true := by
  induction L with
  | nil => simp at h
  | cons x xs ih =>
    rw [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.1 h with rfl | h
    · right; exact Nat.testBit_two_pow_self
    · left; exact ih h

/-- The finite search: no pair sum `t` has `340473 - t` also a pair sum. -/
lemma check : (pairSums.all fun t => !(mask.testBit (340473 - t))) = true := by
  decide +kernel

lemma mem_pairSums {a b : ℕ} (ha : a ∈ pp) (hb : b ∈ pp) (h : a + b ≤ 340473) :
    a + b ∈ pairSums := by
  unfold pairSums
  rw [List.mem_filter]
  refine ⟨List.mem_flatMap.2 ⟨a, ha, List.mem_map.2 ⟨b, hb, rfl⟩⟩, by simpa using h⟩

/-- `340473` is not a sum of four prime powers with exponent at least `2`. -/
lemma a_eq_zero : a 340473 = 0 := by
  unfold a
  have hempty : {q : Fin 4 → ℕ | (∀ i, IsHigherPrimePower (q i)) ∧ ∑ i, q i = 340473} = ∅ := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hq hsum
    rw [Fin.sum_univ_four] at hsum
    have m : ∀ i, q i ∈ pp := fun i => mem_pp (hq i) (by
      have := Fin.sum_univ_four q
      fin_cases i <;> simp <;> omega)
    have h01 := mem_pairSums (m 0) (m 1) (by omega)
    have h23 := mem_pairSums (m 2) (m 3) (by omega)
    have hbit := testBit_foldr h23
    have hno := List.all_eq_true.1 check _ h01
    have heq : 340473 - (q 0 + q 1) = q 2 + q 3 := by omega
    rw [heq] at hno
    unfold mask at hno
    rw [hbit] at hno
    exact absurd hno (by decide)
  rw [hempty, Set.ncard_empty]

/-- The conjecture fails at `n = 340473`. -/
theorem disproof : ¬ (∀ n : ℕ, 27 < n → 0 < a n) := by
  intro h
  have := h 340473 (by norm_num)
  rw [a_eq_zero] at this
  exact absurd this (lt_irrefl 0)

end OMA.A282289Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282289.main) := OMA.A282289Disproof.disproof
