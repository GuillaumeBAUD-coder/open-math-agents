import OMAReductions.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1_H2_R1

-- Step SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1.H2.R1.H1: hypothesis H1 of reduction
-- SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1.H2.R1
-- Credit: @ptc-prover-bot

/-! `n` is a sum of three cubes modulo every `m > 0` iff `n ≢ 4, 5 (mod 9)`.
* Necessity: cubes modulo 9 are `0, ±1`, and three of them never sum to `4` or `5`.
* Sufficiency, by the Chinese remainder theorem over the factorisation of `m`:
  - `p ≠ 3`: the cubes (with `0`) form a set `A` with `3|A| ≥ p + 2` (each nonzero cube has at most
    three cube roots), so `A + A + A = ℤ/p` by Cauchy–Davenport; a solution with a nonzero
    coordinate lifts to `p^k` by Hensel (`p ∤ 3x²`).
  - `p = 3`: every `d ≡ ±1 (mod 9)` is a cube modulo `3^k` (start from `±1`, lift with
    `x ↦ x - s·3^(j-1)`), and `n` splits as a sum of at most three such numbers and zeros. -/

namespace OMA.ThreeCubesLocal

open Finset
open scoped Pointwise

/-- Hensel step for `x³ = d` at a prime `p ∤ 3x²`. -/
lemma lift_step {p : ℤ} (hp : Prime p) (d x : ℤ) (j : ℕ) (hj : 1 ≤ j)
    (hx : ¬ p ∣ 3 * x ^ 2) (h : p ^ j ∣ x ^ 3 - d) :
    ∃ x', p ^ (j + 1) ∣ x' ^ 3 - d ∧ p ∣ x' - x := by
  obtain ⟨s, hs⟩ := h
  have hcop : IsCoprime (3 * x ^ 2) p := ((Prime.coprime_iff_not_dvd hp).mpr hx).symm
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨x + (-s * u) * p ^ j, ?_, ?_⟩
  · have e : (x + (-s * u) * p ^ j) ^ 3 - d =
        p ^ (j + 1) * (s * v) + (p ^ j) ^ 2 * (3 * x * (-s * u) ^ 2) + (p ^ j) ^ 3 * (-s * u) ^ 3 := by
      have hx3 : x ^ 3 = d + p ^ j * s := by linarith
      have hv : v * p = 1 - u * (3 * x ^ 2) := by linarith
      calc (x + (-s * u) * p ^ j) ^ 3 - d
          = (x ^ 3 - d) + p ^ j * (3 * x ^ 2 * (-s * u)) + (p ^ j) ^ 2 * (3 * x * (-s * u) ^ 2)
            + (p ^ j) ^ 3 * (-s * u) ^ 3 := by ring
        _ = p ^ j * (s * (1 - u * (3 * x ^ 2))) + (p ^ j) ^ 2 * (3 * x * (-s * u) ^ 2)
            + (p ^ j) ^ 3 * (-s * u) ^ 3 := by rw [hx3]; ring
        _ = _ := by rw [← hv]; ring
    rw [e]
    have h2 : p ^ (j + 1) ∣ (p ^ j) ^ 2 := by
      rw [← pow_mul]; exact pow_dvd_pow p (by omega)
    have h3 : p ^ (j + 1) ∣ (p ^ j) ^ 3 := by
      rw [← pow_mul]; exact pow_dvd_pow p (by omega)
    exact dvd_add (dvd_add (dvd_mul_right _ _) (h2.mul_right _)) (h3.mul_right _)
  · simp only [add_sub_cancel_left]
    exact (dvd_pow_self p (by omega)).mul_left _

/-- Iterated Hensel lifting. -/
lemma lift_all {p : ℤ} (hp : Prime p) (d x₀ : ℤ) (h0 : p ∣ x₀ ^ 3 - d)
    (hx : ¬ p ∣ 3 * x₀ ^ 2) : ∀ k : ℕ, ∃ x, p ^ k ∣ x ^ 3 - d := by
  have key : ∀ k : ℕ, 1 ≤ k → ∃ x, p ^ k ∣ x ^ 3 - d ∧ p ∣ x - x₀ := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact ⟨x₀, by simpa using h0, by simp⟩
    | succ j hj ih =>
      obtain ⟨x, hxk, hxx⟩ := ih
      have hx' : ¬ p ∣ 3 * x ^ 2 := by
        intro hc; apply hx
        have : p ∣ 3 * x ^ 2 - 3 * x₀ ^ 2 := by
          have : 3 * x ^ 2 - 3 * x₀ ^ 2 = (x - x₀) * (3 * (x + x₀)) := by ring
          rw [this]; exact hxx.mul_right _
        have := dvd_sub hc this
        simpa using this
      obtain ⟨x', h1, h2⟩ := lift_step hp d x j hj hx' hxk
      exact ⟨x', h1, by have := dvd_add h2 hxx; simpa using this⟩
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, by simp⟩
  · obtain ⟨x, hx, -⟩ := key k hk; exact ⟨x, hx⟩

lemma one_sub_sq_of_not_dvd {x : ℤ} (hx : ¬ (3 : ℤ) ∣ x) : (3 : ℤ) ∣ 1 - x ^ 2 := by
  have h1 : x % 3 = 1 ∨ x % 3 = 2 := by omega
  have : (1 - x ^ 2) % 3 = 0 := by
    rcases h1 with h | h
    · have : x = 3 * (x / 3) + 1 := by omega
      rw [this]; ring_nf; omega
    · have : x = 3 * (x / 3) + 2 := by omega
      rw [this]; ring_nf; omega
  omega

/-- Lifting at `3`, from `3^(i+2)` to `3^(i+3)`. -/
lemma lift3_step (d x : ℤ) (i : ℕ) (hx : ¬ (3 : ℤ) ∣ x) (h : (3 : ℤ) ^ (i + 2) ∣ x ^ 3 - d) :
    ∃ x', (3 : ℤ) ^ (i + 3) ∣ x' ^ 3 - d ∧ (3 : ℤ) ∣ x' - x := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨w, hw⟩ := one_sub_sq_of_not_dvd hx
  refine ⟨x + (-s) * 3 ^ (i + 1), ?_, ?_⟩
  · have e : (x + (-s) * 3 ^ (i + 1)) ^ 3 - d =
        3 ^ (i + 3) * (s * w) + 3 ^ (i + 3) * (3 ^ i * (x * s ^ 2))
          + 3 ^ (i + 3) * (3 ^ (2 * i) * (-s) ^ 3) := by
      have hx3 : x ^ 3 = d + 3 ^ (i + 2) * s := by linarith
      calc (x + (-s) * 3 ^ (i + 1)) ^ 3 - d
          = (x ^ 3 - d) + 3 ^ (i + 2) * (x ^ 2 * (-s)) + 3 ^ (2 * i + 3) * (x * s ^ 2)
            + 3 ^ (3 * i + 3) * (-s) ^ 3 := by ring
        _ = 3 ^ (i + 2) * (s * (1 - x ^ 2)) + 3 ^ (2 * i + 3) * (x * s ^ 2)
            + 3 ^ (3 * i + 3) * (-s) ^ 3 := by rw [hx3]; ring
        _ = _ := by rw [hw]; ring
    rw [e]
    exact dvd_add (dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)) (dvd_mul_right _ _)
  · simp only [add_sub_cancel_left]
    exact Dvd.intro_left _ (by ring : (-s * 3 ^ i) * 3 = -s * 3 ^ (i + 1)) |>.trans (dvd_refl _)

/-- Every `d ≡ ±1 (mod 9)` is a cube modulo every power of `3`. -/
lemma cube_mod_three_pow (d : ℤ) (hd : d % 9 = 1 ∨ d % 9 = 8) :
    ∀ k : ℕ, ∃ x : ℤ, (3 : ℤ) ^ k ∣ x ^ 3 - d := by
  have base : ∃ x : ℤ, ¬ (3 : ℤ) ∣ x ∧ (3 : ℤ) ^ 2 ∣ x ^ 3 - d := by
    rcases hd with h | h
    · exact ⟨1, by norm_num, by norm_num; omega⟩
    · exact ⟨-1, by norm_num, by norm_num; omega⟩
  obtain ⟨x₀, hx₀, h₀⟩ := base
  have key : ∀ i : ℕ, ∃ x : ℤ, (3 : ℤ) ^ (i + 2) ∣ x ^ 3 - d ∧ (3 : ℤ) ∣ x - x₀ := by
    intro i
    induction i with
    | zero => exact ⟨x₀, by simpa using h₀, by simp⟩
    | succ i ih =>
      obtain ⟨x, h1, h2⟩ := ih
      have hx : ¬ (3 : ℤ) ∣ x := by
        intro hc; apply hx₀; have := dvd_sub hc h2; simpa using this
      obtain ⟨x', h3, h4⟩ := lift3_step d x i hx h1
      exact ⟨x', by simpa [add_assoc] using h3, by have := dvd_add h4 h2; simpa using this⟩
  intro k
  obtain ⟨x, hx, -⟩ := key k
  exact ⟨x, (pow_dvd_pow 3 (by omega)).trans hx⟩

/-- The case of a power of `3`. -/
lemma three_pow_case (n : ℤ) (hn : ¬ (n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9])) (k : ℕ) :
    ∃ a b c : ℤ, (3 : ℤ) ^ k ∣ n - (a ^ 3 + b ^ 3 + c ^ 3) := by
  -- a target is "good" if it is a cube modulo `3^k`
  have good : ∀ d : ℤ, d = 0 ∨ d % 9 = 1 ∨ d % 9 = 8 → ∃ x : ℤ, (3 : ℤ) ^ k ∣ x ^ 3 - d := by
    rintro d (rfl | hd)
    · exact ⟨0, by simp⟩
    · exact cube_mod_three_pow d hd k
  have split : ∀ d₁ d₂ d₃ : ℤ, d₁ + d₂ + d₃ = n →
      (d₁ = 0 ∨ d₁ % 9 = 1 ∨ d₁ % 9 = 8) → (d₂ = 0 ∨ d₂ % 9 = 1 ∨ d₂ % 9 = 8) →
      (d₃ = 0 ∨ d₃ % 9 = 1 ∨ d₃ % 9 = 8) → ∃ a b c : ℤ, (3 : ℤ) ^ k ∣ n - (a ^ 3 + b ^ 3 + c ^ 3) := by
    intro d₁ d₂ d₃ hs h₁ h₂ h₃
    obtain ⟨a, ha⟩ := good d₁ h₁
    obtain ⟨b, hb⟩ := good d₂ h₂
    obtain ⟨c, hc⟩ := good d₃ h₃
    refine ⟨a, b, c, ?_⟩
    have : n - (a ^ 3 + b ^ 3 + c ^ 3) = -((a ^ 3 - d₁) + (b ^ 3 - d₂) + (c ^ 3 - d₃)) := by
      rw [← hs]; ring
    rw [this]
    exact (dvd_add (dvd_add ha hb) hc).neg_right
  simp only [Int.ModEq] at hn
  have h9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
    omega
  rcases h9 with h | h | h | h | h | h | h
  · exact split 1 (n - 1) 0 (by ring) (by norm_num) (by omega) (by simp)
  · exact split n 0 0 (by ring) (by omega) (by simp) (by simp)
  · exact split 1 (n - 1) 0 (by ring) (by norm_num) (by omega) (by simp)
  · exact split 1 1 (n - 2) (by ring) (by norm_num) (by norm_num) (by omega)
  · exact split (-1) (-1) (n + 2) (by ring) (by norm_num) (by norm_num) (by omega)
  · exact split (-1) (n + 1) 0 (by ring) (by norm_num) (by omega) (by simp)
  · exact split n 0 0 (by ring) (by omega) (by simp) (by simp)

/-- At most three cube roots. -/
lemma card_cube_roots {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    (univ.filter fun x : ZMod p => x ^ 3 = a).card ≤ 3 := by
  classical
  have hne : (Polynomial.X ^ 3 - Polynomial.C a : Polynomial (ZMod p)) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by norm_num) a
  have h := Polynomial.card_le_degree_of_subset_roots (p := Polynomial.X ^ 3 - Polynomial.C a)
    (Z := univ.filter fun x : ZMod p => x ^ 3 = a) (by
      intro x hx
      have hx' : x ^ 3 = a := (mem_filter.mp (Finset.mem_val.mp hx)).2
      rw [Polynomial.mem_roots hne]
      simp [hx'])
  rwa [Polynomial.natDegree_X_pow_sub_C] at h

/-- Modulo a prime `p ≠ 3`: a representation with a nonzero first coordinate. -/
lemma mod_prime (p : ℕ) [hp : Fact p.Prime] (n : ZMod p) :
    ∃ x y z : ZMod p, x ≠ 0 ∧ n = x ^ 3 + y ^ 3 + z ^ 3 := by
  classical
  let A' : Finset (ZMod p) := (univ.erase 0).image fun x => x ^ 3
  let A : Finset (ZMod p) := insert 0 A'
  have h0 : (0 : ZMod p) ∉ A' := by
    simp only [A', mem_image, mem_erase, mem_univ, and_true, not_exists, not_and]
    intro x hx h; exact hx (pow_eq_zero_iff (by norm_num) |>.mp h)
  have hA' : p - 1 ≤ 3 * A'.card := by
    have := card_le_mul_card_image (f := fun x : ZMod p => x ^ 3) (univ.erase (0 : ZMod p)) 3
      (fun a _ => by
        refine le_trans (card_le_card ?_) (card_cube_roots a)
        intro x hx; rw [mem_filter] at hx ⊢; exact ⟨mem_univ _, hx.2⟩)
    rwa [card_erase_of_mem (mem_univ _), card_univ, ZMod.card] at this
  have hA : p + 2 ≤ 3 * A.card := by
    have : A.card = A'.card + 1 := card_insert_of_notMem h0
    have := hp.out.one_lt
    omega
  have hAne : A.Nonempty := insert_nonempty _ _
  have cd1 := ZMod.cauchy_davenport hp.out hAne hAne
  have cd2 := ZMod.cauchy_davenport hp.out (hAne.add hAne) hAne
  have hfull : (A + A + A).card = p := by
    have hle : (A + A + A).card ≤ p := by
      have := card_le_univ (A + A + A); rwa [ZMod.card] at this
    omega
  have hmem : n ∈ A + A + A := by
    have : A + A + A = univ := eq_univ_of_card _ (by rw [hfull, ZMod.card])
    rw [this]; exact mem_univ _
  have hcube : ∀ u ∈ A, ∃ x : ZMod p, u = x ^ 3 := by
    intro u hu
    rcases mem_insert.mp hu with rfl | hu
    · exact ⟨0, by ring⟩
    · obtain ⟨x, -, rfl⟩ := mem_image.mp hu; exact ⟨x, rfl⟩
  obtain ⟨uv, huv, w, hw, rfl⟩ := mem_add.mp hmem
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_add.mp huv
  obtain ⟨x, rfl⟩ := hcube u hu
  obtain ⟨y, rfl⟩ := hcube v hv
  obtain ⟨z, rfl⟩ := hcube w hw
  by_cases hs : x ^ 3 + y ^ 3 + z ^ 3 = 0
  · exact ⟨1, -1, 0, one_ne_zero, by rw [hs]; ring⟩
  · by_cases hx : x = 0
    · by_cases hy : y = 0
      · refine ⟨z, x, y, ?_, by ring⟩
        rintro rfl; apply hs; rw [hx, hy]; ring
      · exact ⟨y, x, z, hy, by ring⟩
    · exact ⟨x, y, z, hx, rfl⟩

/-- The case of a power of a prime `p ≠ 3`. -/
lemma prime_pow_case (n : ℤ) (p : ℕ) (hp : p.Prime) (h3 : p ≠ 3) (k : ℕ) :
    ∃ a b c : ℤ, (p : ℤ) ^ k ∣ n - (a ^ 3 + b ^ 3 + c ^ 3) := by
  haveI := Fact.mk hp
  obtain ⟨x, y, z, hx, hxyz⟩ := mod_prime p (n : ZMod p)
  set b : ℤ := (y.val : ℤ)
  set c : ℤ := (z.val : ℤ)
  set x₀ : ℤ := (x.val : ℤ)
  have cx : ((x₀ : ℤ) : ZMod p) = x := by simp [x₀]
  have cy : ((b : ℤ) : ZMod p) = y := by simp [b]
  have cz : ((c : ℤ) : ZMod p) = z := by simp [c]
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h0 : (p : ℤ) ∣ x₀ ^ 3 - (n - b ^ 3 - c ^ 3) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast; rw [cx, cy, cz, hxyz]; ring
  have hx3 : ¬ (p : ℤ) ∣ 3 * x₀ ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast; rw [cx]
    have h3' : (3 : ZMod p) ≠ 0 := by
      intro h
      have : (p : ℕ) ∣ 3 := by
        exact (ZMod.natCast_eq_zero_iff 3 p).mp (by exact_mod_cast h)
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this
      exact h3 this
    exact mul_ne_zero h3' (pow_ne_zero 2 hx)
  obtain ⟨a, ha⟩ := lift_all hpZ _ x₀ h0 hx3 k
  refine ⟨a, b, c, ?_⟩
  have : n - (a ^ 3 + b ^ 3 + c ^ 3) = -(a ^ 3 - (n - b ^ 3 - c ^ 3)) := by ring
  rw [this]; exact ha.neg_right

/-- Sufficiency at every modulus, by the Chinese remainder theorem. -/
lemma all_moduli (n : ℤ) (hn : ¬ (n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9])) :
    ∀ m : ℕ, 0 < m → ∃ x y z : ZMod m, (n : ZMod m) = x ^ 3 + y ^ 3 + z ^ 3 := by
  have ofInt : ∀ m : ℕ, (∃ a b c : ℤ, (m : ℤ) ∣ n - (a ^ 3 + b ^ 3 + c ^ 3)) →
      ∃ x y z : ZMod m, (n : ZMod m) = x ^ 3 + y ^ 3 + z ^ 3 := by
    rintro m ⟨a, b, c, h⟩
    refine ⟨a, b, c, ?_⟩
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr h
    push_cast at this
    exact sub_eq_zero.mp this
  intro m
  induction m using Nat.recOnPrimeCoprime with
  | zero => intro h; omega
  | prime_pow p k hp =>
    intro _
    apply ofInt
    by_cases h3 : p = 3
    · subst h3; obtain ⟨a, b, c, h⟩ := three_pow_case n hn k; exact ⟨a, b, c, by exact_mod_cast h⟩
    · obtain ⟨a, b, c, h⟩ := prime_pow_case n p hp h3 k; exact ⟨a, b, c, by exact_mod_cast h⟩
  | coprime a b ha hb hab iha ihb =>
    intro _
    obtain ⟨xa, ya, za, hA⟩ := iha (by omega)
    obtain ⟨xb, yb, zb, hB⟩ := ihb (by omega)
    let e := ZMod.chineseRemainder hab
    refine ⟨e.symm (xa, xb), e.symm (ya, yb), e.symm (za, zb), ?_⟩
    apply e.injective
    simp only [map_add, map_pow, RingEquiv.apply_symm_apply, map_intCast]
    ext
    · simpa using hA
    · simpa using hB

theorem H1_proof : OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1_H2_R1.H1 := by
  intro n
  refine ⟨fun h => ?_, all_moduli n⟩
  obtain ⟨x, y, z, hxyz⟩ := h 9 (by norm_num)
  have key : ∀ x y z : ZMod 9, x ^ 3 + y ^ 3 + z ^ 3 ≠ 4 ∧ x ^ 3 + y ^ 3 + z ^ 3 ≠ 5 := by decide
  rintro (h4 | h5)
  · have : (n : ZMod 9) = 4 := by
      have := (ZMod.intCast_eq_intCast_iff n 4 9).mpr h4; simpa using this
    exact (key x y z).1 (hxyz ▸ this)
  · have : (n : ZMod 9) = 5 := by
      have := (ZMod.intCast_eq_intCast_iff n 5 9).mpr h5; simpa using this
    exact (key x y z).2 (hxyz ▸ this)

end OMA.ThreeCubesLocal

theorem OMA.solution : OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1_H2_R1.H1 :=
  OMA.ThreeCubesLocal.H1_proof
