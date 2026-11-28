import OMAReductions.R_mo_139058_R1

/-!
# Proof of `mo-139058.R1.H1`

For distinct primes `p, q` with `|p - q| ∈ {1, 2, 4}`, the set `A(p, q)` is a single residue
class modulo `|p - q|`, and `f(p, q)` equals one of the four fixed points
`(2, 3)`, `(3, 5)`, `(3, 7)`, or `(5, 13)`. Hence `f^[1] (p, q) = f^[2] (p, q)`.
-/

-- Step mo-139058.R1.H1: hypothesis H1 of reduction mo-139058.R1
-- Credit: @lettucrisp

namespace MO139058H1

open OMA.S_mo_139058

private lemma A_comm (p q : ℕ) : A p q = A q p := by
  ext s
  constructor
  · rintro ⟨m, n, h1, h2⟩
    exact ⟨n, m, by linarith, by linarith⟩
  · rintro ⟨m, n, h1, h2⟩
    exact ⟨n, m, by linarith, by linarith⟩

private lemma f_comm (p q : ℕ) : f (p, q) = f (q, p) := by
  simp only [f, first, second, A_comm p q]

private lemma nat_sInf_eq {S : Set ℕ} {a : ℕ} (ha : a ∈ S) (hmin : ∀ x ∈ S, a ≤ x) :
    sInf S = a :=
  le_antisymm (Nat.sInf_le ha) (le_csInf ⟨a, ha⟩ hmin)

private lemma f_eq_of_bounds {p q a b : ℕ}
    (ha : a.Prime ∧ (a : ℤ) ∈ A p q)
    (hmin_a : ∀ x : ℕ, x.Prime → (x : ℤ) ∈ A p q → a ≤ x)
    (hb : b.Prime ∧ (b : ℤ) ∈ A p q ∧ a < b)
    (hmin_b : ∀ x : ℕ, x.Prime → (x : ℤ) ∈ A p q → a < x → b ≤ x) :
    f (p, q) = (a, b) := by
  have h1 : first p q = a :=
    nat_sInf_eq ha (fun x hx => hmin_a x hx.1 hx.2)
  have h2 : second p q = b := by
    unfold second
    rw [h1]
    exact nat_sInf_eq hb (fun x hx => hmin_b x hx.1 hx.2.1 hx.2.2)
  exact Prod.ext h1 h2

private lemma mem_A_iff_add {p d : ℕ} {s : ℤ} :
    s ∈ A p (p + d) ↔ ∃ n : ℤ, s * (p : ℤ) + n * (d : ℤ) = 1 := by
  constructor
  · rintro ⟨m, n, h1, rfl⟩
    refine ⟨n, ?_⟩
    push_cast at h1
    linarith
  · rintro ⟨n, h1⟩
    refine ⟨s - n, n, ?_, by ring⟩
    push_cast
    linarith

private lemma f_2_3 : f (2, 3) = (2, 3) := by
  have hmem : ∀ s : ℤ, s ∈ A 2 3 := by
    intro s
    exact ⟨3 * s - 1, 1 - 2 * s, by ring, by ring⟩
  refine f_eq_of_bounds ⟨by decide, hmem 2⟩ ?_ ⟨by decide, hmem 3, by decide⟩ ?_
  · intro x hx _; exact hx.two_le
  · intro x _ _ hlt; omega

private lemma f_step2 {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) :
    f (p, p + 2) = (3, 5) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hq (by decide)
  have hp_odd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hmem : ∀ x : ℕ, (x : ℤ) ∈ A p (p + 2) ↔ x % 2 = 1 := by
    intro x
    rw [mem_A_iff_add]
    constructor
    · rintro ⟨n, hn⟩
      have hxp : (x * p) % 2 = 1 := by
        have : ((x : ℤ) * (p : ℤ)) % 2 = 1 := by omega
        exact_mod_cast this
      rw [Nat.mul_mod, hp_odd] at hxp
      omega
    · intro hx
      refine ⟨(1 - (x : ℤ) * (p : ℤ)) / 2, ?_⟩
      have hdiv : (2 : ℤ) ∣ 1 - (x : ℤ) * (p : ℤ) := by
        have hxp : (x * p) % 2 = 1 := by rw [Nat.mul_mod, hx, hp_odd]
        omega
      have hcancel := Int.ediv_mul_cancel hdiv
      norm_num
      linarith
  refine f_eq_of_bounds ⟨by decide, (hmem 3).mpr (by decide)⟩ ?_
      ⟨by decide, (hmem 5).mpr (by decide), by decide⟩ ?_
  · intro x hx hxm
    have hodd := (hmem x).mp hxm
    have h2 := hx.two_le
    omega
  · intro x _ hxm hlt
    have hodd := (hmem x).mp hxm
    omega

private lemma f_step4_mod3 {p : ℕ} (hp4 : p % 4 = 3) :
    f (p, p + 4) = (3, 7) := by
  have hmem : ∀ x : ℕ, (x : ℤ) ∈ A p (p + 4) ↔ x % 4 = 3 := by
    intro x
    rw [mem_A_iff_add]
    constructor
    · rintro ⟨n, hn⟩
      have hxp : (x * p) % 4 = 1 := by
        have : ((x : ℤ) * (p : ℤ)) % 4 = 1 := by omega
        exact_mod_cast this
      rw [Nat.mul_mod, hp4] at hxp
      omega
    · intro hx
      refine ⟨(1 - (x : ℤ) * (p : ℤ)) / 4, ?_⟩
      have hxp : (x * p) % 4 = 1 := by rw [Nat.mul_mod, hx, hp4]
      have hdiv : (4 : ℤ) ∣ 1 - (x : ℤ) * (p : ℤ) := by omega
      have hcancel := Int.ediv_mul_cancel hdiv
      norm_num
      linarith
  refine f_eq_of_bounds ⟨by decide, (hmem 3).mpr (by decide)⟩ ?_
      ⟨by decide, (hmem 7).mpr (by decide), by decide⟩ ?_
  · intro x _ hxm
    have := (hmem x).mp hxm
    omega
  · intro x _ hxm hlt
    have := (hmem x).mp hxm
    omega

private lemma f_step4_mod1 {p : ℕ} (hp4 : p % 4 = 1) :
    f (p, p + 4) = (5, 13) := by
  have hmem : ∀ x : ℕ, (x : ℤ) ∈ A p (p + 4) ↔ x % 4 = 1 := by
    intro x
    rw [mem_A_iff_add]
    constructor
    · rintro ⟨n, hn⟩
      have hxp : (x * p) % 4 = 1 := by
        have : ((x : ℤ) * (p : ℤ)) % 4 = 1 := by omega
        exact_mod_cast this
      rw [Nat.mul_mod, hp4] at hxp
      omega
    · intro hx
      refine ⟨(1 - (x : ℤ) * (p : ℤ)) / 4, ?_⟩
      have hxp : (x * p) % 4 = 1 := by rw [Nat.mul_mod, hx, hp4]
      have hdiv : (4 : ℤ) ∣ 1 - (x : ℤ) * (p : ℤ) := by omega
      have hcancel := Int.ediv_mul_cancel hdiv
      norm_num
      linarith
  refine f_eq_of_bounds ⟨by decide, (hmem 5).mpr (by decide)⟩ ?_
      ⟨by decide, (hmem 13).mpr (by decide), by decide⟩ ?_
  · intro x hx hxm
    have hm := (hmem x).mp hxm
    have h2 := hx.two_le
    omega
  · intro x hx hxm hlt
    have hm := (hmem x).mp hxm
    by_contra hlt13
    push Not at hlt13
    have hx9 : x = 9 := by omega
    subst hx9
    exact absurd hx (by decide)

private lemma f_5_13 : f (5, 13) = (5, 13) := by
  have hmem : ∀ x : ℕ, (x : ℤ) ∈ A 5 13 ↔ x % 8 = 5 := by
    intro x
    have h513 : (13 : ℕ) = 5 + 8 := by decide
    rw [h513, mem_A_iff_add]
    constructor
    · rintro ⟨n, hn⟩
      omega
    · intro hx
      refine ⟨(1 - (x : ℤ) * 5) / 8, ?_⟩
      have hdiv : (8 : ℤ) ∣ 1 - (x : ℤ) * 5 := by omega
      have hcancel := Int.ediv_mul_cancel hdiv
      norm_num
      linarith
  refine f_eq_of_bounds ⟨by decide, (hmem 5).mpr (by decide)⟩ ?_
      ⟨by decide, (hmem 13).mpr (by decide), by decide⟩ ?_
  · intro x _ hxm
    have := (hmem x).mp hxm
    omega
  · intro x _ hxm hlt
    have := (hmem x).mp hxm
    omega

private lemma f_idemp_of_add {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : q = p + 1 ∨ q = p + 2 ∨ q = p + 4) :
    f (f (p, q)) = f (p, q) := by
  rcases h with rfl | rfl | rfl
  · have hp2 : p = 2 := by
      by_contra hne
      have hodd := Nat.odd_iff.mp (hp.odd_of_ne_two hne)
      have hq2 : p + 1 ≠ 2 := by have := hp.two_le; omega
      have hqodd := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
      omega
    subst hp2
    rw [f_2_3, f_2_3]
  · rw [f_step2 hp hq, f_step2 (by decide) (by decide)]
  · have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd hq (by decide)
    have hp_odd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with h1 | h3
    · rw [f_step4_mod1 h1, f_5_13]
    · rw [f_step4_mod3 h3, f_step4_mod3 (by decide)]

end MO139058H1

theorem OMA.solution : OMA.R_mo_139058_R1.H1 := by
  intro p q hp hq hdist
  have hidemp : OMA.S_mo_139058.f (OMA.S_mo_139058.f (p, q)) = OMA.S_mo_139058.f (p, q) := by
    rcases hdist with h | h | h | h | h | h
    · exact MO139058H1.f_idemp_of_add hp hq (Or.inl h)
    · exact MO139058H1.f_idemp_of_add hp hq (Or.inr (Or.inl h))
    · exact MO139058H1.f_idemp_of_add hp hq (Or.inr (Or.inr h))
    · rw [MO139058H1.f_comm p q]
      exact MO139058H1.f_idemp_of_add hq hp (Or.inl h)
    · rw [MO139058H1.f_comm p q]
      exact MO139058H1.f_idemp_of_add hq hp (Or.inr (Or.inl h))
    · rw [MO139058H1.f_comm p q]
      exact MO139058H1.f_idemp_of_add hq hp (Or.inr (Or.inr h))
  exact ⟨1, 2, by decide, by simpa only [Function.iterate_succ_apply', Function.iterate_zero, id] using hidemp.symm⟩
