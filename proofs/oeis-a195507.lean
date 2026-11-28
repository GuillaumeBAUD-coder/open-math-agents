import OMAStatements.S_oeis_a195507
import Mathlib

/-!
# OEIS A195507: `a(n) = n + lcm(1, …, n-1)` and the conjectured recurrence

For `m > n`, the conditions `m ≡ n (mod k)` for `1 ≤ k ≤ n - 1` say that every such `k` divides
`m - n`, i.e. `L(n-1) = lcm(1, …, n-1)` divides `m - n`. The least such `m` is `n + L(n-1)`.

Write `L = L(n-1)`, `g = gcd(n, L)`, `n = g b`, `L = g c` with `gcd(b, c) = 1`. Then

* `a(n)/n = (b + c)/b` in lowest terms, so its denominator is `d = b`;
* `L(n) = lcm(n, L) = g b c = b L`, so `a(n+1) = n + 1 + b L`;
* `d a(n) - (d - 1) n + 1 = b (n + L) - (b - 1) n + 1 = n + 1 + b L`.
-/

open OMA.S_oeis_a195507

namespace OMA.A195507

/-- `L j = lcm(1, …, j)`. -/
def L (j : ℕ) : ℕ := (Finset.Icc 1 j).lcm id

lemma L_pos (j : ℕ) : 0 < L j := by
  have hdvd : L j ∣ j.factorial := by
    refine Finset.lcm_dvd fun i hi => ?_
    have hi' := Finset.mem_Icc.mp hi
    exact Nat.dvd_factorial hi'.1 hi'.2
  exact Nat.pos_of_dvd_of_pos hdvd (Nat.factorial_pos j)

lemma L_succ (n : ℕ) (hn : 1 ≤ n) : L n = Nat.lcm n (L (n - 1)) := by
  unfold L
  have h : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [h, Finset.lcm_insert]
  rfl

/-- For `m > n`: the congruences hold iff `L(n-1) ∣ m - n`. -/
lemma mem_iff (n m : ℕ) (hnm : n < m) :
    (∀ k : ℕ, 1 ≤ k → k ≤ n - 1 → m % k = n % k) ↔ L (n - 1) ∣ m - n := by
  unfold L
  rw [Finset.lcm_dvd_iff]
  constructor
  · intro h k hk
    have hk' := Finset.mem_Icc.mp hk
    have hmod : m ≡ n [MOD k] := h k hk'.1 hk'.2
    exact (Nat.modEq_iff_dvd' hnm.le).mp hmod.symm
  · intro h k hk1 hk2
    have hd : k ∣ m - n := h k (Finset.mem_Icc.mpr ⟨hk1, hk2⟩)
    exact ((Nat.modEq_iff_dvd' hnm.le).mpr hd).symm

/-- `a(n) = n + lcm(1, …, n-1)`. -/
lemma a_eq (n : ℕ) : a n = n + L (n - 1) := by
  have hL := L_pos (n - 1)
  have hmem : n + L (n - 1) ∈ {m : ℕ | n < m ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 → m % k = n % k} := by
    refine ⟨by omega, ?_⟩
    rw [mem_iff n _ (by omega)]
    simp
  unfold a
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
  rintro m ⟨hnm, h⟩
  have hd := (mem_iff n m hnm).mp h
  have := Nat.le_of_dvd (by omega) hd
  omega

/-- The arithmetic behind the recurrence. -/
lemma formula (n Lv : ℕ) (hn : 1 ≤ n) :
    ((n + 1 + Nat.lcm n Lv : ℕ) : ℤ)
      = ((((n + Lv : ℕ) : ℚ) / (n : ℚ)).den : ℤ) * ((n + Lv : ℕ) : ℤ)
        - (((((n + Lv : ℕ) : ℚ) / (n : ℚ)).den : ℤ) - 1) * (n : ℤ) + 1 := by
  obtain ⟨g, hg⟩ : ∃ g, Nat.gcd n Lv = g := ⟨_, rfl⟩
  have hgpos : 0 < g := hg ▸ Nat.gcd_pos_of_pos_left _ (by omega)
  obtain ⟨b, hb⟩ : g ∣ n := hg ▸ Nat.gcd_dvd_left n Lv
  obtain ⟨c, hc⟩ : g ∣ Lv := hg ▸ Nat.gcd_dvd_right n Lv
  subst hb hc
  have hcop : Nat.Coprime b c := by
    rw [Nat.gcd_mul_left] at hg
    have h : g * Nat.gcd b c = g * 1 := by rw [hg, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hgpos h
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | h
    · omega
    · exact h
  have hlcm : Nat.lcm (g * b) (g * c) = g * b * c := by
    rw [Nat.lcm_mul_left, hcop.lcm_eq_mul, mul_assoc]
  have hden : ((((g * b + g * c : ℕ) : ℚ) / ((g * b : ℕ) : ℚ)).den : ℤ) = b := by
    have e : ((g * b + g * c : ℕ) : ℚ) / ((g * b : ℕ) : ℚ)
        = (((c + b : ℕ) : ℤ) : ℚ) / ((b : ℤ) : ℚ) := by
      have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hgpos.ne'
      have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hbpos.ne'
      push_cast
      field_simp
      ring
    rw [e]
    apply Rat.den_div_eq_of_coprime (by exact_mod_cast hbpos)
    have hc2 : Nat.Coprime (c + b) b := Nat.coprime_add_self_left.mpr hcop.symm
    rw [Int.natAbs_natCast, Int.natAbs_natCast]
    exact hc2
  rw [hlcm, hden]
  push_cast
  ring

end OMA.A195507

open OMA.A195507 in
theorem OMA.solution : type_of% @OMA.S_oeis_a195507.main := by
  intro n hn
  have h2 := a_eq (n + 1)
  rw [Nat.add_sub_cancel, L_succ n hn] at h2
  rw [a_eq n, h2]
  exact formula n (L (n - 1)) hn
