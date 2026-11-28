import OMAStatements.S_oeis_a364421
import Mathlib

namespace A364421Proof

lemma char (n r : ℕ) : (∃ y : ℕ, y ^ 2 = n ^ 3 + n ^ 2 + 2 * r * n + r ^ 2) ↔
    ∃ d e, d * e = n ^ 3 ∧ e = d + 2 * (n + r) := by
  constructor
  · rintro ⟨y, hy⟩
    have hge : n + r ≤ y := by
      by_contra hcon
      have : y + 1 ≤ n + r := by omega
      nlinarith [Nat.zero_le (n ^ 3)]
    obtain ⟨d, rfl⟩ : ∃ d, y = d + (n + r) := ⟨y - (n + r), by omega⟩
    exact ⟨d, d + 2 * (n + r), by nlinarith [hy], rfl⟩
  · rintro ⟨d, e, h, rfl⟩
    exact ⟨d + (n + r), by nlinarith [h]⟩

lemma count (n k : ℕ) (D E : ℕ → ℕ) (hn : 0 < n)
    (h1 : ∀ i, i < k → D i * E i = n ^ 3)
    (h2 : ∀ i, i < k → ∃ r, E i = D i + 2 * (n + r))
    (hstep : ∀ i, i + 1 < k → D i < D (i + 1))
    (hall : ∀ d e r, d * e = n ^ 3 → e = d + 2 * (n + r) → ∃ i, i < k ∧ d = D i) :
    OMA.S_oeis_a364421.a n = k := by
  have hmono : ∀ j, j < k → ∀ i, i < j → D i < D j := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ j ih =>
      intro hj i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact (ih (by omega) i h).trans (hstep j hj)
      · subst h; exact hstep i hj
  let g : ℕ → ℕ := fun i => (E i - D i) / 2 - n
  have hgi : ∀ i, i < k → E i = D i + 2 * (n + g i) := by
    intro i hi
    obtain ⟨r, hr⟩ := h2 i hi
    show E i = D i + 2 * (n + ((E i - D i) / 2 - n))
    omega
  have hpos : ∀ i, i < k → 0 < D i := by
    intro i hi
    rcases Nat.eq_zero_or_pos (D i) with h | h
    · have h3 := h1 i hi
      rw [h, zero_mul] at h3
      have := pow_pos hn 3
      omega
    · exact h
  have hne : ∀ i j, i < k → j < k → i < j → g i ≠ g j := by
    intro i j hi hj hlt hij
    have hlt' := hmono j hj i hlt
    have e1 := hgi i hi
    have e2 := hgi j hj
    have p1 := h1 i hi
    have p2 := h1 j hj
    rw [e1] at p1
    rw [e2, ← hij] at p2
    have : D i * (D i + 2 * (n + g i)) < D j * (D j + 2 * (n + g i)) :=
      Nat.mul_lt_mul'' hlt' (by omega)
    omega
  have hinj : Set.InjOn g (↑(Finset.range k)) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (hne i j hi hj h)
    · exact h
    · exact absurd hij.symm (hne j i hj hi h)
  have hS : {r : ℕ | ∃ y : ℕ, y ^ 2 = n ^ 3 + n ^ 2 + 2 * r * n + r ^ 2} =
      ↑((Finset.range k).image g) := by
    ext r
    simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    rw [char]
    constructor
    · rintro ⟨d, e, hde, he⟩
      obtain ⟨i, hi, rfl⟩ := hall d e r hde he
      refine ⟨i, hi, ?_⟩
      have h3 : E i = e := Nat.eq_of_mul_eq_mul_left (hpos i hi) ((h1 i hi).trans hde.symm)
      have h4 := hgi i hi
      omega
    · rintro ⟨i, hi, rfl⟩
      exact ⟨D i, E i, h1 i hi, hgi i hi⟩
  unfold OMA.S_oeis_a364421.a
  rw [hS, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, Finset.card_range]

lemma case1 (p : ℕ) (hp : p.Prime) (hodd : Odd p) : OMA.S_oeis_a364421.a (p ^ 3) = 5 := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨c, hc⟩ := hodd
    omega
  apply count (p ^ 3) 5 (fun i => p ^ i) (fun i => p ^ (9 - i)) (pow_pos hp.pos 3)
  · intro i hi
    show p ^ i * p ^ (9 - i) = (p ^ 3) ^ 3
    rw [← pow_add, ← pow_mul]
    congr 1
    omega
  · intro i hi
    show ∃ r, p ^ (9 - i) = p ^ i + 2 * (p ^ 3 + r)
    obtain ⟨a, ha⟩ := hodd.pow (n := i)
    obtain ⟨b, hb⟩ := hodd.pow (n := 9 - i)
    have h1 : p ^ i ≤ p ^ 4 := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : p ^ 5 ≤ p ^ (9 - i) := Nat.pow_le_pow_right hp.pos (by omega)
    have h3 : 3 * p ^ 4 ≤ p ^ 5 := by
      rw [pow_succ p 4, mul_comm 3]
      exact Nat.mul_le_mul_left _ hp3
    have h4 : p ^ 3 ≤ p ^ 4 := Nat.pow_le_pow_right hp.pos (by omega)
    exact ⟨b - a - p ^ 3, by omega⟩
  · intro i hi
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  · intro d e r hde he
    have hd : d ∣ p ^ 9 := ⟨e, by rw [hde, ← pow_mul]⟩
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
    have he' : e = p ^ (9 - i) := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos i)
      rw [hde, ← pow_add, ← pow_mul]
      congr 1
      omega
    refine ⟨i, ?_, rfl⟩
    by_contra hcon
    have h5 : p ^ (9 - i) ≤ p ^ i := Nat.pow_le_pow_right hp.pos (by omega)
    have h6 := pow_pos hp.pos 3
    omega

lemma case2 (p : ℕ) (hp : p.Prime) (hodd : Odd p) : OMA.S_oeis_a364421.a (2 * p ^ 2) = 7 := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨c, hc⟩ := hodd
    omega
  have q : ∀ t, 3 * p ^ t ≤ p ^ (t + 1) := by
    intro t
    rw [pow_succ p t, mul_comm 3]
    exact Nat.mul_le_mul_left _ hp3
  have q1 := q 1
  have q2 := q 2
  have q3 := q 3
  have q4 := q 4
  have q5 := q 5
  simp only [pow_one, Nat.reduceAdd] at q1 q2 q3 q4 q5
  apply count (2 * p ^ 2) 7 (fun i => 2 ^ (1 + i % 2) * p ^ (i / 2))
    (fun i => 2 ^ (2 - i % 2) * p ^ (6 - i / 2)) (by positivity)
  · intro i hi
    show 2 ^ (1 + i % 2) * p ^ (i / 2) * (2 ^ (2 - i % 2) * p ^ (6 - i / 2)) = (2 * p ^ 2) ^ 3
    interval_cases i <;> norm_num <;> ring
  · intro i hi
    refine ⟨(2 ^ (2 - i % 2) * p ^ (6 - i / 2) - 2 ^ (1 + i % 2) * p ^ (i / 2)) / 2 - 2 * p ^ 2, ?_⟩
    show 2 ^ (2 - i % 2) * p ^ (6 - i / 2) = 2 ^ (1 + i % 2) * p ^ (i / 2) + 2 * (2 * p ^ 2 +
      ((2 ^ (2 - i % 2) * p ^ (6 - i / 2) - 2 ^ (1 + i % 2) * p ^ (i / 2)) / 2 - 2 * p ^ 2))
    interval_cases i <;> norm_num <;> omega
  · intro i hi
    show 2 ^ (1 + i % 2) * p ^ (i / 2) < 2 ^ (1 + (i + 1) % 2) * p ^ ((i + 1) / 2)
    have hi6 : i < 6 := by omega
    interval_cases i <;> norm_num <;> omega
  · intro d e r hde he
    have hd : d ∣ 2 ^ 3 * p ^ 6 := ⟨e, by rw [hde]; ring⟩
    obtain ⟨u, v, hu, hv, rfl⟩ := (Nat.dvd_mul).mp hd
    obtain ⟨s, hs, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hu
    obtain ⟨t, ht, rfl⟩ := (Nat.dvd_prime_pow hp).mp hv
    have he' : e = 2 ^ (3 - s) * p ^ (6 - t) := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ s * p ^ t by have := hp.pos; positivity)
      rw [hde]
      have e1 : 2 ^ s * 2 ^ (3 - s) = 2 ^ 3 := by rw [← pow_add]; congr 1; omega
      have e2 : p ^ t * p ^ (6 - t) = p ^ 6 := by rw [← pow_add]; congr 1; omega
      calc (2 * p ^ 2) ^ 3 = 2 ^ 3 * p ^ 6 := by ring
        _ = (2 ^ s * 2 ^ (3 - s)) * (p ^ t * p ^ (6 - t)) := by rw [e1, e2]
        _ = _ := by ring
    subst he'
    obtain ⟨a, ha⟩ := hodd.pow (n := t)
    obtain ⟨b, hb⟩ := hodd.pow (n := 6 - t)
    have hp2 := pow_pos hp.pos 2
    have hs12 : s = 1 ∨ s = 2 := by
      interval_cases s
      · exfalso; simp only [pow_zero, one_mul, Nat.sub_zero] at he; omega
      · left; rfl
      · right; rfl
      · exfalso; simp only [Nat.sub_self, pow_zero, one_mul] at he; omega
    rcases hs12 with rfl | rfl
    · interval_cases t
      · exact ⟨0, by norm_num, by norm_num⟩
      · exact ⟨2, by norm_num, by norm_num⟩
      · exact ⟨4, by norm_num, by norm_num⟩
      · exact ⟨6, by norm_num, by norm_num⟩
      all_goals (exfalso; norm_num at he; omega)
    · interval_cases t
      · exact ⟨1, by norm_num, by norm_num⟩
      · exact ⟨3, by norm_num, by norm_num⟩
      · exact ⟨5, by norm_num, by norm_num⟩
      all_goals (exfalso; norm_num at he; omega)

end A364421Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a364421.main :=
  ⟨A364421Proof.case1, A364421Proof.case2⟩
