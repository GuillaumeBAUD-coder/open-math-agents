import OMAStatements.S_oeis_a164009
import Mathlib

namespace OMA.S_oeis_a164009

theorem lowerDiv_eq (n j : ℕ) (hn : 0 < n) :
    lowerDiv j = n ↔ (n ∣ j ∧ n * n ≤ j ∧ ∀ d, d ∣ j → d * d ≤ j → d ≤ n) := by
  unfold lowerDiv
  constructor
  · intro h
    have hne : ((Nat.divisors j).filter (fun d => d * d ≤ j)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      rw [he, Finset.sup_empty] at h
      exact absurd h.symm (Nat.pos_iff_ne_zero.1 hn)
    obtain ⟨m, hm, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [h] at hsup
    have hm' : m = n := hsup.symm
    subst hm'
    rw [Finset.mem_filter, Nat.mem_divisors] at hm
    refine ⟨hm.1.1, hm.2, fun d hd hdd => ?_⟩
    rw [← h]
    exact Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hd, hm.1.2⟩, hdd⟩)
  · rintro ⟨h1, h2, h3⟩
    have hj : j ≠ 0 := by
      rintro rfl
      have : 0 < n * n := Nat.mul_pos hn hn
      omega
    apply le_antisymm
    · apply Finset.sup_le
      intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      exact h3 d hd.1.1 hd.2
    · exact Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨h1, hj⟩, h2⟩)

theorem key (n i : ℕ) (hn : 12 < n) (hi : i ≤ 8) : lowerDiv (n * (n + i)) = n := by
  rw [lowerDiv_eq n _ (by omega)]
  refine ⟨Dvd.intro _ rfl, Nat.mul_le_mul_left n (by omega), fun d hd hdd => ?_⟩
  by_contra hlt
  obtain ⟨e, he⟩ := hd
  have hd0 : 0 < d := by omega
  have hde : d ≤ e := by
    rw [he] at hdd
    exact Nat.le_of_mul_le_mul_left hdd hd0
  obtain ⟨s, rfl⟩ : ∃ s, d = n + 1 + s := ⟨d - (n + 1), by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, e = n + 1 + s + t := ⟨e - (n + 1 + s), by omega⟩
  have h1 : n * i = n * (2 + 2 * s + t) + (1 + s) * (1 + s + t) := by nlinarith
  have hic : 2 + 2 * s + t < i := by
    by_contra h
    have := Nat.mul_le_mul_left n (Nat.le_of_not_lt h)
    nlinarith
  have hk : n ≤ (1 + s) * (1 + s + t) := by
    have := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hic)
    nlinarith
  have hs : s ≤ 2 := by omega
  have ht : t ≤ 5 := by omega
  interval_cases s <;> interval_cases t <;> omega

theorem conj : ∀ n : ℕ, 12 < n → a n = n * (n + 8) := by
  intro n hn
  have hn0 : 0 < n := by omega
  have hset : (Finset.range (n * (n + 8))).filter (fun j => lowerDiv j = n) =
      (Finset.range 8).image (fun i => n * (n + i)) := by
    ext j
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, hl⟩
      rw [lowerDiv_eq n j hn0] at hl
      obtain ⟨⟨m, rfl⟩, h2, -⟩ := hl
      have hm : n ≤ m := Nat.le_of_mul_le_mul_left h2 hn0
      have hm2 : m < n + 8 := Nat.lt_of_mul_lt_mul_left hj
      exact ⟨m - n, Finset.mem_range.2 (by omega), by rw [Nat.add_sub_cancel' hm]⟩
    · rintro ⟨i, hi, rfl⟩
      rw [Finset.mem_range] at hi
      exact ⟨Nat.mul_lt_mul_of_pos_left (by omega) hn0, key n i hn (by omega)⟩
  have hcount : Nat.count (fun j => lowerDiv j = n) (n * (n + 8)) = 8 := by
    rw [Nat.count_eq_card_filter_range, hset, Finset.card_image_of_injective, Finset.card_range]
    intro x y hxy
    have := Nat.eq_of_mul_eq_mul_left hn0 hxy
    omega
  have hp : lowerDiv (n * (n + 8)) = n := key n 8 hn (le_refl 8)
  have := Nat.nth_count (p := fun j => lowerDiv j = n) hp
  rw [hcount] at this
  unfold a T
  rw [if_neg (by omega)]
  exact this

end OMA.S_oeis_a164009

theorem OMA.solution : type_of% @OMA.S_oeis_a164009.main :=
  OMA.S_oeis_a164009.conj
