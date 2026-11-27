import OMAStatements.S_oeis_a274010
import Mathlib

namespace A274010Aux
lemma cond (n t : ℕ) (ht : 1 ≤ t) :
    t ∣ n * t / (t + 1) ↔ (n % (t + 1) = 0 ∨ n % (t + 1) = 1) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < t + 1 ∧ n = (t + 1) * q + r :=
    ⟨n / (t + 1), n % (t + 1), Nat.mod_lt _ (by omega), (Nat.div_add_mod n (t + 1)).symm⟩
  have hmod : ((t + 1) * q + r) % (t + 1) = r := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hr
  rw [hmod]
  rcases r with _ | r'
  · have e : ((t + 1) * q + 0) * t / (t + 1) = q * t := by
      rw [add_zero, mul_assoc]; exact Nat.mul_div_cancel_left _ (by omega)
    rw [e]
    simp
  · obtain ⟨u, rfl⟩ : ∃ u, t = r' + u := ⟨t - r', by omega⟩
    have e : ((r' + u + 1) * q + (r' + 1)) * (r' + u) =
        u + (r' + u + 1) * (q * (r' + u) + r') := by ring
    have hdiv : ((r' + u + 1) * q + (r' + 1)) * (r' + u) / (r' + u + 1) =
        q * (r' + u) + r' := by
      rw [e, Nat.add_mul_div_left _ _ (by omega : 0 < r' + u + 1),
        Nat.div_eq_of_lt (by omega), zero_add]
    rw [hdiv]
    constructor
    · intro h
      have h' : r' + u ∣ r' := (Nat.dvd_add_right (Dvd.intro_left q rfl)).mp h
      have h0 : r' = 0 := Nat.eq_zero_of_dvd_of_lt h' (by omega)
      omega
    · rintro (h | h)
      · omega
      · have h0 : r' = 0 := by omega
        subst h0
        simp
end A274010Aux

open OMA.S_oeis_a274010 in
theorem OMA.solution : type_of% @OMA.S_oeis_a274010.main := by
  intro n hn
  have h1n : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr (by omega)
  have h1n' : 1 ∈ (n - 1).divisors := Nat.one_mem_divisors.mpr (by omega)
  have hset : (Finset.Icc 2 n).filter (fun m => (m - 1) ∣ n * (m - 1) / m)
      = n.divisors.erase 1 ∪ (n - 1).divisors.erase 1 := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_erase,
      Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h2, hmn⟩, hc⟩
      obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
      rw [Nat.add_sub_cancel, A274010Aux.cond n t (by omega)] at hc
      rcases hc with hc | hc
      · left; exact ⟨by omega, Nat.dvd_of_mod_eq_zero hc, by omega⟩
      · right
        refine ⟨by omega, ?_, by omega⟩
        have hdm := Nat.div_add_mod n (t + 1)
        rw [hc] at hdm
        exact ⟨n / (t + 1), by omega⟩
    · rintro (⟨hm1, hd, -⟩ | ⟨hm1, hd, -⟩)
      · have hm0 : m ≠ 0 := by
          rintro rfl
          rw [Nat.zero_dvd] at hd
          omega
        have hle := Nat.le_of_dvd (by omega) hd
        refine ⟨⟨by omega, hle⟩, ?_⟩
        obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
        rw [Nat.add_sub_cancel, A274010Aux.cond n t (by omega)]
        left; exact Nat.mod_eq_zero_of_dvd hd
      · have hm0 : m ≠ 0 := by
          rintro rfl
          rw [Nat.zero_dvd] at hd
          omega
        have hle := Nat.le_of_dvd (by omega) hd
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
        rw [Nat.add_sub_cancel, A274010Aux.cond n t (by omega)]
        right
        obtain ⟨c, hc⟩ := hd
        have hn' : n = (t + 1) * c + 1 := by omega
        rw [hn', Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt (by omega)
  have hdisj : Disjoint (n.divisors.erase 1) ((n - 1).divisors.erase 1) := by
    rw [Finset.disjoint_left]
    intro m h1 h2
    simp only [Finset.mem_erase, Nat.mem_divisors] at h1 h2
    have hd1 : m ∣ (n - 1) + 1 := by
      rw [Nat.sub_add_cancel (by omega)]; exact h1.2.1
    have hm1 : m ∣ 1 := (Nat.dvd_add_right h2.2.1).mp hd1
    exact h1.1 (Nat.dvd_one.mp hm1)
  unfold a
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem h1n,
    Finset.card_erase_of_mem h1n']
  have p1 : 1 ≤ n.divisors.card := Finset.card_pos.mpr ⟨1, h1n⟩
  have p2 : 1 ≤ (n - 1).divisors.card := Finset.card_pos.mpr ⟨1, h1n'⟩
  push_cast [Nat.cast_sub p1, Nat.cast_sub p2]
  ring
