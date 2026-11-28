import OMAStatements.S_oeis_a164010
import Mathlib

open Finset OMA.S_oeis_a164010

private theorem lower_eq {n k : ℕ} (hn : 16 < n) (hk : k ≤ 9) :
    lowerDiv (n * (n+k)) = n := by
  have hn0 : 0 < n := by omega
  unfold lowerDiv
  apply le_antisymm
  · apply Finset.sup_le
    intro d hd
    have ⟨hdv, hdq⟩ := Finset.mem_filter.mp hd
    change d ≤ n
    by_contra! hnd
    have hdiv : d ∣ n * (n+k) := (Nat.mem_divisors.mp hdv).1
    have hd5 : d < n+5 := by
      by_contra! h
      have hm := Nat.mul_self_le_mul_self h
      have hle := Nat.mul_le_mul_left n (show n+k ≤ n+9 by omega)
      nlinarith
    let s := d-n
    have hds : d = n+s := by omega
    have hs1 : 1 ≤ s := by omega
    have hs4 : s ≤ 4 := by omega
    have hslt : s < k := by
      by_contra! h
      have hle := Nat.mul_le_mul_left n (show n+k ≤ d by omega)
      have hlt := Nat.mul_lt_mul_of_pos_right hnd (show 0 < d by omega)
      omega
    let t := k-s
    have he : k = s+t := by omega
    have hst : d ∣ s*t := (Nat.dvd_add_iff_right hdiv).mpr (by
      rw [hds, he, show n * (n+(s+t)) + s*t = (n+s)*(n+t) by ring]
      exact dvd_mul_right _ _)
    have hle := Nat.le_of_dvd (Nat.mul_pos (by omega : 0 < s) (by omega : 0 < t)) hst
    interval_cases s <;> omega
  · apply le_sup (f := id)
    refine mem_filter.mpr ⟨?_, Nat.mul_le_mul_left n (by omega)⟩
    exact Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, Nat.mul_ne_zero hn0.ne' (by omega)⟩

private theorem multiple_of_lower {n q : ℕ} (hn : 0 < n) (h : lowerDiv q = n) :
    ∃ i : ℕ, q = n * (n+i) := by
  let D := q.divisors.filter (fun d => d*d ≤ q)
  change D.sup id = n at h
  have hD : D.Nonempty := by
    by_contra h'
    rw [Finset.not_nonempty_iff_eq_empty.mp h', Finset.sup_empty] at h
    exact hn.ne' h.symm
  obtain ⟨d, hd, he⟩ := D.exists_mem_eq_sup hD id
  have hd' : d = n := he.symm.trans h
  subst d
  obtain ⟨hh, hs⟩ := Finset.mem_filter.mp hd
  obtain ⟨r, hr⟩ := (Nat.mem_divisors.mp hh).1
  have hnR : n ≤ r := by
    rw [hr] at hs
    exact Nat.le_of_mul_le_mul_left hs hn
  exact ⟨r-n, by rw [Nat.add_sub_of_le hnR, ← hr]⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a164010.main := by
  classical
  intro n hn
  have hn0 : 0 < n := by omega
  have hmono : StrictMono (fun i : ℕ => n * (n+i)) := by
    intro i j hij
    exact Nat.mul_lt_mul_of_pos_left (by omega) hn0
  have hcount : Nat.count (fun q => lowerDiv q = n) (n * (n+9)) = 9 := by
    rw [Nat.count_eq_card_filter_range]
    have hset : ((range (n * (n+9))).filter (fun q => lowerDiv q = n)) =
        (range 9).image (fun i => n * (n+i)) := by
      ext q
      rw [mem_filter, mem_range, mem_image]
      constructor
      · rintro ⟨hlt, hq⟩
        obtain ⟨i, rfl⟩ := multiple_of_lower hn0 hq
        exact ⟨i, mem_range.mpr (hmono.lt_iff_lt.mp hlt), rfl⟩
      · rintro ⟨i, hi, rfl⟩
        have hi' := mem_range.mp hi
        exact ⟨hmono hi', lower_eq hn (by omega)⟩
    rw [hset, card_image_of_injective _ hmono.injective, card_range]
  rw [a, if_neg hn0.ne', T]
  change Nat.nth (fun q => lowerDiv q = n) 9 = n * (n+9)
  simpa only [hcount] using
    (Nat.nth_count (p := fun q => lowerDiv q = n) (n := n * (n+9)) (lower_eq hn le_rfl))