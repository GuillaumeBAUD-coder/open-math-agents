import OMAReductions.R_oeis_a003459_R1
import Mathlib

namespace OMA.A003459
open OMA.S_oeis_a003459

/-- Moving a zero to the units place produces a multiple of ten. -/
private theorem no_zero {p : ℕ} (hp : IsPermutablePrime p) : 0 ∉ Nat.digits 10 p := by
  intro hz
  have h := hp _ (List.perm_cons_erase hz).symm
  rw [Nat.ofDigits_cons, zero_add] at h
  have hd : 10 ∣ 10 * Nat.ofDigits 10 ((Nat.digits 10 p).erase 0) := dvd_mul_right _ _
  rcases (Nat.dvd_prime h).mp hd with h1 | h10
  · omega
  · rw [← h10] at h
    exact (by decide : ¬ Nat.Prime 10) h

private theorem allowed_digits {p : ℕ} (hp : IsPermutablePrime p) (hlen : 10 ≤ p)
    {j : ℕ} (hj : j ∈ Nat.digits 10 p) : j ∈ [1, 3, 7, 9] := by
  let rest := (Nat.digits 10 p).erase j
  have perm : (j :: rest).Perm (Nat.digits 10 p) := (List.perm_cons_erase hj).symm
  have hlen' := (Nat.lt_digits_length_iff (k := 1) (by decide : 1 < 10) p).mpr (by simpa)
  have hn : rest ≠ [] := by
    intro h
    have := perm.length_eq
    simp [h] at this
    omega
  have hpos : 0 < Nat.ofDigits 10 rest := by
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hn
    have hmem : x ∈ Nat.digits 10 p := perm.subset (by simp [hx])
    have hxpos : x ≠ 0 := fun h => no_zero hp (h ▸ hmem)
    rw [hx, Nat.ofDigits_cons]
    omega
  have hprime := hp _ perm
  rw [Nat.ofDigits_cons] at hprime
  have hbig : 5 < j + 10 * Nat.ofDigits 10 rest := by omega
  have avoid_two : ¬ 2 ∣ j + 10 * Nat.ofDigits 10 rest := by
    intro h
    rcases (Nat.dvd_prime hprime).mp h with h | h <;> omega
  have avoid_five : ¬ 5 ∣ j + 10 * Nat.ofDigits 10 rest := by
    intro h
    rcases (Nat.dvd_prime hprime).mp h with h | h <;> omega
  have hlt := Nat.digits_lt_base (by decide : 1 < 10) hj
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- Choose the positions of the two exceptional digits in a seven-digit
block. Every residue of the higher part can be cancelled modulo seven. -/
private def block (a b c : ℕ) (i j : Fin 7) :=
  (List.range 7).map fun n => if n = i.val then b else if n = j.val then c else a

private theorem repeated_certificate :
    ∀ a ∈ [1, 3, 7, 9], ∀ b ∈ [1, 3, 7, 9], ∀ c ∈ [1, 3, 7, 9],
    b ≠ a → c ≠ a → ∀ r : Fin 7, ∃ i j : Fin 7,
      let s := block a b c i j
      s.Perm (List.replicate 5 a ++ [b, c]) ∧
        7 < Nat.ofDigits 10 s ∧ (Nat.ofDigits 10 s + 10000000 * r.val) % 7 = 0 := by
  decide +kernel

private theorem first_two {xs : List ℕ} (h : 2 ≤ xs.length) :
    ∃ b c tail, xs = b :: c :: tail := by
  cases xs with
  | nil => simp at h
  | cons b t => cases t <;> simp_all

private theorem almost_constant {p a : ℕ} (hp : IsPermutablePrime p) (hp10 : 10 ≤ p)
    (ha : 5 ≤ (Nat.digits 10 p).count a) :
    (Nat.digits 10 p).length ≤ (Nat.digits 10 p).count a + 1 := by
  let l := Nat.digits 10 p
  let others := l.filter fun x => !(x == a)
  have perm := List.filter_append_perm (fun x => x == a) l
  rw [List.filter_beq] at perm
  change (List.replicate (l.count a) a ++ others).Perm l at perm
  have hlen := perm.length_eq
  simp only [List.length_append, List.length_replicate] at hlen
  change l.length ≤ l.count a + 1
  by_contra! bad
  have two : 2 ≤ others.length := by omega
  obtain ⟨b, c, tail, htail⟩ := first_two two
  have memOther (x : ℕ) (hx : x ∈ others) : x ∈ [1,3,7,9] ∧ x ≠ a := by
    obtain ⟨hx', hxne⟩ := List.mem_filter.mp hx
    exact ⟨allowed_digits hp hp10 hx', by simpa using hxne⟩
  obtain ⟨hb, hba⟩ := memOther b (by simp [htail])
  obtain ⟨hc, hca⟩ := memOther c (by simp [htail])
  have subA : (List.replicate 5 a).Sublist (List.replicate (l.count a) a) :=
    List.replicate_sublist_iff.mpr (by simpa using ha)
  have subBC : [b,c].Sublist others := by
    rw [htail]
    exact List.Sublist.cons_cons _ (List.Sublist.cons_cons _ (List.nil_sublist _))
  obtain ⟨rest, hrest⟩ := (subA.append subBC).exists_perm_append
  let m := Nat.ofDigits 10 rest
  have ha' := allowed_digits hp hp10 (List.count_pos_iff.mp (by omega : 0 < (Nat.digits 10 p).count a))
  obtain ⟨i, j, hs, hbig, hmod⟩ := repeated_certificate a ha' b hb c hc hba hca
    ⟨m % 7, Nat.mod_lt _ (by decide)⟩
  let s := block a b c i j
  have hpr := hp _ ((hs.append_right rest).trans (hrest.symm.trans perm))
  rw [Nat.ofDigits_append] at hpr
  have hslen : s.length = 7 := by simp [s, block]
  change (Nat.ofDigits 10 s + 10 ^ s.length * m).Prime at hpr
  rw [hslen] at hpr
  change (Nat.ofDigits 10 s + 10000000 * (m % 7)) % 7 = 0 at hmod
  change 7 < Nat.ofDigits 10 s at hbig
  have hd : 7 ∣ Nat.ofDigits 10 s + 10000000 * m := by omega
  rcases (Nat.dvd_prime hpr).mp hd with h | h <;> omega

/-- The sorted representative of a multiset of admissible decimal digits. -/
private def sortedDigits (a b c d : ℕ) : List ℕ :=
  List.replicate a 1 ++ List.replicate b 3 ++ List.replicate c 7 ++ List.replicate d 9

private theorem sorted_perm {l : List ℕ} (ha : l ⊆ [1,3,7,9]) :
    (sortedDigits (l.count 1) (l.count 3) (l.count 7) (l.count 9)).Perm l := by
  apply List.perm_iff_count.mpr
  intro x
  by_cases hx : x ∈ [1,3,7,9]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [sortedDigits, List.count_replicate]
  · have hx' : x ∉ l := fun h => hx (ha h)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h1,h3,h7,h9⟩ := hx
    simp [sortedDigits, List.count_replicate, Ne.symm h1, Ne.symm h3, Ne.symm h7,
      Ne.symm h9, List.count_eq_zero_of_not_mem hx']

/-- With at most four copies of each digit, it suffices to check digit
multiplicities. A single transposition of the sorted digits exhibits a
proper common divisor with the product of the primes up to 31. -/
private theorem small_counts : ∀ a b c d : Fin 5,
    let l := sortedDigits a b c d
    max (max a.val b.val) (max c.val d.val) + 1 < l.length →
    ∃ i j : Fin 16, let n := Nat.ofDigits 10 (l.swap i j)
      1 < n.gcd 200560490130 ∧ n.gcd 200560490130 < n := by
  decide +kernel

private theorem sparse_counts {p : ℕ} (hp : IsPermutablePrime p) (hp10 : 10 ≤ p)
    (hs : ∀ a : ℕ, (Nat.digits 10 p).count a < 5) :
    ∃ a : ℕ, (Nat.digits 10 p).length ≤ (Nat.digits 10 p).count a + 1 := by
  let l := Nat.digits 10 p
  let count (a : ℕ) : Fin 5 := ⟨l.count a, hs a⟩
  let s := sortedDigits (count 1) (count 3) (count 7) (count 9)
  have perm : s.Perm l := sorted_perm (fun x hx => allowed_digits hp hp10 hx)
  by_contra! h
  have big : max (max (count 1).val (count 3).val) (max (count 7).val (count 9).val) + 1 < s.length := by
    rw [perm.length_eq]
    dsimp [count,l]
    have h1 := h 1
    have h3 := h 3
    have h7 := h 7
    have h9 := h 9
    omega
  obtain ⟨i, j, hlow, hhigh⟩ := small_counts (count 1) (count 3) (count 7) (count 9) big
  have prime := hp _ ((s.swap_perm i j).trans perm)
  exact (Nat.not_prime_of_dvd_of_lt (Nat.gcd_dvd_left _ 200560490130) hlow hhigh) prime

end OMA.A003459

open OMA.A003459 in
theorem OMA.solution : OMA.R_oeis_a003459_R1.H1 := by
  intro p hlen hp
  refine ⟨fun j hj => allowed_digits hp hlen hj, ?_⟩
  by_cases h : ∃ a : ℕ, 5 ≤ (Nat.digits 10 p).count a
  · obtain ⟨a, ha⟩ := h
    exact ⟨a, almost_constant hp hlen ha⟩
  · exact sparse_counts hp hlen (fun a => by have := not_exists.mp h a; omega)
