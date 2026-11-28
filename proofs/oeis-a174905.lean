import OMAStatements.S_oeis_a174905
import Mathlib

-- Problem: A174905: m has no divisors d < e < 2d iff it has as many odd divisors as 2-dense
-- sublists of divisors.
-- Credit: @theterabites
--
-- Proof: the heads of the 2-dense sublists are exactly the odd divisors d with no divisor in
-- [d/2, d) (the block-head lemma of the proofs of A379379 and A389592). Hence the two counts
-- agree iff every odd divisor is a head. With no pair d < e < 2d every odd divisor is a head.
-- Conversely, from a pair d < e < 2d halve both while both are even: if e becomes odd it is not a
-- head (d lies in [e/2, e)), and if d becomes odd then e/2 lies in [d/2, d).

open OMA.S_oeis_a174905
open scoped Classical

namespace OMA.A174905

private abbrev small (b d : ℕ) := decide (d ≤ 2 * b)

/-- The divisors following a gap (previous divisor less than half). -/
private def gapList (b : ℕ) (xs : List ℕ) : List ℕ :=
  (((b :: xs).zip xs).filter (fun p => decide (2 * p.1 < p.2))).map Prod.snd

private lemma gapList_cons (b d : ℕ) (xs : List ℕ) :
    gapList b (d :: xs) = (if 2 * b < d then [d] else []) ++ gapList d xs := by
  by_cases h : 2 * b < d <;> simp [gapList, h]

private lemma loop_heads (xs : List ℕ) (b : ℕ) (run : List ℕ) (acc : List (List ℕ)) :
    (List.splitBy.loop small xs b run acc).map (fun r => r.headD 0) =
      (acc.map (fun r => r.headD 0)).reverse ++ [(b :: run).getLast?.getD 0] ++ gapList b xs := by
  induction xs generalizing b run acc with
  | nil =>
    simp [List.splitBy.loop, gapList, List.map_reverse, List.head?_reverse, List.headD_eq_head?_getD,
      List.getLast?_cons]
  | cons d xs ih =>
    rw [List.splitBy.loop, gapList_cons]
    by_cases h : d ≤ 2 * b
    · have hs : small b d = true := by simp [small, h]
      simp only [hs]
      rw [ih]
      simp [not_lt_of_ge h, List.getLast?_cons_cons]
    · have hs : small b d = false := by simp [small, h]
      simp only [hs]
      rw [ih]
      simp [show 2 * b < d by omega, List.headD_eq_head?_getD, List.head?_reverse, List.getLast?_cons]

private abbrev starts (D : Finset ℕ) (d : ℕ) := ∀ j ∈ D, j < d → 2 * j < d

private lemma remaining_gaps (D : Finset ℕ) (xs : List ℕ) (b : ℕ) (hb : b ∈ D)
    (inside : ∀ j ∈ xs, j ∈ D) (cover : ∀ j ∈ D, j ≤ b ∨ j ∈ xs)
    (order : (b :: xs).Pairwise (· < ·)) :
    gapList b xs = xs.filter fun d => decide (starts D d) := by
  induction xs generalizing b with
  | nil => rfl
  | cons d tail ih =>
    obtain ⟨hbefore, htail⟩ := List.pairwise_cons.mp order
    have hbd : b < d := hbefore d (by simp)
    have hd : d ∈ D := inside d (by simp)
    have hinside : ∀ j ∈ tail, j ∈ D := fun j hj => inside j (by simp [hj])
    have hcover : ∀ j ∈ D, j ≤ d ∨ j ∈ tail := by
      intro j hj
      rcases cover j hj with h | h
      · exact Or.inl (by omega)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl le_rfl
        · exact Or.inr h
    have criterion : starts D d ↔ 2 * b < d := by
      constructor
      · intro hs
        exact hs b hb hbd
      · intro h j hj hjd
        rcases cover j hj with hle | hmem
        · omega
        · rcases List.mem_cons.mp hmem with rfl | ht
          · omega
          · have := (List.pairwise_cons.mp htail).1 j ht
            omega
    rw [gapList_cons, ih d hd hinside hcover htail, List.filter_cons]
    by_cases h : 2 * b < d
    · rw [if_pos h, if_pos (by simpa using criterion.mpr h)]
      rfl
    · rw [if_neg h, if_neg (by simpa using fun hs => h (criterion.mp hs))]
      rfl

private lemma heads_eq (D : Finset ℕ) (_pos : ∀ d ∈ D, 0 < d) :
    ((D.sort (· ≤ ·)).splitBy small).map (fun r => r.headD 0) =
      (D.sort (· ≤ ·)).filter fun d => decide (starts D d) := by
  have hsort : (D.sort (· ≤ ·)).Pairwise (· < ·) := D.sortedLT_sort.pairwise
  have mem (j : ℕ) : j ∈ D.sort (· ≤ ·) ↔ j ∈ D := Finset.mem_sort _
  generalize hl : D.sort (· ≤ ·) = xs at hsort mem
  cases xs with
  | nil => rfl
  | cons d tail =>
    have hd : d ∈ D := (mem d).mp (by simp)
    have hi : ∀ j ∈ tail, j ∈ D := fun j hj => (mem j).mp (by simp [hj])
    have hc : ∀ j ∈ D, j ≤ d ∨ j ∈ tail := by
      intro j hj
      rcases List.mem_cons.mp ((mem j).mpr hj) with rfl | h
      · exact Or.inl le_rfl
      · exact Or.inr h
    have hs : starts D d := by
      intro j hj hjd
      rcases List.mem_cons.mp ((mem j).mpr hj) with rfl | h
      · omega
      · have := (List.pairwise_cons.mp hsort).1 j h
        omega
    rw [List.splitBy, loop_heads, remaining_gaps D tail d hd hi hc hsort, List.filter_cons,
      if_pos (by simpa using hs)]
    simp

private lemma start_iff (n d : ℕ) (hd : d ∈ n.divisors) :
    starts n.divisors d ↔ (Odd d ∧ ¬ ∃ j ∈ n.divisors, j < d ∧ d < 2 * j) := by
  constructor
  · intro hs
    refine ⟨Nat.not_even_iff_odd.mp ?_, ?_⟩
    · rintro ⟨u, hu⟩
      have hud : u ∣ d := ⟨2, by omega⟩
      obtain ⟨hdn, hn⟩ := Nat.mem_divisors.mp hd
      have hum : u ∈ n.divisors := Nat.mem_divisors.mpr ⟨hud.trans hdn, hn⟩
      have hpos := Nat.pos_of_mem_divisors hd
      have := hs u hum (by omega)
      omega
    · rintro ⟨j, hj, hlt, hcut⟩
      have := hs j hj hlt
      omega
  · rintro ⟨⟨t, ht⟩, hw⟩ j hj hlt
    by_contra hc
    apply hw
    refine ⟨j, hj, hlt, ?_⟩
    omega

/-- Sorting commutes with filtering. -/
private lemma sort_filter (D : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (D.filter p).sort (· ≤ ·) = (D.sort (· ≤ ·)).filter (fun d => decide (p d)) := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Finset.pairwise_sort _ _)
    ((Finset.pairwise_sort _ _).filter _)
  apply List.perm_of_nodup_nodup_toFinset_eq (Finset.sort_nodup _ _)
    ((Finset.sort_nodup _ _).filter _)
  ext x
  simp


private lemma filter_length (D : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((D.sort (· ≤ ·)).filter (fun d => decide (p d))).length = (D.filter p).card := by
  rw [← sort_filter, Finset.length_sort]

private lemma no_pair_of_heads (m : ℕ) (hm : m ≠ 0)
    (hstart : ∀ x ∈ m.divisors, Odd x → starts m.divisors x) :
    ∀ d e : ℕ, d ∣ m → e ∣ m → d < e → e < 2 * d → False := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro e hd he hde hed
  have hdD : d ∈ m.divisors := Nat.mem_divisors.mpr ⟨hd, hm⟩
  have heD : e ∈ m.divisors := Nat.mem_divisors.mpr ⟨he, hm⟩
  rcases Nat.even_or_odd e with ⟨e', rfl⟩ | heo
  · rcases Nat.even_or_odd d with ⟨d', rfl⟩ | hdo
    · have hd' : d' ∣ m := (Dvd.intro_left 2 (by ring)).trans hd
      have he' : e' ∣ m := (Dvd.intro_left 2 (by ring)).trans he
      exact ih d' (by omega) e' hd' he' (by omega) (by omega)
    · have he' : e' ∈ m.divisors :=
        Nat.mem_divisors.mpr ⟨(Dvd.intro_left 2 (by ring)).trans he, hm⟩
      have := hstart d hdD hdo e' he' (by omega)
      omega
  · have := hstart e heD heo d hdD hde
    omega

end OMA.A174905

open OMA.A174905

theorem OMA.A174905.main_proof :
    ∀ m : ℕ, 1 ≤ m → (NoPair m ↔ oddDivisorCount m = twoDenseCount m) := by
  intro m hm
  have hm0 : m ≠ 0 := by omega
  have hpos : ∀ d ∈ m.divisors, 0 < d := fun _ hd => Nat.pos_of_mem_divisors hd
  have htwo : twoDenseCount m = (m.divisors.filter (starts m.divisors)).card := by
    unfold twoDenseCount
    rw [← List.length_map (f := fun r => r.headD 0), heads_eq m.divisors hpos, filter_length]
  have hsub : m.divisors.filter (starts m.divisors) ⊆ m.divisors.filter Odd := by
    intro d hd
    rw [Finset.mem_filter] at hd ⊢
    exact ⟨hd.1, ((start_iff m d hd.1).mp hd.2).1⟩
  rw [htwo, oddDivisorCount]
  constructor
  · intro hno
    congr 1
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd, hodd⟩
      refine ⟨hd, (start_iff m d hd).mpr ⟨hodd, ?_⟩⟩
      rintro ⟨j, hj, hjd, hdj⟩
      exact hno ⟨j, d, Nat.dvd_of_mem_divisors hj, Nat.dvd_of_mem_divisors hd, hjd, hdj⟩
    · rintro ⟨hd, hs⟩
      exact ⟨hd, ((start_iff m d hd).mp hs).1⟩
  · intro hcard
    have heq : m.divisors.filter (starts m.divisors) = m.divisors.filter Odd :=
      Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard)
    have hstart : ∀ x ∈ m.divisors, Odd x → starts m.divisors x := by
      intro x hx hodd
      have : x ∈ m.divisors.filter Odd := Finset.mem_filter.mpr ⟨hx, hodd⟩
      rw [← heq] at this
      exact (Finset.mem_filter.mp this).2
    rintro ⟨d, e, hd, he, hde, hed⟩
    exact no_pair_of_heads m hm0 hstart d e hd he hde hed

theorem OMA.solution : type_of% @OMA.S_oeis_a174905.main := by
  exact OMA.A174905.main_proof
