import OMAReductions.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1

/-! Credit: @connoranderson. The finite-period counting argument adapts the
one in proofs/Erdos692.erdos_692.parts.ii.lean. Compare the two densities
within the same factorial period: adding 2q loses the residue 2q and
cannot gain any residue because q already divides every multiple of 2q. -/
namespace Erdos692PrimeEndpoint

open Erdos692 Filter Finset
open scoped Topology

private abbrev divisorsIn (n m x : ℕ) : Set ℕ := {d ∈ Set.Ioo n m | d ∣ x}

private lemma common_period {n m b : ℕ} (hm : m ≤ b) :
    Function.Periodic (fun x => x ∈ exactlyOneDivisorIn n m) b.factorial := by
  intro x
  apply propext
  change (divisorsIn n m (x + b.factorial)).ncard = 1 ↔ (divisorsIn n m x).ncard = 1
  have he : divisorsIn n m (x + b.factorial) = divisorsIn n m x := by
    ext d
    change (_ ∧ d ∣ x + b.factorial) ↔ (_ ∧ d ∣ x)
    constructor
    · rintro ⟨hd,hx⟩
      have hd' : d ∣ b.factorial := Nat.dvd_factorial (Nat.zero_lt_of_lt hd.1) (hd.2.le.trans hm)
      exact ⟨hd, (Nat.dvd_add_iff_left hd').mpr hx⟩
    · rintro ⟨hd,hx⟩
      exact ⟨hd,dvd_add hx (Nat.dvd_factorial (Nat.zero_lt_of_lt hd.1) (hd.2.le.trans hm))⟩
  rw [he]

private lemma density_count (p : ℕ → Prop) [DecidablePred p] {d : ℕ} (hd : 0 < d)
    (hp : Function.Periodic p d) {v : ℝ} (hv : Set.HasDensity {x | p x} v) :
    v = (Nat.count p d : ℝ) / d := by
  have hc (k : ℕ) : Nat.count p (k*d) = k * Nat.count p d := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, Nat.succ_mul, Nat.count_add' p, ← ih]
      congr 1
      apply le_antisymm <;> apply Nat.count_mono_left <;> intro x _ hx <;> simpa only [hp x] using hx
  have ht : Tendsto (fun k : ℕ => k*d) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_right k hd) tendsto_id
  apply tendsto_nhds_unique (hv.comp ht)
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop 0] with k hk
  change _ = Set.partialDensity {x | p x} Set.univ (k*d)
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat]
  have he : ({x | p x} ∩ Set.Iio (k*d)).ncard = Nat.count p (k*d) := by
    rw [Nat.count_eq_card_filter_range, ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [and_comm]
  rw [he, hc, Nat.cast_mul, Nat.cast_mul]
  field_simp

private lemma multiple_excluded {n q x : ℕ} (hnq : n < q) (hx : 2*q ∣ x) :
    x ∉ exactlyOneDivisorIn n (2*q+1) := by
  intro h
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h
  have h₁ : q ∈ divisorsIn n (2*q+1) x :=
    ⟨⟨hnq, by omega⟩, dvd_trans (dvd_mul_left q 2) hx⟩
  have h₂ : 2*q ∈ divisorsIn n (2*q+1) x := ⟨⟨by omega, by omega⟩, hx⟩
  change divisorsIn n (2*q+1) x = {a} at ha
  rw [ha, Set.mem_singleton_iff] at h₁ h₂
  omega

private lemma shrink {n q : ℕ} (hnq : n < q) :
    exactlyOneDivisorIn n (2*q+1) ⊆ exactlyOneDivisorIn n (2*q) := by
  intro x hx
  have hnd : ¬ 2*q ∣ x := fun h => multiple_excluded hnq h hx
  have he : divisorsIn n (2*q) x = divisorsIn n (2*q+1) x := by
    ext d
    change ((n < d ∧ d < 2*q) ∧ d ∣ x) ↔ ((n < d ∧ d < 2*q+1) ∧ d ∣ x)
    constructor
    · exact fun h => ⟨⟨h.1.1,by omega⟩,h.2⟩
    · rintro ⟨⟨h₁,h₂⟩,hd⟩
      have hne : d ≠ 2*q := fun h => hnd (h ▸ hd)
      exact ⟨⟨h₁,by omega⟩,hd⟩
  change (divisorsIn n (2*q) x).ncard = 1
  rw [he]
  exact hx

private lemma lost {n q : ℕ} (hn : 2 ≤ n) (hnq : n < q) (hq : q.Prime) :
    2*q ∈ exactlyOneDivisorIn n (2*q) := by
  apply Set.ncard_eq_one.mpr
  refine ⟨q, ?_⟩
  ext d
  change ((n < d ∧ d < 2*q) ∧ d ∣ 2*q) ↔ d = q
  constructor
  · rintro ⟨⟨hd,hlt⟩,e,he⟩
    have hdiv : q ∣ d*e := he ▸ dvd_mul_left q 2
    rcases hq.dvd_mul.mp hdiv with h | h
    · obtain ⟨m, rfl⟩ := h
      by_cases hm : m ≤ 1
      · interval_cases m <;> simp_all
      · have := Nat.mul_le_mul_left q (show 2 ≤ m by omega)
        omega
    · have hepos : 0 < e := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at he; omega
      have hqe := Nat.le_of_dvd hepos h
      nlinarith [Nat.mul_le_mul (show 3 ≤ d by omega) hqe]
  · rintro rfl
    exact ⟨⟨hnq,by omega⟩,dvd_mul_left _ 2⟩

end Erdos692PrimeEndpoint

open Erdos692PrimeEndpoint Erdos692 in
theorem OMA.solution : OMA.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1.H2 := by
  classical
  intro δ hδ n q hn hnq hq
  let L := (2*q+1).factorial
  have hL : 0 < L := Nat.factorial_pos _
  let A := exactlyOneDivisorIn n (2*q)
  let B := exactlyOneDivisorIn n (2*q+1)
  have denA := density_count (fun x => x ∈ A) hL (common_period (by omega : 2*q ≤ 2*q+1)) (hδ n (2*q))
  have denB := density_count (fun x => x ∈ B) hL (common_period (le_refl (2*q+1))) (hδ n (2*q+1))
  rw [denA, denB]
  apply div_lt_div_of_pos_right _ (by exact_mod_cast hL)
  apply Nat.cast_lt.mpr
  simp only [Nat.count_eq_card_filter_range]
  apply Finset.card_lt_card
  apply lt_of_le_of_ne
  · exact Finset.monotone_filter_right _ fun x _ hx => shrink hnq hx
  · intro h
    have hx : 2*q ∈ (Finset.range L).filter (· ∈ A) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Nat.self_le_factorial (2*q+1); dsimp [L]; omega),lost hn hnq hq⟩
    rw [← h] at hx
    exact multiple_excluded hnq (dvd_refl _) (Finset.mem_filter.mp hx).2
