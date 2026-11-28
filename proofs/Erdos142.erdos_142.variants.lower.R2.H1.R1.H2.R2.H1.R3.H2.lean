import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R3
import Mathlib

/-!
# Step H2 of the reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H1.R3

Write f for r 3. Since 1 <= f N <= N, the exponent m = log2 (N / f N) satisfies
2^m f N <= N < 2^(m+1) f N. Let n be the least positive length with 2^m f n <= n; then
n <= N, every shorter positive length j has j < 2^m f j, and monotonicity of f at n - 1
(or f 1 >= 1 when n = 1) forces 2^m f n = n. The last inequality is subadditivity of the
extremal function: splitting a free subset of [1, M + N] at M and translating the upper part
gives r k (M + N) <= r k M + r k N, hence r k N <= (N / n + 1) r k n, and multiplying by n
gives n r k N <= 2 N r k n.
-/

namespace OMA.Helpers

open Erdos142

theorem crossFree_subset {s t : Set ℕ} {l : ℕ∞} (h : s.IsAPOfLengthFree l) (hts : t ⊆ s) :
    t.IsAPOfLengthFree l :=
  fun u hu hap => h u (hu.trans hts) hap

theorem crossFree_shift {s : Set ℕ} {l : ℕ∞} (M : ℕ) (h : s.IsAPOfLengthFree l)
    {t : Set ℕ} (hts : ∀ y ∈ t, y + M ∈ s) : t.IsAPOfLengthFree l := by
  intro u hu hap
  obtain ⟨a, d, hc, he⟩ := hap
  have hinj : Function.Injective (fun y : ℕ => y + M) := fun x y hxy => by simpa using hxy
  apply h ((fun y => y + M) '' u)
  · rintro _ ⟨y, hy, rfl⟩
    exact hts y (hu hy)
  · refine ⟨a + M, d, ?_, ?_⟩
    · show Set.encard _ = l
      rw [hinj.encard_image]
      exact hc
    · rw [he]
      ext x
      simp only [Set.mem_image, Set.mem_ofPred_eq, smul_eq_mul]
      constructor
      · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
        exact ⟨i, hi, by ring⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨a + i * d, ⟨i, hi, rfl⟩, by ring⟩

theorem crossCard_le {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hfree : (S : Set ℕ).IsAPOfLengthFree k) : S.card ≤ r k N := by
  unfold r Set.IsAPOfLengthFree.maxCard
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro _ ⟨T, hT, -, rfl⟩
    simpa using Finset.card_le_card hT
  · exact ⟨S, hS, hfree, rfl⟩

theorem crossMax_le {k N b : ℕ}
    (h : ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → (S : Set ℕ).IsAPOfLengthFree k → S.card ≤ b) :
    r k N ≤ b := by
  unfold r Set.IsAPOfLengthFree.maxCard
  apply csSup_le'
  rintro _ ⟨S, hS, hf, rfl⟩
  exact h S hS hf

theorem crossMax_le_self (k N : ℕ) : r k N ≤ N :=
  crossMax_le fun _ hS _ => by simpa using Finset.card_le_card hS

theorem crossMax_mono (k : ℕ) {M N : ℕ} (h : M ≤ N) : r k M ≤ r k N :=
  crossMax_le fun S hS hf => crossCard_le (hS.trans (Finset.Icc_subset_Icc le_rfl h)) hf

theorem crossMax_add (k M N : ℕ) : r k (M + N) ≤ r k M + r k N := by
  classical
  apply crossMax_le
  intro S hS hf
  rw [← Finset.card_filter_add_card_filter_not (s := S) (fun x => x ≤ M)]
  apply add_le_add
  · apply crossCard_le
    · intro x hx
      rw [Finset.mem_filter] at hx
      have := Finset.mem_Icc.mp (hS hx.1)
      exact Finset.mem_Icc.mpr ⟨this.1, hx.2⟩
    · exact crossFree_subset hf (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  · have hinj : Set.InjOn (fun x => x - M) ↑(S.filter fun x => ¬ x ≤ M) := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
      simp only at hxy
      omega
    rw [← Finset.card_image_of_injOn hinj]
    apply crossCard_le
    · intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [Finset.mem_filter] at hx
      have := Finset.mem_Icc.mp (hS hx.1)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · apply crossFree_shift M hf
      intro y hy
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter] at hy
      obtain ⟨x, ⟨hx, hxM⟩, rfl⟩ := hy
      have hx' : x - M + M = x := by omega
      rw [hx']
      exact hx

theorem crossMax_mul (k n q s : ℕ) : r k (q * n + s) ≤ q * r k n + r k s := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : (q + 1) * n + s = n + (q * n + s) := by ring
    rw [h1]
    calc r k (n + (q * n + s)) ≤ r k n + r k (q * n + s) := crossMax_add k n _
      _ ≤ r k n + (q * r k n + r k s) := Nat.add_le_add_left ih _
      _ = (q + 1) * r k n + r k s := by ring

theorem crossBlock (k n N : ℕ) (hn : 0 < n) (hnN : n ≤ N) : n * r k N ≤ 2 * N * r k n := by
  have hdiv : N / n * n + N % n = N := by rw [mul_comm]; exact Nat.div_add_mod N n
  have hmod : N % n ≤ n := (Nat.mod_lt N hn).le
  have h1 : r k N ≤ N / n * r k n + r k (N % n) := by
    have := crossMax_mul k n (N / n) (N % n)
    rwa [hdiv] at this
  have h2 : r k (N % n) ≤ r k n := crossMax_mono k hmod
  have h3 : n * (N / n) ≤ N := Nat.mul_div_le N n
  calc n * r k N ≤ n * (N / n * r k n + r k n) := Nat.mul_le_mul_left _ (by omega)
    _ = (n * (N / n) + n) * r k n := by ring
    _ ≤ (N + N) * r k n := Nat.mul_le_mul_right _ (by omega)
    _ = 2 * N * r k n := by ring

theorem crossOne_le (N : ℕ) (hN : 0 < N) : 1 ≤ r 3 N := by
  have h : ({1} : Finset ℕ).card ≤ r 3 N := by
    apply crossCard_le
    · intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
    · intro t ht hap
      exfalso
      have hc : t.encard = ((3 : ℕ) : ℕ∞) := hap.card
      have hle : t.encard ≤ 1 := by
        calc t.encard ≤ ({1} : Set ℕ).encard :=
              Set.encard_le_encard (by simpa using ht)
          _ = 1 := Set.encard_singleton 1
      rw [hc] at hle
      norm_num at hle
  simpa using h

end OMA.Helpers

open OMA.Helpers Erdos142 in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R3.H2 := by
  intro k N hN
  have h1 : 1 ≤ r 3 N := crossOne_le N hN
  have h2 : r 3 N ≤ N := crossMax_le_self 3 N
  have hq : N / r 3 N ≠ 0 := (Nat.div_pos h2 h1).ne'
  have hm1 : 2 ^ Nat.log 2 (N / r 3 N) ≤ N / r 3 N := Nat.pow_log_le_self 2 hq
  have hm2 : N / r 3 N < 2 ^ (Nat.log 2 (N / r 3 N) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  set m := Nat.log 2 (N / r 3 N)
  have hA : 2 ^ m * r 3 N ≤ N :=
    calc 2 ^ m * r 3 N ≤ N / r 3 N * r 3 N := Nat.mul_le_mul_right _ hm1
      _ ≤ N := Nat.div_mul_le_self N (r 3 N)
  have hB : N < 2 ^ (m + 1) * r 3 N := by
    have e := Nat.div_add_mod N (r 3 N)
    have l := Nat.mod_lt N (show 0 < r 3 N by omega)
    calc N < r 3 N * (N / r 3 N) + r 3 N := by omega
      _ = (N / r 3 N + 1) * r 3 N := by ring
      _ ≤ 2 ^ (m + 1) * r 3 N := Nat.mul_le_mul_right _ hm2
  classical
  have hex : ∃ j, 0 < j ∧ 2 ^ m * r 3 j ≤ j := ⟨N, hN, hA⟩
  obtain ⟨n, ⟨hn0, hnle⟩, hmin⟩ : ∃ n, (0 < n ∧ 2 ^ m * r 3 n ≤ n) ∧
      ∀ j < n, ¬ (0 < j ∧ 2 ^ m * r 3 j ≤ j) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hnN : n ≤ N := by
    by_contra hc
    exact hmin N (by omega) ⟨hN, hA⟩
  refine ⟨m, n, hn0, hnN, ?_, ?_, hB, crossBlock k n N hn0 hnN⟩
  · apply le_antisymm hnle
    rcases Nat.lt_or_ge 1 n with h | h
    · have hprev : n - 1 < 2 ^ m * r 3 (n - 1) := by
        by_contra hc
        exact hmin (n - 1) (by omega) ⟨by omega, by omega⟩
      have hmono := crossMax_mono 3 (Nat.sub_le n 1)
      calc n ≤ 2 ^ m * r 3 (n - 1) := by omega
        _ ≤ 2 ^ m * r 3 n := Nat.mul_le_mul_left _ hmono
    · have hn1 : n = 1 := by omega
      subst hn1
      have h3 := crossOne_le 1 one_pos
      have h4 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      calc 1 = 1 * 1 := rfl
        _ ≤ 2 ^ m * r 3 1 := Nat.mul_le_mul h4 h3
  · intro j hj hjn
    by_contra hc
    exact hmin j hjn ⟨hj, by omega⟩
