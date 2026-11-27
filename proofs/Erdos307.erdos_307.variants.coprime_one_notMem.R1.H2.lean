import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1

/-!
A prime shared by a new denominator and the product on its side would
divide the new denominator on the opposite side, then that side's product.
-/

open Finset

namespace OMA.E307

lemma coprime_close {M Mp N Np p q : ℕ} (hMN : M.Coprime N)
    (hp : p * Mp + M = N * q) (hq : q * Np + N = M * p) : p.Coprime M := by
  by_contra h
  obtain ⟨r, hr, hrp, hrM⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hrN : ¬ r ∣ N := by
    intro hd
    have hd1 := Nat.dvd_gcd hrM hd
    rw [hMN.gcd_eq_one] at hd1
    exact hr.not_dvd_one hd1
  have hrNq : r ∣ N * q := by
    rw [← hp]
    exact dvd_add (dvd_mul_of_dvd_left hrp _) hrM
  have hrq : r ∣ q := (hr.dvd_mul.mp hrNq).resolve_left hrN
  have he : r ∣ q * Np + N := hq.symm ▸ dvd_mul_of_dvd_left hrM p
  exact hrN ((Nat.dvd_add_iff_right (dvd_mul_of_dvd_left hrq Np)).mpr he)

lemma insert_coprime {A : Finset ℕ} {p : ℕ} (hp : 2 ≤ p)
    (hPair : Set.Pairwise (A : Set ℕ) Nat.Coprime)
    (hC : p.Coprime (∏ a ∈ A, a)) :
    p ∉ A ∧ Set.Pairwise ((insert p A : Finset ℕ) : Set ℕ) Nat.Coprime := by
  have hEach (a : ℕ) (ha : a ∈ A) : p.Coprime a :=
    hC.coprime_dvd_right (Finset.dvd_prod_of_mem id ha)
  refine ⟨?_, ?_⟩
  · intro hpA
    have h := hEach p hpA
    rw [Nat.coprime_self] at h
    omega
  · rw [Finset.coe_insert, Set.pairwise_insert]
    exact ⟨hPair, fun a ha _ => ⟨hEach a ha, (hEach a ha).symm⟩⟩

end OMA.E307

theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H2 := by
  intro P Q hPne hQne hP hQ pairP pairQ across M Mp N Np hlt hlowp hlowq hdivp hdivq p q
  have hMN : M.Coprime N :=
    Nat.coprime_prod_left_iff.mpr fun a ha =>
      Nat.coprime_prod_right_iff.mpr (across a ha)
  have hpos : 0 < M * N - Mp * Np := Nat.sub_pos_of_lt hlt
  have hp2 : 2 ≤ p := (Nat.le_div_iff_mul_le hpos).mpr hlowp
  have hq2 : 2 ≤ q := (Nat.le_div_iff_mul_le hpos).mpr hlowq
  have hpEq : (M * N - Mp * Np) * p = M * Np + N^2 := Nat.mul_div_cancel' hdivp
  have hqEq : (M * N - Mp * Np) * q = Mp * N + M^2 := Nat.mul_div_cancel' hdivq
  obtain ⟨hCrossP, hCrossQ⟩ :=
    OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.frame_cross_eq hlt rfl hpEq hqEq
  obtain ⟨hpNot, hnewP⟩ :=
    OMA.E307.insert_coprime hp2 pairP (OMA.E307.coprime_close hMN hCrossP hCrossQ)
  obtain ⟨hqNot, hnewQ⟩ :=
    OMA.E307.insert_coprime hq2 pairQ (OMA.E307.coprime_close hMN.symm hCrossQ hCrossP)
  exact ⟨hp2, hpNot, hq2, hqNot, hnewP, hnewQ⟩
