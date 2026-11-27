import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1
import Mathlib

/-! The frame equations send a common divisor across to the other closing quotient
and then force it to divide the opposite base product. -/

open Finset

namespace OMA.CoprimeFrame

theorem closing_coprime {a M N M' N' p q : ℕ} (haM : a ∣ M) (haN : Nat.Coprime a N)
    (h1 : p*M'+M = N*q) (h2 : q*N'+N = M*p) :
    Nat.Coprime p a := by
  let d := Nat.gcd p a
  have hp : d ∣ p := Nat.gcd_dvd_left p a
  have ha : d ∣ a := Nat.gcd_dvd_right p a
  have hdN : Nat.Coprime d N := haN.coprime_dvd_left ha
  have hdM := ha.trans haM
  have hNq : d ∣ N*q := h1 ▸ dvd_add (dvd_mul_of_dvd_left hp _) hdM
  have hq : d ∣ q := hdN.dvd_of_dvd_mul_left hNq
  have hMprod : d ∣ M*p := dvd_mul_of_dvd_left hdM _
  have hSum : d ∣ q*N'+N := h2.symm ▸ hMprod
  have hd : d ∣ N := by
    simpa using Nat.dvd_sub hSum (dvd_mul_of_dvd_left hq N')
  have hone : d ∣ 1 := by
    have h := Nat.dvd_gcd ha hd
    rwa [haN.gcd_eq_one] at h
  exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp hone)

theorem insert_pairwise (A : Finset ℕ) (p : ℕ) (hp : 2 ≤ p)
    (hA : Set.Pairwise (A : Set ℕ) Nat.Coprime)
    (hCop : ∀ a ∈ A, Nat.Coprime p a) :
    p ∉ A ∧ Set.Pairwise ((insert p A : Finset ℕ) : Set ℕ) Nat.Coprime := by
  refine ⟨fun h => ?_,?_⟩
  · have hEq := (hCop p h).gcd_eq_one
    rw [Nat.gcd_self] at hEq
    omega
  · intro a ha b hb hne
    change a ∈ insert p A at ha
    change b ∈ insert p A at hb
    rcases mem_insert.mp ha with rfl|ha' <;> rcases mem_insert.mp hb with rfl|hb'
    · exact (hne rfl).elim
    · exact hCop b hb'
    · exact (hCop a ha').symm
    · exact hA ha' hb' hne

end OMA.CoprimeFrame

theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H2 := by
  intro P Q _ _ _ _ hP hQ hCross
  dsimp only
  intro hlt hPN hQN hPD hQD
  let M := ∏ a ∈ P,a
  let N := ∏ b ∈ Q,b
  let M' := ∑ a ∈ P,M/a
  let N' := ∑ b ∈ Q,N/b
  let D := M*N-M'*N'
  let p := (M*N'+N^2)/D
  let q := (M'*N+M^2)/D
  change M'*N' < M*N at hlt
  change 2*D ≤ M*N'+N^2 at hPN
  change 2*D ≤ M'*N+M^2 at hQN
  change D ∣ M*N'+N^2 at hPD
  change D ∣ M'*N+M^2 at hQD
  have hD : 0 < D := Nat.sub_pos_of_lt hlt
  have hp : 2 ≤ p := (Nat.le_div_iff_mul_le hD).mpr hPN
  have hq : 2 ≤ q := (Nat.le_div_iff_mul_le hD).mpr hQN
  have hPmul : D*p = M*N'+N^2 := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hPD
  have hQmul : D*q = M'*N+M^2 := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hQD
  have ⟨hOne,hTwo⟩ := OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.frame_cross_eq
    hlt rfl hPmul hQmul
  have hPCop (a : ℕ) (ha : a ∈ P) : Nat.Coprime p a :=
    OMA.CoprimeFrame.closing_coprime (dvd_prod_of_mem id ha)
      (Nat.coprime_prod_right_iff.mpr (hCross a ha)) hOne hTwo
  have hQCop (b : ℕ) (hb : b ∈ Q) : Nat.Coprime q b :=
    OMA.CoprimeFrame.closing_coprime (dvd_prod_of_mem id hb)
      (Nat.coprime_prod_right_iff.mpr (fun a ha => (hCross a ha b hb).symm))
      hTwo hOne
  have ⟨hpFresh,hpAll⟩ := OMA.CoprimeFrame.insert_pairwise P p hp hP hPCop
  have ⟨hqFresh,hqAll⟩ := OMA.CoprimeFrame.insert_pairwise Q q hq hQ hQCop
  exact ⟨hp,hpFresh,hq,hqFresh,hpAll,hqAll⟩
