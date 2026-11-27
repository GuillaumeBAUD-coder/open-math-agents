import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1
import Mathlib.Tactic

-- Step Erdos307.erdos_307.variants.coprime_one_notMem.R1.H2
-- Credit: @nijv

open Finset

lemma coprime_closing_quotient {P₀ Q₀ : Finset ℕ}
    (hPQcop : ∀ a ∈ P₀, ∀ b ∈ Q₀, Nat.Coprime a b)
    {Δ p : ℕ}
    (hp_eq : Δ * p = (∏ a ∈ P₀, a) * (∑ b ∈ Q₀, (∏ y ∈ Q₀, y) / b) + (∏ b ∈ Q₀, b) ^ 2) :
    ∀ a ∈ P₀, Nat.Coprime p a := by
  intro a ha
  rw [Nat.Coprime]
  apply Nat.dvd_one.mp
  have haN : Nat.Coprime a (∏ b ∈ Q₀, b) :=
    Nat.Coprime.prod_right fun b hb => hPQcop a ha b hb
  have haN2 : Nat.Coprime a ((∏ b ∈ Q₀, b) ^ 2) := haN.pow_right 2
  set g := Nat.gcd p a
  have hgp : g ∣ p := Nat.gcd_dvd_left p a
  have hga : g ∣ a := Nat.gcd_dvd_right p a
  have hgM : g ∣ ∏ x ∈ P₀, x := dvd_trans hga (Finset.dvd_prod_of_mem _ ha)
  have hgΔp : g ∣ Δ * p := dvd_mul_of_dvd_right hgp Δ
  rw [hp_eq] at hgΔp
  have hgMN' : g ∣ (∏ x ∈ P₀, x) * (∑ b ∈ Q₀, (∏ y ∈ Q₀, y) / b) :=
    dvd_mul_of_dvd_left hgM _
  have hgN2 : g ∣ (∏ b ∈ Q₀, b) ^ 2 := (Nat.dvd_add_right hgMN').mp hgΔp
  have hggcd : g ∣ Nat.gcd a ((∏ b ∈ Q₀, b) ^ 2) := Nat.dvd_gcd hga hgN2
  rwa [haN2] at hggcd

theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H2 := by
  unfold OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H2
  intro P₀ Q₀ _hP₀ne _hQ₀ne _hP₀2 _hQ₀2 hP₀cop hQ₀cop hPQcop
    M M' N N' hMlt h2p h2q hdvdp hdvdq p q
  set Δ := M * N - M' * N'
  have hΔpos : 0 < Δ := by omega
  have hp2 : 2 ≤ p := by
    have h := Nat.div_le_div_right (c := Δ) h2p
    rwa [Nat.mul_div_cancel _ hΔpos] at h
  have hq2 : 2 ≤ q := by
    have h := Nat.div_le_div_right (c := Δ) h2q
    rwa [Nat.mul_div_cancel _ hΔpos] at h
  have hp_mul : Δ * p = M * N' + N ^ 2 := Nat.mul_div_cancel' hdvdp
  have hq_mul : Δ * q = N * M' + M ^ 2 := by
    have h : Δ * q = M' * N + M ^ 2 := Nat.mul_div_cancel' hdvdq
    linarith
  have hQPcop : ∀ b ∈ Q₀, ∀ a ∈ P₀, Nat.Coprime b a :=
    fun b hb a ha => (hPQcop a ha b hb).symm
  have hpcop : ∀ a ∈ P₀, Nat.Coprime p a := coprime_closing_quotient hPQcop hp_mul
  have hqcop : ∀ b ∈ Q₀, Nat.Coprime q b := coprime_closing_quotient hQPcop hq_mul
  have hpnot : p ∉ P₀ := by
    intro hpin
    have h1 : Nat.gcd p p = 1 := hpcop p hpin
    rw [Nat.gcd_self] at h1
    omega
  have hqnot : q ∉ Q₀ := by
    intro hqin
    have h1 : Nat.gcd q q = 1 := hqcop q hqin
    rw [Nat.gcd_self] at h1
    omega
  refine ⟨hp2, hpnot, hq2, hqnot, ?_, ?_⟩
  · rw [Finset.coe_insert]
    exact hP₀cop.insert fun a ha _ => ⟨hpcop a ha, (hpcop a ha).symm⟩
  · rw [Finset.coe_insert]
    exact hQ₀cop.insert fun b hb _ => ⟨hqcop b hb, (hqcop b hb).symm⟩
