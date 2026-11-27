import OMAReductions.R_Erdos1204_erdos_1204_variants_A_lower_R1
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.RingTheory.Radical.NatInt

/-! Group the harmonic sum by radical. For radical d put D = d^z. Each n in
the group gives a distinct divisor b = dD/n of D with φ(b) = (D/n)φ(d).
The identity summing φ over the divisors of D bounds the group's contribution. -/
namespace OMA.SieveDenominator
open Finset UniqueFactorizationMonoid

lemma fiber (z d : ℕ) (hz : 1 ≤ z) (hd : Squarefree d) :
    ∑ n ∈ (Icc 1 z).filter (fun n => radical n = d), (n : ℝ)⁻¹ ≤ (d.totient : ℝ)⁻¹ := by
  classical
  let D := d ^ z
  let S := (Icc 1 z).filter fun n => radical n = d
  let b := fun n => D / n * d
  have hD : D ≠ 0 := pow_ne_zero _ hd.ne_zero
  have hf : 0 < d.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd.ne_zero)
  have facts (n : ℕ) (hn : n ∈ S) :
      b n ∈ D.divisors ∧ (b n).totient * n = D * d.totient := by
    obtain ⟨hI,hr⟩ := mem_filter.mp hn
    have hLo := (mem_Icc.mp hI).1
    have hHi := (mem_Icc.mp hI).2
    have hnd : n ∣ D := by
      calc n ∣ radical n ^ n := Nat.dvd_radical_pow_self (by omega)
           _ ∣ D := by rw [hr]; exact pow_dvd_pow d hHi
    have hmul := Nat.div_mul_cancel hnd
    have hdn : d ∣ n := hr ▸ radical_dvd_self
    have hb : b n ∣ D := by
      rw [← hmul]
      exact Nat.mul_dvd_mul_left _ hdn
    have hbp : (b n).primeFactors = d.primeFactors := by
      apply Subset.antisymm
      · simpa only [D, Nat.primeFactors_pow d (show z ≠ 0 by omega)] using Nat.primeFactors_mono hb hD
      · exact Nat.primeFactors_mono (dvd_mul_left d (D/n)) (fun e => hD (by simpa [e] using hb))
    have ht : (b n).totient = D / n * d.totient := by
      rw [Nat.totient_eq_div_primeFactors_mul (b n), hbp, Nat.prod_primeFactors_of_squarefree hd,
        Nat.totient_eq_div_primeFactors_mul d, Nat.prod_primeFactors_of_squarefree hd,
        Nat.div_self (Nat.pos_of_ne_zero hd.ne_zero), one_mul]
      simp only [b, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd.ne_zero)]
    exact ⟨Nat.mem_divisors.mpr ⟨hb,hD⟩, by rw [ht, Nat.mul_right_comm,hmul]⟩
  have inj : Set.InjOn b (S : Set ℕ) := by
    intro i hi j hj he
    have hi' := (facts i hi).2
    have hj' := (facts j hj).2
    rw [he] at hi'
    have hp := (Nat.totient_pos.mpr (Nat.pos_of_mem_divisors (facts j hj).1))
    exact Nat.eq_of_mul_eq_mul_left hp (hi'.trans hj'.symm)
  have sub : S.image b ⊆ D.divisors := by
    rintro _ hx
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hx
    exact (facts n hn).1
  have bound : ∑ n ∈ S, (b n).totient ≤ D := calc
    _ = ∑ m ∈ S.image b, m.totient := (sum_image inj).symm
    _ ≤ ∑ m ∈ D.divisors, m.totient := sum_le_sum_of_subset sub
    _ = D := Nat.sum_totient D
  have hDR : 0 < (D : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hD
  have hFR : 0 < (d.totient : ℝ) := by exact_mod_cast hf
  change ∑ n ∈ S, (n : ℝ)⁻¹ ≤ _
  calc
    _ = ∑ n ∈ S, ((b n).totient : ℝ) / ((D : ℝ) * d.totient) := by
      apply sum_congr rfl
      intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (show n ≠ 0 by have := (mem_Icc.mp (mem_filter.mp hn).1).1; omega)
      have ht : ((b n).totient : ℝ) * n = D * (d.totient : ℝ) := by exact_mod_cast (facts n hn).2
      field_simp
      linarith
    _ = (↑(∑ n ∈ S, (b n).totient) : ℝ) / ((D : ℝ) * d.totient) := by simp [sum_div]
    _ ≤ (D : ℝ) / ((D : ℝ) * d.totient) := by gcongr
    _ = _ := by field_simp

end OMA.SieveDenominator

open Finset UniqueFactorizationMonoid in
theorem OMA.solution : OMA.R_Erdos1204_erdos_1204_variants_A_lower_R1.H2 := by
  classical
  intro z hz
  have maps (n : ℕ) (hn : n ∈ Icc 1 z) : radical n ∈ (Icc 1 z).filter Squarefree := by
    obtain ⟨hn,hnz⟩ := mem_Icc.mp hn
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.radical_pos n,
      (Nat.radical_le_self_iff.mpr (by omega)).trans hnz⟩, squarefree_radical⟩
  calc
    _ ≤ (harmonic z : ℝ) := by simpa using log_add_one_le_harmonic z
    _ = ∑ n ∈ Icc 1 z, (n : ℝ)⁻¹ := by simp [harmonic_eq_sum_Icc]
    _ = ∑ d ∈ (Icc 1 z).filter Squarefree, ∑ n ∈ (Icc 1 z).filter (fun n => radical n = d),
        (n : ℝ)⁻¹ := (sum_fiberwise_of_maps_to maps _).symm
    _ ≤ _ := by
      apply sum_le_sum
      intro d hd
      simpa only [one_div] using OMA.SieveDenominator.fiber z d hz (mem_filter.mp hd).2
