import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1

namespace OMA.FrameCoprime

lemma quotient (A B : Finset ℕ) (L D : ℕ)
    (hc : ∀ a ∈ A, ∀ b ∈ B, Nat.Coprime a b)
    (hd : D ∣ (∏ a ∈ A, a)*L + (∏ b ∈ B, b)^2) :
    ∀ a ∈ A, Nat.Coprime (((∏ a ∈ A, a)*L + (∏ b ∈ B, b)^2)/D) a := by
  intro a ha
  have hp : a.Coprime (∏ b ∈ B, b) := Nat.coprime_prod_right_iff.mpr (hc a ha)
  have had : a ∣ (∏ a ∈ A, a)*L :=
    dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (fun x => x) ha) L
  have hnum := (Nat.coprime_add_iff_right had).mpr (hp.pow_right 2)
  exact (Nat.Coprime.of_dvd_right (Nat.div_dvd_of_dvd hd) hnum).symm

end OMA.FrameCoprime

-- Step Erdos307.erdos_307.variants.coprime_one_notMem.R1.H2: hypothesis H2 of reduction Erdos307.erdos_307.variants.coprime_one_notMem.R1
-- Credit: @DeepDuke
-- H2 := ∀ (P₀ Q₀ : Finset ℕ),     P₀.Nonempty → Q₀.Nonempty →     (∀ a ∈ P₀, 2 ≤ a) → (∀ b ∈ Q₀, 2 ≤ b) →     Set.Pairwise (P₀ : Set ℕ) Nat.Coprime →     Set.Pairwise (Q₀ : Set ℕ) Nat.Coprime →     (∀ a ∈ P₀, ∀ b ∈ Q₀, Nat.Coprime a b) →     let M := ∏ a ∈ P₀, a     let M' := ∑ a ∈ P₀, M / a     let N := ∏ b ∈ Q₀, b     let N' := ∑ b ∈ Q₀, N / b     M' * N' < M * N →     2 * (M * N - M' * N') ≤ M * N' + N ^ 2 →     2 * (M * N - M' * N') ≤ M' * N + M ^ 2 →     (M * N - M' * N') ∣ (M * N' + N ^ 2) →     (M * N - M' * N') ∣ (M' * N + M ^ 2) →     let p := (M * N' + N ^ 2) / (M * N - M' * N')     let q := (M' * N + M ^ 2) / (M * N - M' * N')     2 ≤ p ∧ p ∉ P₀ ∧ 2 ≤ q ∧ q ∉ Q₀ ∧       Set.Pairwise ((insert p P₀ : Finset ℕ) : Set ℕ) Nat.Coprime ∧       Set.Pairwise ((insert q Q₀ : Finset ℕ) : Set ℕ) Nat.Coprime  -- H3: Lossless pure-integer Diophantine frame existence (equivalent to the full problem by erasing -- one element from each side of any solution).

theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H2 := by
  intro P Q hPne hQne hP2 hQ2 hP hQ hcross
  dsimp only
  let M := ∏ a ∈ P, a
  let U := ∑ a ∈ P, M/a
  let N := ∏ b ∈ Q, b
  let V := ∑ b ∈ Q, N/b
  let D := M*N-U*V
  let p := (M*V+N^2)/D
  let q := (U*N+M^2)/D
  change U*V < M*N → 2*D ≤ M*V+N^2 → 2*D ≤ U*N+M^2 →
    D ∣ M*V+N^2 → D ∣ U*N+M^2 →
    2 ≤ p ∧ p ∉ P ∧ 2 ≤ q ∧ q ∉ Q ∧
      Set.Pairwise ((insert p P : Finset ℕ) : Set ℕ) Nat.Coprime ∧
      Set.Pairwise ((insert q Q : Finset ℕ) : Set ℕ) Nat.Coprime
  intro hlt hpbound hqbound hpdiv hqdiv
  have hD : 0 < D := Nat.sub_pos_of_lt hlt
  have hp2 : 2 ≤ p := (Nat.le_div_iff_mul_le hD).mpr hpbound
  have hq2 : 2 ≤ q := (Nat.le_div_iff_mul_le hD).mpr hqbound
  have hpc : ∀ a ∈ P, p.Coprime a := OMA.FrameCoprime.quotient P Q V D hcross hpdiv
  have hqc : ∀ b ∈ Q, q.Coprime b := by
    have hd : D ∣ N*U+M^2 := by simpa only [mul_comm N U] using hqdiv
    have hc : ∀ b ∈ Q, ∀ a ∈ P, Nat.Coprime b a :=
      fun b hb a ha => (hcross a ha b hb).symm
    have hh := OMA.FrameCoprime.quotient Q P U D hc hd
    change ∀ b ∈ Q, ((N*U+M^2)/D).Coprime b at hh
    simpa only [q, mul_comm N U] using hh
  have hpnot : p ∉ P := by
    intro h
    have hh := hpc p h
    simp only [Nat.coprime_self] at hh
    omega
  have hqnot : q ∉ Q := by
    intro h
    have hh := hqc q h
    simp only [Nat.coprime_self] at hh
    omega
  refine ⟨hp2, hpnot, hq2, hqnot, ?_, ?_⟩
  · rw [Finset.coe_insert]
    exact hP.insert (fun a ha _ => ⟨hpc a ha, (hpc a ha).symm⟩)
  · rw [Finset.coe_insert]
    exact hQ.insert (fun b hb _ => ⟨hqc b hb, (hqc b hb).symm⟩)

