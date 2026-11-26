import FormalConjectures.ErdosProblems.«535»

/-! The fixed-petal sunflower bound transfers to integers via prime-exponent thinning. -/

namespace OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1

open Erdos535

def H1 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ C : ℕ, 1 ≤ C ∧
    ∀ (k : ℕ) (F : Finset (Finset ℕ)),
      (∀ A ∈ F, A.card = k) → C ^ k < F.card →
      ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset ℕ,
        ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K

def H2 : Prop :=
  ∀ (r k : ℕ) (A : Finset ℕ), AllBigOmega k A →
    ∃ B ⊆ A, A.card ≤ 2 ^ k * B.card ∧
      ∃ enc : ℕ → Finset ℕ, Set.InjOn enc (B : Set ℕ) ∧
        (∀ n ∈ B, (enc n).card = k) ∧
        (∀ S ⊆ B, S.card = r →
          (∃ K : Finset ℕ,
            (S : Set ℕ).Pairwise (fun a b => enc a ∩ enc b = K)) →
          ∃ d, 0 < d ∧ (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d) ∧
            ∀ a ∈ S, ∃ b, a = d * b ∧ Nat.gcd b d = 1)

theorem main : H1 → H2 → type_of% @Erdos535.erdos_535.variants.sunflower_strong := by
  intro h₁ h₂ r hr
  obtain ⟨C, hC, hSunflower⟩ := h₁ r hr
  refine ⟨↑(2 * C : ℕ), by exact_mod_cast (by omega : 0 < 2 * C), ?_⟩
  intro k A hA hNoSunflower
  obtain ⟨B, hBA, hlarge, enc, henc, hsize, hlift⟩ := h₂ r k A hA
  have hBound : B.card ≤ C ^ k := by
    by_contra h
    have hG : C ^ k < (B.image enc).card := by
      rwa [Finset.card_image_of_injOn henc, ← not_le]
    obtain ⟨G, hGB, hGr, K, hGinter⟩ :=
      hSunflower k (B.image enc)
        (by
          intro L hL
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hL
          exact hsize n hn)
        hG
    let S := B.filter (fun n => enc n ∈ G)
    have hSB : S ⊆ B := Finset.filter_subset _ _
    have hSG : S.image enc = G := by
      ext L
      constructor
      · intro hL
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hL
        exact (Finset.mem_filter.mp hn).2
      · intro hL
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (hGB hL)
        exact Finset.mem_image.mpr ⟨n, Finset.mem_filter.mpr ⟨hn, hL⟩, rfl⟩
    have hencS : Set.InjOn enc (S : Set ℕ) :=
      henc.mono (by exact hSB)
    have hSr : S.card = r := by
      rw [← Finset.card_image_of_injOn hencS, hSG, hGr]
    apply hNoSunflower S (hSB.trans hBA) hSr
    refine hlift S hSB hSr ⟨K, ?_⟩
    intro a ha b hb hab
    exact hGinter _ (Finset.mem_filter.mp ha).2 _ (Finset.mem_filter.mp hb).2
      (fun hEq => hab (hencS ha hb hEq))
  have hCard : A.card ≤ (2 * C) ^ k := by
    rw [mul_pow]
    exact hlarge.trans (Nat.mul_le_mul_left _ hBound)
  exact_mod_cast hCard

end OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1
