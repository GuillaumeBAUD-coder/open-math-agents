import OMAReductions.R_Kourovka_1_40_kourovka_1_40_R1

/-!
# Proof of `Kourovka.1.40.kourovka_1_40.R1.H1`

Proves that if a group `G` is the product `H ⊔ K = ⊤` of two normal Engel subgroups `H` and `K`
whose intersection `H ⊓ K` lies in the center of `G`, then `G` is an Engel group.

Proof outline:
1. Since `H` is normal and `H ⊔ K = ⊤`, every element of `G` can be written as `h * k` with
   `h ∈ H` and `k ∈ K`.
2. For `h ∈ H` and `k ∈ K`, normality of `H` and `K` yields `⁅h, k⁆ ∈ H ⊓ K ≤ Subgroup.center G`.
3. Passing to the quotient `G ⧸ Subgroup.center G`, the images of `H` and `K` commute elementwise,
   so `(h, k) ↦ π h * π k` is a surjective group homomorphism `H × K →* G ⧸ Subgroup.center G`.
4. Since `H` and `K` are Engel, `H × K` is Engel componentwise; taking `n = max n₁ n₂` sends
   `engelCommutator x y n` into `Subgroup.center G`, and one more commutator step kills it:
   `engelCommutator x y (n + 1) = 1`.
-/

namespace Kourovka140R1H1Proof

open Kourovka.«1.40»
open scoped commutatorElement

private lemma engelCommutator_map {A B : Type*} [Group A] [Group B] (f : A →* B)
    (a b : A) : ∀ n : ℕ, f (engelCommutator a b n) = engelCommutator (f a) (f b) n
  | 0 => rfl
  | n + 1 => by
    simp only [engelCommutator, map_commutatorElement, engelCommutator_map f a b n]

private lemma engelCommutator_one_left {A : Type*} [Group A] (y : A) :
    ∀ n : ℕ, engelCommutator (1 : A) y n = 1
  | 0 => rfl
  | n + 1 => by
    simp only [engelCommutator, engelCommutator_one_left y n, commutatorElement_one_left]

private lemma engelCommutator_add {A : Type*} [Group A] (x y : A) (n : ℕ) :
    ∀ m : ℕ, engelCommutator x y (n + m) = engelCommutator (engelCommutator x y n) y m
  | 0 => rfl
  | m + 1 => by
    rw [← Nat.add_assoc, engelCommutator, engelCommutator_add x y n m, engelCommutator]

private lemma engelCommutator_eq_one_of_le {A : Type*} [Group A] {x y : A} {n m : ℕ}
    (hnm : n ≤ m) (h : engelCommutator x y n = 1) : engelCommutator x y m = 1 := by
  have hm : m = n + (m - n) := (Nat.add_sub_cancel' hnm).symm
  rw [hm, engelCommutator_add, h, engelCommutator_one_left]

private lemma engelCommutator_prod {A B : Type*} [Group A] [Group B]
    (a₁ a₂ : A) (b₁ b₂ : B) :
    ∀ n : ℕ, engelCommutator (a₁, b₁) (a₂, b₂) n =
      (engelCommutator a₁ a₂ n, engelCommutator b₁ b₂ n)
  | 0 => rfl
  | n + 1 => by
    simp only [engelCommutator, engelCommutator_prod a₁ a₂ b₁ b₂ n]
    rfl

private lemma exists_mul_of_sup_eq_top {G : Type*} [Group G] {H K : Subgroup G}
    (hH : H.Normal) (hsup : H ⊔ K = ⊤) (g : G) :
    ∃ h ∈ H, ∃ k ∈ K, g = h * k := by
  let S : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * (k₁ * h₂ * k₁⁻¹), H.mul_mem hh₁ (hH.conj_mem h₂ hh₂ k₁),
          k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨k⁻¹ * h⁻¹ * k, ?_, k⁻¹, K.inv_mem hk, ?_⟩
        · have := hH.conj_mem h⁻¹ (H.inv_mem hh) k⁻¹
          simpa [inv_inv] using this
        · group }
  have hHS : H ≤ S := fun h hh => ⟨h, hh, 1, K.one_mem, (mul_one h).symm⟩
  have hKS : K ≤ S := fun k hk => ⟨1, H.one_mem, k, hk, (one_mul k).symm⟩
  have htop : (⊤ : Subgroup G) ≤ S := hsup ▸ sup_le hHS hKS
  exact htop (Subgroup.mem_top g)

private lemma commutator_mem_inf {G : Type*} [Group G] {H K : Subgroup G}
    (hH : H.Normal) (hK : K.Normal) {h k : G} (hh : h ∈ H) (hk : k ∈ K) :
    h * k * h⁻¹ * k⁻¹ ∈ H ⊓ K := by
  refine ⟨?_, ?_⟩
  · have h1 : k * h⁻¹ * k⁻¹ ∈ H := hH.conj_mem h⁻¹ (H.inv_mem hh) k
    have h2 : h * (k * h⁻¹ * k⁻¹) ∈ H := H.mul_mem hh h1
    simpa [mul_assoc] using h2
  · have h1 : h * k * h⁻¹ ∈ K := hK.conj_mem k hk h
    have h2 : (h * k * h⁻¹) * k⁻¹ ∈ K := K.mul_mem h1 (K.inv_mem hk)
    simpa [mul_assoc] using h2

end Kourovka140R1H1Proof

theorem OMA.solution : OMA.R_Kourovka_1_40_kourovka_1_40_R1.H1 := by
  intro G _ H K hH hK hHE hKE hsup hcenter y x
  let Z : Subgroup G := Subgroup.center G
  let π : G →* G ⧸ Z := QuotientGroup.mk' Z
  have hcomm : ∀ (h : H) (k : K), π h.1 * π k.1 = π k.1 * π h.1 := by
    intro h k
    have hmem : h.1 * k.1 * h.1⁻¹ * k.1⁻¹ ∈ Z := hcenter (Kourovka140R1H1Proof.commutator_mem_inf hH hK h.2 k.2)
    have h1 : π (h.1 * k.1 * h.1⁻¹ * k.1⁻¹) = 1 := (QuotientGroup.eq_one_iff (h.1 * k.1 * h.1⁻¹ * k.1⁻¹)).mpr hmem
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π h.1 * π k.1
        = (π h.1 * π k.1 * (π h.1)⁻¹ * (π k.1)⁻¹) * (π k.1 * π h.1) := by group
      _ = 1 * (π k.1 * π h.1) := by rw [h1]
      _ = π k.1 * π h.1 := one_mul _
  let φ : H × K →* G ⧸ Z :=
    { toFun := fun p => π p.1.1 * π p.2.1
      map_one' := by simp
      map_mul' := by
        rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩
        change π (h₁.1 * h₂.1) * π (k₁.1 * k₂.1) = (π h₁.1 * π k₁.1) * (π h₂.1 * π k₂.1)
        rw [map_mul, map_mul]
        calc π h₁.1 * π h₂.1 * (π k₁.1 * π k₂.1)
            = π h₁.1 * (π h₂.1 * π k₁.1) * π k₂.1 := by group
          _ = π h₁.1 * (π k₁.1 * π h₂.1) * π k₂.1 := by rw [hcomm h₂ k₁]
          _ = (π h₁.1 * π k₁.1) * (π h₂.1 * π k₂.1) := by group }
  obtain ⟨h₁, hh₁, k₁, hk₁, hx⟩ := Kourovka140R1H1Proof.exists_mul_of_sup_eq_top hH hsup x
  obtain ⟨h₂, hh₂, k₂, hk₂, hy⟩ := Kourovka140R1H1Proof.exists_mul_of_sup_eq_top hH hsup y
  obtain ⟨n₁, hn₁⟩ := hHE ⟨h₂, hh₂⟩ ⟨h₁, hh₁⟩
  obtain ⟨n₂, hn₂⟩ := hKE ⟨k₂, hk₂⟩ ⟨k₁, hk₁⟩
  let n := max n₁ n₂
  have hn₁' : Kourovka.«1.40».engelCommutator (⟨h₁, hh₁⟩ : H) ⟨h₂, hh₂⟩ n = 1 :=
    Kourovka140R1H1Proof.engelCommutator_eq_one_of_le (le_max_left n₁ n₂) hn₁
  have hn₂' : Kourovka.«1.40».engelCommutator (⟨k₁, hk₁⟩ : K) ⟨k₂, hk₂⟩ n = 1 :=
    Kourovka140R1H1Proof.engelCommutator_eq_one_of_le (le_max_right n₁ n₂) hn₂
  have hprod : Kourovka.«1.40».engelCommutator
      ((⟨h₁, hh₁⟩ : H), (⟨k₁, hk₁⟩ : K)) (⟨h₂, hh₂⟩, ⟨k₂, hk₂⟩) n = 1 := by
    rw [Kourovka140R1H1Proof.engelCommutator_prod, hn₁', hn₂']
    rfl
  have hφx : φ (⟨h₁, hh₁⟩, ⟨k₁, hk₁⟩) = π x := by
    change π h₁ * π k₁ = π x
    rw [hx, map_mul]
  have hφy : φ (⟨h₂, hh₂⟩, ⟨k₂, hk₂⟩) = π y := by
    change π h₂ * π k₂ = π y
    rw [hy, map_mul]
  have hq : π (Kourovka.«1.40».engelCommutator x y n) = 1 := by
    rw [Kourovka140R1H1Proof.engelCommutator_map π, ← hφx, ← hφy,
      ← Kourovka140R1H1Proof.engelCommutator_map φ, hprod, map_one]
  have hmemZ : Kourovka.«1.40».engelCommutator x y n ∈ Z :=
    (QuotientGroup.eq_one_iff _).mp hq
  refine ⟨n + 1, ?_⟩
  rw [Kourovka.«1.40».engelCommutator, commutatorElement_def]
  have hzc : Kourovka.«1.40».engelCommutator x y n * y = y * Kourovka.«1.40».engelCommutator x y n :=
    (Subgroup.mem_center_iff.mp hmemZ y).symm
  rw [hzc]
  group
