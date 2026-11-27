import OMAReductions.R_Erdos535_erdos_535_R2

/-!
# Uniform prime-exponent encoding

New formalization by Hanan Beer (@hananzlt).
This proves the encoding step in the Erdős 1964 prime-power reduction of Problem 535.
Reduction and statement: @JamesSlash, open-math-agents PR #3194.
Prime-exponent layers above the cutoff use even tags; odd tags pad every code to size `K`.
-/

namespace OMA.Erdos535Encoding

open Finset

private def tag (x : Σ _p : ℕ, ℕ) : ℕ := 2 * Nat.pair x.1 x.2

private theorem tag_injective : Function.Injective tag := by
  rintro ⟨p, i⟩ ⟨q, j⟩ h
  have hpair : Nat.pair p i = Nat.pair q j := by simpa [tag] using h
  have h := Nat.pair_eq_pair.mp hpair
  rcases h with ⟨rfl, rfl⟩
  rfl

private def layers (t n : ℕ) : Finset (Σ _p : ℕ, ℕ) :=
  (n.primeFactors.filter (t < ·)).sigma (fun p => range (n.factorization p))

private theorem layers_card (t n : ℕ) :
    (layers t n).card = ∑ p ∈ n.primeFactors.filter (t < ·), n.factorization p := by
  simp [layers]

private theorem mem_layers (t n p i : ℕ) :
    (⟨p, i⟩ : Σ _p : ℕ, ℕ) ∈ layers t n ↔ t < p ∧ i < n.factorization p := by
  simp only [layers, mem_sigma, mem_filter, mem_range]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · intro h
    have hp : p ∈ n.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      omega
    exact ⟨⟨hp, h.1⟩, h.2⟩

private def code (t K n : ℕ) : Finset ℕ :=
  (layers t n).image tag ∪ (range (K - (layers t n).card)).image (fun i => 2 * i + 1)

private theorem code_card {t K n : ℕ} (h : (layers t n).card ≤ K) :
    (code t K n).card = K := by
  have hd : Disjoint ((layers t n).image tag)
      ((range (K - (layers t n).card)).image (fun i => 2 * i + 1)) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨⟨p, i⟩, _, rfl⟩ := mem_image.mp hx
    obtain ⟨j, _, hj⟩ := mem_image.mp hy
    dsimp [tag] at hj
    omega
  have hi : Function.Injective (fun i : ℕ => 2 * i + 1) := by
    intro i j hij
    dsimp at hij
    omega
  rw [code, card_union_of_disjoint hd, card_image_of_injective _ tag_injective,
    card_image_of_injective _ hi, card_range]
  omega

private theorem even_mem_code (t K n p i : ℕ) :
    2 * Nat.pair p i ∈ code t K n ↔ t < p ∧ i < n.factorization p := by
  rw [code, mem_union]
  have heven : 2 * Nat.pair p i ∈ (layers t n).image tag ↔
      (⟨p, i⟩ : Σ _p : ℕ, ℕ) ∈ layers t n := by
    change tag ⟨p, i⟩ ∈ (layers t n).image tag ↔ _
    constructor
    · rintro hx
      obtain ⟨x, hx, heq⟩ := mem_image.mp hx
      exact tag_injective heq ▸ hx
    · exact mem_image_of_mem tag
  rw [heven, mem_layers]
  suffices 2 * Nat.pair p i ∉ (range (K - (layers t n).card)).image (fun j => 2 * j + 1) by
    simp [this]
  rintro hx
  obtain ⟨j, _, hj⟩ := mem_image.mp hx
  omega

private theorem factorization_le_log {n N : ℕ} (hn : n ≠ 0) (hnN : n ≤ N) (p : ℕ) :
    n.factorization p ≤ Nat.log 2 N := by
  by_cases hp : p.Prime
  · apply Nat.le_log_of_pow_le (by omega)
    exact (Nat.pow_le_pow_left hp.two_le (n.factorization p)).trans
      ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.ordProj_dvd n p)).trans hnN)
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

private def smallClass (t N n : ℕ) : Fin (t + 1) → Fin (Nat.log 2 N + 1) :=
  fun p => ⟨min (n.factorization p) (Nat.log 2 N), Nat.lt_succ_of_le (min_le_right _ _)⟩

private theorem smallClass_eq {t N a b : ℕ}
    (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N)
    (h : smallClass t N a = smallClass t N b) {p : ℕ} (hp : p ≤ t) :
    a.factorization p = b.factorization p := by
  have haa : a ≠ 0 := by have := (mem_Icc.mp ha).1; omega
  have hbb : b ≠ 0 := by have := (mem_Icc.mp hb).1; omega
  have heq := congrArg Fin.val (congrFun h ⟨p, by omega⟩)
  simpa only [smallClass,
    min_eq_left (factorization_le_log haa (mem_Icc.mp ha).2 p),
    min_eq_left (factorization_le_log hbb (mem_Icc.mp hb).2 p)] using heq

private theorem large_min_eq {t K a b c d : ℕ}
    (h : code t K a ∩ code t K b = code t K c ∩ code t K d) {p : ℕ} (hp : t < p) :
    min (a.factorization p) (b.factorization p) =
      min (c.factorization p) (d.factorization p) := by
  have heq (i : ℕ) :
      i < min (a.factorization p) (b.factorization p) ↔
        i < min (c.factorization p) (d.factorization p) := by
    have hi := Finset.ext_iff.mp h (2 * Nat.pair p i)
    simpa [mem_inter, even_mem_code, hp, lt_min_iff] using hi
  apply Nat.le_antisymm
  · by_contra! hlt
    have := (heq _).mp hlt
    omega
  · by_contra! hlt
    have := (heq _).mpr hlt
    omega

end OMA.Erdos535Encoding

open OMA.Erdos535Encoding in
theorem OMA.solution : OMA.R_Erdos535_erdos_535_R2.H2 := by
  intro t K N hK
  refine ⟨smallClass t N, code t K, ?_, ?_⟩
  · intro n hn
    exact code_card (by simpa only [layers_card] using hK n hn)
  · intro a ha b hb c hc d hd hab hac had hcode
    have ha0 : a ≠ 0 := by have := (Finset.mem_Icc.mp ha).1; omega
    have hb0 : b ≠ 0 := by have := (Finset.mem_Icc.mp hb).1; omega
    have hc0 : c ≠ 0 := by have := (Finset.mem_Icc.mp hc).1; omega
    have hd0 : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
    apply Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_left ha0) (Nat.gcd_ne_zero_left hc0)
    intro p
    simp only [Nat.factorization_gcd ha0 hb0, Nat.factorization_gcd hc0 hd0,
      Finsupp.inf_apply]
    change min (a.factorization p) (b.factorization p) =
      min (c.factorization p) (d.factorization p)
    rcases le_or_gt p t with hp | hp
    · rw [← smallClass_eq ha hb hab hp, ← smallClass_eq ha hc hac hp,
        ← smallClass_eq ha hd had hp]
    · exact large_min_eq hcode hp
