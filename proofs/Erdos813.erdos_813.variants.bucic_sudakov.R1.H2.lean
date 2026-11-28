import OMAReductions.R_Erdos813_erdos_813_variants_bucic_sudakov_R1
import Mathlib

-- Step Erdos813.erdos_813.variants.bucic_sudakov.R1.H2: hypothesis H2 of reduction Erdos813.erdos_813.variants.bucic_sudakov.R1

/-!
# Bucić–Sudakov: `h(n) ≥ n^{5/12 - ε}` for large `n` (original formalization)

We work in the complement `Γ = Gᶜ`, where every 7 vertices contain an independent 3-set, and show
that `Γ` has an independent set of size `a = ⌈n^{5/12-ε}⌉` once `n` is large. The argument follows
Section 2.2 of Bucić–Sudakov, *Large independent sets from local considerations* (Combinatorica 2023,
arXiv:2007.03667), reorganised for formalization:

* a `K4` forces a triangle-free remainder, so `Γ` is `K4`-free; the `C5`-blow-up `H7` is excluded
  directly from the 7-vertex condition (`h7`);
* out-neighbourhoods `out v ⊆ N(v)` in which independent sets expand by a factor `x ≈ n/a²`;
* the `L / C / I` partition of `v`-extending vertices with star centres (pairwise version of
  Lemma 2.4d, no connected components);
* one Star lemma for both claims: a greedy matching regime and a grid regime (our version of
  Lemma 2.6 with explicit parameters; sinks that are leaves are discarded);
* Claim 1 (`T ≳ x⁴ n³ / a⁴`), Claim 2 with dyadic regularisation, and the final double count of
  `K4`-minus-an-edge configurations, all with linear "Turán-lite" and `λ`-tricks instead of
  Cauchy–Schwarz over vertices.

All lemmas are proved from scratch here (route planned with Claude Fable).
-/

-- ===== B1 =====
section S_B1

/-! Basic graph facts for the Bucić–Sudakov argument (original). -/

open Finset

namespace E813

noncomputable section
open Classical

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- neighbourhood as a finset -/
def Nb (v : V) : Finset V := univ.filter (G.Adj v)

/-- independent finset -/
def Ind (A : Finset V) : Prop := ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y

/-- every 7 vertices contain an independent 3-set -/
def Seven3 : Prop := ∀ S : Finset V, S.card = 7 → ∃ t ⊆ S, t.card = 3 ∧ Ind G t

def K4free : Prop := ∀ p q r s : V, G.Adj p q → G.Adj p r → G.Adj p s → G.Adj q r →
  G.Adj q s → G.Adj r s → False

/-- all independent sets have fewer than `a` elements -/
def IndLt (a : ℕ) : Prop := ∀ A : Finset V, Ind G A → A.card < a

/-- ordered edge count inside `A` -/
def edges (A : Finset V) : ℕ := ∑ z ∈ A, (A.filter (G.Adj z)).card

/-- no triangle inside `A` -/
def TriFree (A : Finset V) : Prop := ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, G.Adj x y → G.Adj x z →
  G.Adj y z → False

variable {G}

@[simp] lemma mem_Nb {v w : V} : w ∈ Nb G v ↔ G.Adj v w := by simp [Nb]

lemma Ind.mono {A B : Finset V} (h : Ind G B) (hAB : A ⊆ B) : Ind G A :=
  fun x hx y hy => h x (hAB hx) y (hAB hy)

lemma ind_empty : Ind G (∅ : Finset V) := by intro x hx; simp at hx

/-- Greedy: a conflict-free subfamily of proportional size. -/
lemma greedy {β : Type*} (P : Finset β) (R : β → β → Prop) (hsymm : ∀ p q, R p q → R q p)
    (D : ℕ) (hD : ∀ p ∈ P, (P.filter (R p)).card ≤ D) :
    ∃ Q ⊆ P, (∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → ¬ R p q) ∧ P.card ≤ (D + 1) * Q.card := by
  obtain ⟨Q, hQ, hmax⟩ := (P.powerset.filter
    (fun Q => ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → ¬ R p q)).exists_max_image card
    ⟨∅, by simp⟩
  simp only [mem_filter, mem_powerset] at hQ
  refine ⟨Q, hQ.1, hQ.2, ?_⟩
  have hcov : P ⊆ Q ∪ Q.biUnion (fun q => P.filter (R q)) := by
    intro p hp
    by_cases hpQ : p ∈ Q
    · exact mem_union_left _ hpQ
    · apply mem_union_right
      by_contra hcon
      have hmem : insert p Q ∈ P.powerset.filter
          (fun Q => ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → ¬ R p q) := by
        simp only [mem_filter, mem_powerset]
        refine ⟨insert_subset hp hQ.1, ?_⟩
        intro x hx y hy hxy
        rw [mem_insert] at hx hy
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · exact absurd rfl hxy
        · intro hR; exact hcon (mem_biUnion.2 ⟨y, hy, mem_filter.2 ⟨hp, hsymm _ _ hR⟩⟩)
        · intro hR; exact hcon (mem_biUnion.2 ⟨x, hx, mem_filter.2 ⟨hp, hR⟩⟩)
        · exact hQ.2 x hx y hy hxy
      have h1 := hmax _ hmem
      rw [card_insert_of_notMem hpQ] at h1
      omega
  calc P.card ≤ (Q ∪ Q.biUnion (fun q => P.filter (R q))).card := card_le_card hcov
    _ ≤ Q.card + (Q.biUnion (fun q => P.filter (R q))).card := card_union_le _ _
    _ ≤ Q.card + ∑ q ∈ Q, (P.filter (R q)).card := by gcongr; exact card_biUnion_le
    _ ≤ Q.card + ∑ _q ∈ Q, D := by gcongr with q hq; exact hD q (hQ.1 hq)
    _ = (D + 1) * Q.card := by rw [sum_const, smul_eq_mul]; ring

/-- bounded degree inside `W` gives a proportional independent subset -/
lemma ind_of_deg (W : Finset V) (D : ℕ) (hD : ∀ z ∈ W, (W.filter (G.Adj z)).card ≤ D) :
    ∃ Q ⊆ W, Ind G Q ∧ W.card ≤ (D + 1) * Q.card := by
  obtain ⟨Q, hQW, hQ, hc⟩ := greedy W (fun x y => G.Adj x y) (fun _ _ h => h.symm) D hD
  refine ⟨Q, hQW, ?_, hc⟩
  intro x hx y hy hxy
  exact hQ x hx y hy (G.ne_of_adj hxy) hxy

/-- Turán-type lower bound for the ordered edge count. -/
lemma turan_lite {a : ℕ} (ha : IndLt G a) (D : Finset V) (m : ℕ) :
    m * D.card ≤ edges G D + a * m ^ 2 := by
  set B := D.filter (fun z => (D.filter (G.Adj z)).card < m)
  have hB : B.card ≤ m * a := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have : B = ∅ := by
        ext z; simp [B]
      simp [this]
    obtain ⟨Q, hQB, hQ, hc⟩ := ind_of_deg (G := G) B (m - 1) (by
      intro z hz
      have hz' := (mem_filter.1 hz).2
      have : (B.filter (G.Adj z)).card ≤ (D.filter (G.Adj z)).card :=
        card_le_card (filter_subset_filter _ (filter_subset _ _))
      omega)
    have := ha Q hQ
    calc B.card ≤ (m - 1 + 1) * Q.card := hc
      _ ≤ m * a := by
        rw [Nat.sub_add_cancel hm]; exact Nat.mul_le_mul_left _ this.le
  have hE : m * (D \ B).card ≤ edges G D := by
    unfold edges
    calc m * (D \ B).card = ∑ _z ∈ D \ B, m := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ z ∈ D \ B, (D.filter (G.Adj z)).card := by
          gcongr with z hz
          rw [mem_sdiff] at hz
          by_contra h
          exact hz.2 (mem_filter.2 ⟨hz.1, by omega⟩)
      _ ≤ ∑ z ∈ D, (D.filter (G.Adj z)).card :=
          sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => Nat.zero_le _)
  have hsd : (D \ B).card + B.card = D.card := by
    rw [card_sdiff_add_card_eq_card (filter_subset _ _)]
  nlinarith

/-- a triangle-free set of size at most `e^2` has an independent subset of size `≥ |W|/e` -/
lemma sqrt_ind (W : Finset V) (hW : TriFree G W) (e : ℕ) (he : W.card ≤ e * e) :
    ∃ I ⊆ W, Ind G I ∧ W.card ≤ e * I.card := by
  by_cases h : ∃ z ∈ W, e ≤ (W.filter (G.Adj z)).card
  · obtain ⟨z, hz, hze⟩ := h
    refine ⟨W.filter (G.Adj z), filter_subset _ _, ?_, ?_⟩
    · intro x hx y hy hxy
      rw [mem_filter] at hx hy
      exact hW z hz x hx.1 y hy.1 hx.2 hy.2 hxy
    · calc W.card ≤ e * e := he
        _ ≤ e * (W.filter (G.Adj z)).card := Nat.mul_le_mul_left _ hze
  · push_neg at h
    rcases Nat.eq_zero_or_pos e with he0 | hepos
    · subst he0
      refine ⟨∅, empty_subset _, ind_empty, by simpa using he⟩
    obtain ⟨Q, hQW, hQ, hc⟩ := ind_of_deg (G := G) W (e - 1) (fun z hz => by
      have := h z hz; omega)
    exact ⟨Q, hQW, hQ, by rwa [Nat.sub_add_cancel hepos] at hc⟩

lemma trifree_card {a : ℕ} (ha : IndLt G a) (W : Finset V) (hW : TriFree G W) :
    W.card < a * a := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · exfalso; have := ha ∅ ind_empty; omega
  obtain ⟨Q, hQW, hQ, hc⟩ := ind_of_deg (G := G) W (a - 1) (by
    intro z hz
    have : Ind G (W.filter (G.Adj z)) := by
      intro x hx y hy hxy
      rw [mem_filter] at hx hy
      exact hW z hz x hx.1 y hy.1 hx.2 hy.2 hxy
    have := ha _ this; omega)
  have := ha Q hQ
  calc W.card ≤ (a - 1 + 1) * Q.card := hc
    _ < a * a := by rw [Nat.sub_add_cancel hpos]; exact Nat.mul_lt_mul_of_pos_left this hpos

/-- configuration lemma on 7 vertices -/
lemma seven_config (hS : Seven3 G) (f : Fin 7 → V) (hf : Function.Injective f)
    (R : Fin 7 → Fin 7 → Prop)
    (hR : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → R i j ∨ R i k ∨ R j k)
    (hadj : ∀ i j, R i j → G.Adj (f i) (f j)) : False := by
  obtain ⟨t, hts, htc, hti⟩ := hS (univ.image f) (by
    rw [card_image_of_injective _ hf]; simp)
  set t' := univ.filter (fun i => f i ∈ t) with ht'def
  have ht' : t'.image f = t := by
    ext y
    simp only [mem_image, ht'def, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hy
      obtain ⟨i, -, rfl⟩ := mem_image.1 (hts hy)
      exact ⟨i, hy, rfl⟩
  have hc : t'.card = 3 := by rw [← card_image_of_injective t' hf, ht', htc]
  obtain ⟨i, j, k, hij, hik, hjk, hijk⟩ := card_eq_three.1 hc
  have hmem : ∀ l ∈ t', f l ∈ t := fun l hl => by
    rw [ht'def, mem_filter] at hl; exact hl.2
  have hi : f i ∈ t := hmem i (by rw [hijk]; simp)
  have hj : f j ∈ t := hmem j (by rw [hijk]; simp)
  have hk : f k ∈ t := hmem k (by rw [hijk]; simp)
  rcases hR i j k hij hik hjk with h | h | h
  · exact hti _ hi _ hj (hadj _ _ h)
  · exact hti _ hi _ hk (hadj _ _ h)
  · exact hti _ hj _ hk (hadj _ _ h)

/-- a `K4` plus a disjoint triangle is impossible -/
lemma no_k4_tri (hS : Seven3 G) {p q r s x y z : V}
    (hpq : G.Adj p q) (hpr : G.Adj p r) (hps : G.Adj p s) (hqr : G.Adj q r)
    (hqs : G.Adj q s) (hrs : G.Adj r s) (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z)
    (hd : ∀ w ∈ ({p, q, r, s} : Finset V), w ≠ x ∧ w ≠ y ∧ w ≠ z) : False := by
  have h1 := hd p (by simp); have h2 := hd q (by simp)
  have h3 := hd r (by simp); have h4 := hd s (by simp)
  let f : Fin 7 → V := ![p, q, r, s, x, y, z]
  let part : Fin 7 → Fin 2 := ![0, 0, 0, 0, 1, 1, 1]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;> simp_all
  refine seven_config hS f hf (fun i j => i ≠ j ∧ part i = part j) (by decide) ?_
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [part] at hij <;> simp [f] <;>
    first | assumption | (rw [SimpleGraph.adj_comm]; assumption)

/-- the `H7` configuration (`C5` blow-up with parts `1,2,1,1,2`) is impossible -/
lemma h7 (hS : Seven3 G) (hK : K4free G) {v p q y p' q' y' : V}
    (hvp : G.Adj v p) (hvq : G.Adj v q) (hpq : G.Adj p q)
    (hvp' : G.Adj v p') (hvq' : G.Adj v q') (hp'q' : G.Adj p' q')
    (hyp : G.Adj y p) (hyq : G.Adj y q) (hy'p' : G.Adj y' p') (hy'q' : G.Adj y' q')
    (hyv : y ≠ v) (hy'v : y' ≠ v)
    (h1 : p ≠ p') (h2 : p ≠ q') (h3 : q ≠ p') (h4 : q ≠ q') : ¬ G.Adj y y' := by
  intro hyy'
  have hny : ¬ G.Adj v y := fun h => hK v p q y hvp hvq h hpq hyp.symm hyq.symm
  have hny' : ¬ G.Adj v y' := fun h => hK v p' q' y' hvp' hvq' h hp'q' hy'p'.symm hy'q'.symm
  have e1 : p ≠ y' := fun h => hny' (h ▸ hvp)
  have e2 : q ≠ y' := fun h => hny' (h ▸ hvq)
  have e3 : p' ≠ y := fun h => hny (h ▸ hvp')
  have e4 : q' ≠ y := fun h => hny (h ▸ hvq')
  let f : Fin 7 → V := ![v, p, q, y, y', p', q']
  let part : Fin 7 → Fin 5 := ![0, 1, 1, 2, 3, 4, 4]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;> simp_all
  refine seven_config hS f hf
    (fun i j => i ≠ j ∧ (part i = part j ∨ part j = part i + 1 ∨ part i = part j + 1))
    (by decide) ?_
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [part] at hij <;> simp [f] <;>
    first | assumption | (rw [SimpleGraph.adj_comm]; assumption)

/-- in a K4-free graph, the common neighbourhood of an edge is independent -/
lemma ind_common (hK : K4free G) {p q : V} (hpq : G.Adj p q) :
    Ind G ((Nb G p).filter (G.Adj q)) := by
  intro x hx y hy hxy
  simp only [mem_filter, mem_Nb] at hx hy
  exact hK p q x y hpq hx.1 hy.1 hx.2 hy.2 hxy

/-- in a K4-free graph, neighbourhoods are triangle-free -/
lemma trifree_nb (hK : K4free G) (u : V) : TriFree G (Nb G u) := by
  intro x hx y hy z hz hxy hxz hyz
  simp only [mem_Nb] at hx hy hz
  exact hK u x y z hx hy hz hxy hxz hyz

lemma TriFree.mono {A B : Finset V} (h : TriFree G B) (hAB : A ⊆ B) : TriFree G A :=
  fun x hx y hy z hz => h x (hAB hx) y (hAB hy) z (hAB hz)

end

end E813

end S_B1

-- ===== G1 =====
section S_G1

/-! Grid lemma (Bucić–Sudakov Lemma 2.6, our version with explicit parameters; original). -/

open Finset

namespace E813

noncomputable section
open Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}
variable {ρ κ : Type*}

/-- the packet structure used in the clean-up step -/
def Packet (G : SimpleGraph V) (row : V → ρ) (col : V → κ) (q β : ℕ)
    (Ru : Finset ρ) (K : Finset κ) (J : Finset V) : Prop :=
  Ind G J ∧ (∀ z ∈ J, row z ∈ Ru ∧ col z ∈ K) ∧ K.card ≤ q * Ru.card ∧
    β * Ru.card ≤ J.card

/-- clean-up: a maximal packet family -/
lemma grid_cleanup (U : Finset V) (R : Finset ρ) (row : V → ρ) (col : V → κ)
    (hedge : ∀ z ∈ U, ∀ z' ∈ U, G.Adj z z' → row z = row z' ∨ col z = col z')
    (q β : ℕ) :
    ∃ Ru ⊆ R, ∃ K ⊆ U.image col, ∃ J ⊆ U, Packet G row col q β Ru K J ∧
      ∀ r ∈ R, r ∉ Ru → ∀ Cs ⊆ U.image col, Disjoint Cs K → Cs.card ≤ q →
        ∀ J' ⊆ U, Ind G J' → (∀ z ∈ J', row z = r ∧ col z ∈ Cs) → J'.card < β := by
  set 𝒮 := ((R.powerset ×ˢ (U.image col).powerset) ×ˢ U.powerset).filter
    (fun x => Packet G row col q β x.1.1 x.1.2 x.2) with h𝒮
  have hne : 𝒮.Nonempty := ⟨((∅, ∅), ∅), by
    rw [h𝒮, mem_filter]
    refine ⟨by simp, ind_empty, by simp, by simp, by simp⟩⟩
  obtain ⟨⟨⟨Ru, K⟩, J⟩, hx, hmax⟩ := 𝒮.exists_max_image (fun x => x.1.1.card) hne
  rw [h𝒮, mem_filter] at hx
  simp only [mem_product, mem_powerset] at hx
  obtain ⟨⟨⟨hRu, hK⟩, hJ⟩, hP⟩ := hx
  refine ⟨Ru, hRu, K, hK, J, hJ, hP, ?_⟩
  intro r hr hrRu Cs hCs hdisj hCsq J' hJ'U hJ'ind hJ'
  by_contra hlt
  push_neg at hlt
  obtain ⟨hJind, hJmem, hKq, hβJ⟩ := hP
  have hdJ : Disjoint J J' := by
    rw [disjoint_left]
    intro z hz hz'
    exact hrRu ((hJ' z hz').1 ▸ (hJmem z hz).1)
  have hmem : ((insert r Ru, K ∪ Cs), J ∪ J') ∈ 𝒮 := by
    rw [h𝒮, mem_filter]
    simp only [mem_product, mem_powerset]
    refine ⟨⟨⟨insert_subset hr hRu, union_subset hK hCs⟩, union_subset hJ hJ'U⟩, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      rw [mem_union] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact hJind x hx y hy hxy
      · rcases hedge x (hJ hx) y (hJ'U hy) hxy with h | h
        · exact hrRu ((hJ' y hy).1 ▸ h ▸ (hJmem x hx).1)
        · exact disjoint_left.1 hdisj ((hJ' y hy).2) (h ▸ (hJmem x hx).2)
      · rcases hedge x (hJ'U hx) y (hJ hy) hxy with h | h
        · exact hrRu ((hJ' x hx).1 ▸ h.symm ▸ (hJmem y hy).1)
        · exact disjoint_left.1 hdisj ((hJ' x hx).2) (h.symm ▸ (hJmem y hy).2)
      · exact hJ'ind x hx y hy hxy
    · intro z hz
      rw [mem_union] at hz
      rcases hz with hz | hz
      · exact ⟨mem_insert_of_mem (hJmem z hz).1, mem_union_left _ (hJmem z hz).2⟩
      · exact ⟨by rw [(hJ' z hz).1]; exact mem_insert_self _ _, mem_union_right _ (hJ' z hz).2⟩
    · calc (K ∪ Cs).card ≤ K.card + Cs.card := card_union_le _ _
        _ ≤ q * Ru.card + q := by omega
        _ = q * (insert r Ru).card := by rw [card_insert_of_notMem hrRu]; ring
    · rw [card_insert_of_notMem hrRu, card_union_of_disjoint hdJ]
      nlinarith
  have := hmax _ hmem
  simp only at this
  rw [card_insert_of_notMem hrRu] at this
  omega

/-- The grid lemma with explicit parameters. -/
lemma grid_core {a : ℕ} (ha : IndLt G a)
    (U : Finset V) (R : Finset ρ) (row : V → ρ) (col : V → κ) (k M m sh : ℕ)
    (hrowR : ∀ z ∈ U, row z ∈ R)
    (hcell : ∀ r c, (U.filter (fun z => row z = r ∧ col z = c)).card ≤ k)
    (hrowlo : ∀ r ∈ R, m ≤ (U.filter (fun z => row z = r)).card)
    (hrowhi : ∀ r, (U.filter (fun z => row z = r)).card ≤ M)
    (hRhi : R.card ≤ sh)
    (hedge : ∀ z ∈ U, ∀ z' ∈ U, G.Adj z z' → row z = row z' ∨ col z = col z')
    (htriR : ∀ r, TriFree G (U.filter (fun z => row z = r)))
    (htriC : ∀ c, TriFree G (U.filter (fun z => col z = c)))
    (j₀ q β s₁ m₁ δ h e φ e' : ℕ)
    (hβ : a ≤ β * j₀) (hs1 : s₁ + j₀ ≤ R.card) (hm1 : m₁ + k * (q * j₀) ≤ m)
    (hh : h + 2 * a * δ ≤ s₁ * m₁) (he : M ≤ e * e) (hcol : 2 * e * a * sh * k < h * δ)
    (hφ : β ≤ q * φ) (he' : sh * φ ≤ e' * e') (hδβ : 2 * β ≤ δ)
    (hrow : 4 * M * e' * a < h * δ) : False := by
  have ha0 : 0 < a := by have := ha ∅ ind_empty; simpa using this
  obtain ⟨Ru, hRu, K, hK, J, hJ, ⟨hJind, hJmem, hKq, hβJ⟩, hpack⟩ :=
    grid_cleanup U R row col hedge q β
  have hJa := ha J hJind
  have hRuj : Ru.card < j₀ := by
    by_contra hc; push_neg at hc
    have : β * j₀ ≤ β * Ru.card := Nat.mul_le_mul_left _ hc
    omega
  -- the cleaned sub-grid
  set U' := U.filter (fun z => row z ∉ Ru ∧ col z ∉ K) with hU'
  have hU'U : U' ⊆ U := filter_subset _ _
  set R' := R \ Ru with hR'
  have hR'c : s₁ ≤ R'.card := by
    rw [hR', card_sdiff_of_subset hRu]; omega
  have hrow' : ∀ r ∈ R', m₁ ≤ (U'.filter (fun z => row z = r)).card := by
    intro r hr
    rw [hR', mem_sdiff] at hr
    have hsub : U.filter (fun z => row z = r) ⊆ U'.filter (fun z => row z = r) ∪
        K.biUnion (fun c => U.filter (fun z => row z = r ∧ col z = c)) := by
      intro z hz
      rw [mem_filter] at hz
      by_cases hc : col z ∈ K
      · exact mem_union_right _ (mem_biUnion.2 ⟨col z, hc, mem_filter.2 ⟨hz.1, hz.2, rfl⟩⟩)
      · refine mem_union_left _ (mem_filter.2 ⟨mem_filter.2 ⟨hz.1, ?_, hc⟩, hz.2⟩)
        rw [hz.2]; exact hr.2
    have h1 := card_le_card hsub
    have h2 := card_union_le (U'.filter (fun z => row z = r))
      (K.biUnion (fun c => U.filter (fun z => row z = r ∧ col z = c)))
    have h3 : (K.biUnion (fun c => U.filter (fun z => row z = r ∧ col z = c))).card ≤
        K.card * k := by
      calc _ ≤ ∑ c ∈ K, (U.filter (fun z => row z = r ∧ col z = c)).card := card_biUnion_le
        _ ≤ ∑ _c ∈ K, k := sum_le_sum (fun c _ => hcell r c)
        _ = K.card * k := by rw [sum_const, smul_eq_mul]
    have h4 : K.card * k ≤ k * (q * j₀) := by
      calc K.card * k ≤ (q * Ru.card) * k := Nat.mul_le_mul_right _ hKq
        _ ≤ (q * j₀) * k := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hRuj.le)
        _ = k * (q * j₀) := by ring
    have := hrowlo r hr.1
    omega
  have hU'c : s₁ * m₁ ≤ U'.card := by
    have hmaps : (U' : Set V).MapsTo row R := fun z hz => hrowR z (hU'U hz)
    rw [card_eq_sum_card_fiberwise hmaps]
    calc s₁ * m₁ ≤ R'.card * m₁ := Nat.mul_le_mul_right _ hR'c
      _ = ∑ _r ∈ R', m₁ := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ r ∈ R', (U'.filter (fun z => row z = r)).card := sum_le_sum hrow'
      _ ≤ ∑ r ∈ R, (U'.filter (fun z => row z = r)).card :=
          sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => Nat.zero_le _)
  -- degree dichotomy
  set deg := fun z => (U'.filter (G.Adj z)).card
  set B := U'.filter (fun z => deg z < 2 * δ)
  have hB : B.card ≤ 2 * δ * a := by
    rcases Nat.eq_zero_or_pos δ with hd | hd
    · have : B = ∅ := by ext z; simp [B, hd]
      simp [this]
    obtain ⟨Q, hQB, hQ, hc⟩ := ind_of_deg (G := G) B (2 * δ - 1) (by
      intro z hz
      have hz' := (mem_filter.1 hz).2
      have : (B.filter (G.Adj z)).card ≤ deg z :=
        card_le_card (filter_subset_filter _ (filter_subset _ _))
      omega)
    have := ha Q hQ
    calc B.card ≤ (2 * δ - 1 + 1) * Q.card := hc
      _ ≤ 2 * δ * a := by
        rw [Nat.sub_add_cancel (by omega)]; exact Nat.mul_le_mul_left _ this.le
  set H := U' \ B
  have hH : h ≤ H.card := by
    have : H.card + B.card = U'.card := card_sdiff_add_card_eq_card (filter_subset _ _)
    have : 2 * a * δ = 2 * δ * a := by ring
    omega
  set rdeg := fun z => (U'.filter (fun z' => row z' = row z ∧ G.Adj z z')).card
  set cdeg := fun z => (U'.filter (fun z' => col z' = col z ∧ G.Adj z z')).card
  have hsplit : ∀ z ∈ H, δ ≤ rdeg z ∨ δ ≤ cdeg z := by
    intro z hz
    have hz' : ¬ deg z < 2 * δ := fun h => (mem_sdiff.1 hz).2 (mem_filter.2 ⟨(mem_sdiff.1 hz).1, h⟩)
    have hzU : z ∈ U := hU'U (mem_sdiff.1 hz).1
    have hsub : U'.filter (G.Adj z) ⊆ U'.filter (fun z' => row z' = row z ∧ G.Adj z z') ∪
        U'.filter (fun z' => col z' = col z ∧ G.Adj z z') := by
      intro z' hz'
      rw [mem_filter] at hz'
      rcases hedge z hzU z' (hU'U hz'.1) hz'.2 with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨hz'.1, h.symm, hz'.2⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨hz'.1, h.symm, hz'.2⟩)
    have := (card_le_card hsub).trans (card_union_le _ _)
    simp only [deg, rdeg, cdeg] at hz' this ⊢
    omega
  set Hr := H.filter (fun z => δ ≤ rdeg z)
  set Hc := H.filter (fun z => δ ≤ cdeg z)
  have hHrc : h ≤ 2 * Hr.card ∨ h ≤ 2 * Hc.card := by
    have hsub : H ⊆ Hr ∪ Hc := by
      intro z hz
      rcases hsplit z hz with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨hz, h⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨hz, h⟩)
    have := (card_le_card hsub).trans (card_union_le _ _)
    omega
  have hHU' : H ⊆ U' := sdiff_subset
  have hh0 : 0 < h := Nat.pos_of_ne_zero (by rintro rfl; simp at hcol)
  haveI : Nonempty V := ⟨(card_pos.1 (by omega : 0 < H.card)).choose⟩
  rcases hHrc with hHr | hHc
  · ---------------- row case
    set Rws := Hr.image row
    have hzr : ∀ r ∈ Rws, ∃ z ∈ Hr, row z = r := fun r hr => mem_image.1 hr
    choose! zr hzrH hzrr using hzr
    set Jr := fun r => U'.filter (fun z' => row z' = r ∧ G.Adj (zr r) z')
    have hJr_sub : ∀ r, Jr r ⊆ U' := fun r => filter_subset _ _
    have hJr_card : ∀ r ∈ Rws, δ ≤ (Jr r).card := by
      intro r hr
      have := (mem_filter.1 (hzrH r hr)).2
      simp only [rdeg, hzrr r hr] at this
      exact this
    have hJr_ind : ∀ r ∈ Rws, Ind G (Jr r) := by
      intro r hr x hx y hy hxy
      simp only [Jr, mem_filter] at hx hy
      have hzU : zr r ∈ U := hU'U (hHU' (mem_filter.1 (hzrH r hr)).1)
      exact htriR r (zr r) (mem_filter.2 ⟨hzU, hzrr r hr⟩) x
        (mem_filter.2 ⟨hU'U hx.1, hx.2.1⟩) y (mem_filter.2 ⟨hU'U hy.1, hy.2.1⟩)
        hx.2.2 hy.2.2 hxy
    have hRwsR : ∀ r ∈ Rws, r ∈ R ∧ r ∉ Ru := by
      intro r hr
      have hz := hzrH r hr
      have hzU' := hHU' (mem_filter.1 hz).1
      have := (mem_filter.1 hzU').2.1
      rw [hzrr r hr] at this
      exact ⟨hzrr r hr ▸ hrowR _ (hU'U hzU'), this⟩
    -- |Hr| ≤ |Rws| * M
    have hHrM : Hr.card ≤ Rws.card * M := by
      have hmaps : (Hr : Set V).MapsTo row Rws := fun z hz => mem_image_of_mem _ hz
      rw [card_eq_sum_card_fiberwise hmaps]
      calc _ ≤ ∑ _r ∈ Rws, M := by
            apply sum_le_sum; intro r _
            refine le_trans (card_le_card ?_) (hrowhi r)
            intro z hz; rw [mem_filter] at hz ⊢
            exact ⟨hU'U (hHU' (mem_filter.1 hz.1).1), hz.2⟩
        _ = Rws.card * M := by rw [sum_const, smul_eq_mul]
    -- full columns
    set F := fun r => ((Jr r).image col).filter (fun c => φ ≤ ((Jr r).filter (fun z => col z = c)).card)
    have hpackr : ∀ r ∈ Rws, ∀ Cs ⊆ (Jr r).image col, Cs.card ≤ q →
        ((Jr r).filter (fun z => col z ∈ Cs)).card < β := by
      intro r hr Cs hCs hCsq
      refine hpack r (hRwsR r hr).1 (hRwsR r hr).2 Cs ?_ ?_ hCsq _ ?_ ?_ ?_
      · intro c hc
        obtain ⟨z, hz, rfl⟩ := mem_image.1 (hCs hc)
        exact mem_image_of_mem _ (hU'U (hJr_sub r hz))
      · rw [disjoint_left]
        intro c hc hcK
        obtain ⟨z, hz, rfl⟩ := mem_image.1 (hCs hc)
        exact (mem_filter.1 (hJr_sub r hz)).2.2 hcK
      · exact (filter_subset _ _).trans ((hJr_sub r).trans hU'U)
      · exact (hJr_ind r hr).mono (filter_subset _ _)
      · intro z hz
        rw [mem_filter] at hz
        exact ⟨(mem_filter.1 hz.1).2.1, hz.2⟩
    have hFq : ∀ r ∈ Rws, (F r).card < q := by
      intro r hr
      by_contra hc; push_neg at hc
      obtain ⟨Cs, hCsF, hCsc⟩ := exists_subset_card_eq hc
      have h1 := hpackr r hr Cs (hCsF.trans (filter_subset _ _)) hCsc.le
      have h2 : q * φ ≤ ((Jr r).filter (fun z => col z ∈ Cs)).card := by
        have hmaps : (((Jr r).filter (fun z => col z ∈ Cs)) : Set V).MapsTo col Cs :=
          fun z hz => (mem_filter.1 hz).2
        rw [card_eq_sum_card_fiberwise hmaps]
        calc q * φ = ∑ _c ∈ Cs, φ := by rw [sum_const, smul_eq_mul, hCsc]
          _ ≤ _ := by
            apply sum_le_sum; intro c hc
            have := (mem_filter.1 (hCsF hc)).2
            refine this.trans (card_le_card ?_)
            intro z hz; rw [mem_filter] at hz ⊢
            refine ⟨mem_filter.2 ⟨hz.1, ?_⟩, hz.2⟩
            rw [hz.2]; exact hc
      omega
    set J3 := fun r => (Jr r).filter (fun z => col z ∉ F r)
    have hJ3 : ∀ r ∈ Rws, δ ≤ 2 * (J3 r).card := by
      intro r hr
      have h1 := hpackr r hr (F r) (filter_subset _ _) (hFq r hr).le
      have h2 := card_filter_add_card_filter_not (s := Jr r) (fun z => col z ∈ F r)
      have := hJr_card r hr
      simp only [J3] at h2 ⊢
      omega
    set W := Rws.biUnion J3
    have hWc : Rws.card * δ ≤ 2 * W.card := by
      have hdisj : (Rws : Set ρ).PairwiseDisjoint J3 := by
        intro r _ r' _ hrr'
        rw [Function.onFun, disjoint_left]
        intro z hz hz'
        have h1 := (mem_filter.1 (mem_filter.1 hz).1).2.1
        have h2 := (mem_filter.1 (mem_filter.1 hz').1).2.1
        exact hrr' (h1.symm.trans h2)
      rw [card_biUnion hdisj, mul_sum]
      calc Rws.card * δ = ∑ _r ∈ Rws, δ := by rw [sum_const, smul_eq_mul]
        _ ≤ ∑ r ∈ Rws, 2 * (J3 r).card := sum_le_sum hJ3
    have hWU : W ⊆ U := by
      intro z hz
      obtain ⟨r, _, hz⟩ := mem_biUnion.1 hz
      exact hU'U (hJr_sub r (mem_filter.1 hz).1)
    have hWrow : ∀ z ∈ W, row z ∈ Rws ∧ z ∈ Jr (row z) := by
      intro z hz
      obtain ⟨r, hr, hz⟩ := mem_biUnion.1 hz
      have h1 := (mem_filter.1 (mem_filter.1 hz).1).2.1
      rw [h1]; exact ⟨hr, (mem_filter.1 hz).1⟩
    -- columns of W
    set Cl := W.image col
    have hWcol : ∀ c, (W.filter (fun z => col z = c)).card ≤ sh * φ := by
      intro c
      have hmaps : ((W.filter (fun z => col z = c)) : Set V).MapsTo row Rws :=
        fun z hz => (hWrow z (mem_filter.1 hz).1).1
      rw [card_eq_sum_card_fiberwise hmaps]
      have hRws : Rws.card ≤ sh := by
        refine le_trans (card_le_card ?_) hRhi
        intro r hr; exact (hRwsR r hr).1
      calc _ ≤ ∑ _r ∈ Rws, φ := by
            apply sum_le_sum; intro r hr
            by_cases hcF : c ∈ F r
            · have : ((W.filter (fun z => col z = c)).filter (fun z => row z = r)) = ∅ := by
                rw [eq_empty_iff_forall_notMem]
                intro z hz
                rw [mem_filter, mem_filter] at hz
                obtain ⟨⟨hzW, hzc⟩, hzr⟩ := hz
                obtain ⟨r', hr', hz'⟩ := mem_biUnion.1 hzW
                have h1 := (mem_filter.1 (mem_filter.1 hz').1).2.1
                have h2 := (mem_filter.1 hz').2
                rw [hzc] at h2
                rw [hzr] at h1; subst h1
                exact h2 hcF
              rw [this]; exact Nat.zero_le _
            · by_cases hcI : c ∈ (Jr r).image col
              · have hlt : ¬ φ ≤ ((Jr r).filter (fun z => col z = c)).card :=
                  fun h => hcF (mem_filter.2 ⟨hcI, h⟩)
                have hsub : ((W.filter (fun z => col z = c)).filter (fun z => row z = r)) ⊆
                    (Jr r).filter (fun z => col z = c) := by
                  intro z hz
                  simp only [mem_filter] at hz ⊢
                  have := (hWrow z hz.1.1).2
                  rw [hz.2] at this
                  exact ⟨this, hz.1.2⟩
                exact (card_le_card hsub).trans (Nat.le_of_lt (Nat.lt_of_not_le hlt))
              · have : ((W.filter (fun z => col z = c)).filter (fun z => row z = r)) = ∅ := by
                  rw [eq_empty_iff_forall_notMem]
                  intro z hz
                  rw [mem_filter, mem_filter] at hz
                  obtain ⟨⟨hzW, hzc⟩, hzr⟩ := hz
                  have := (hWrow z hzW).2
                  rw [hzr] at this
                  exact hcI (hzc ▸ mem_image_of_mem _ this)
                rw [this]; exact Nat.zero_le _
        _ = Rws.card * φ := by rw [sum_const, smul_eq_mul]
        _ ≤ sh * φ := Nat.mul_le_mul_right _ hRws
    have hIc : ∀ c, ∃ I ⊆ W.filter (fun z => col z = c), Ind G I ∧
        (W.filter (fun z => col z = c)).card ≤ e' * I.card := by
      intro c
      refine sqrt_ind _ ((htriC c).mono ?_) e' ((hWcol c).trans he')
      intro z hz; rw [mem_filter] at hz ⊢; exact ⟨hWU hz.1, hz.2⟩
    choose Ic hIcW hIci hIcc using hIc
    set I := Cl.biUnion Ic
    have hIind : Ind G I := by
      intro x hx y hy hxy
      obtain ⟨c, _, hxc⟩ := mem_biUnion.1 hx
      obtain ⟨c', _, hyc⟩ := mem_biUnion.1 hy
      have hx1 := mem_filter.1 (hIcW c hxc)
      have hy1 := mem_filter.1 (hIcW c' hyc)
      rcases hedge x (hWU hx1.1) y (hWU hy1.1) hxy with h | h
      · have hxJ := (hWrow x hx1.1).2
        have hyJ := (hWrow y hy1.1).2
        rw [h] at hxJ
        exact hJr_ind _ (hWrow y hy1.1).1 x hxJ y hyJ hxy
      · have : c = c' := by rw [← hx1.2, ← hy1.2, h]
        subst this
        exact hIci c x hxc y hyc hxy
    have hIa := ha I hIind
    have hWI : W.card ≤ e' * I.card := by
      have hmaps : (W : Set V).MapsTo col Cl := fun z hz => mem_image_of_mem _ hz
      have hdisj : (Cl : Set κ).PairwiseDisjoint Ic := by
        intro c _ c' _ hcc'
        rw [Function.onFun, disjoint_left]
        intro z hz hz'
        exact hcc' ((mem_filter.1 (hIcW c hz)).2.symm.trans (mem_filter.1 (hIcW c' hz')).2)
      rw [card_eq_sum_card_fiberwise hmaps, card_biUnion hdisj, mul_sum]
      exact sum_le_sum (fun c _ => hIcc c)
    have h1 : h * δ ≤ 2 * Rws.card * M * δ := by
      have := Nat.mul_le_mul_right δ (hHr.trans (Nat.mul_le_mul_left 2 hHrM))
      calc h * δ ≤ 2 * (Rws.card * M) * δ := this
        _ = 2 * Rws.card * M * δ := by ring
    have h2 : 2 * Rws.card * M * δ ≤ 4 * M * W.card := by
      have := Nat.mul_le_mul_left (2 * M) hWc
      calc 2 * Rws.card * M * δ = 2 * M * (Rws.card * δ) := by ring
        _ ≤ 2 * M * (2 * W.card) := this
        _ = 4 * M * W.card := by ring
    have h3 : 4 * M * W.card ≤ 4 * M * e' * a := by
      have : W.card ≤ e' * a := hWI.trans (Nat.mul_le_mul_left _ hIa.le)
      calc 4 * M * W.card ≤ 4 * M * (e' * a) := Nat.mul_le_mul_left _ this
        _ = 4 * M * e' * a := by ring
    omega
  · ---------------- column case
    set Cols := Hc.image col
    have hzc : ∀ c ∈ Cols, ∃ z ∈ Hc, col z = c := fun c hc => mem_image.1 hc
    choose! zc hzcH hzcc using hzc
    set Jc := fun c => U'.filter (fun z' => col z' = c ∧ G.Adj (zc c) z')
    have hJc_sub : ∀ c, Jc c ⊆ U' := fun c => filter_subset _ _
    have hJc_card : ∀ c ∈ Cols, δ ≤ (Jc c).card := by
      intro c hc
      have := (mem_filter.1 (hzcH c hc)).2
      simp only [cdeg, hzcc c hc] at this
      exact this
    have hJc_ind : ∀ c ∈ Cols, Ind G (Jc c) := by
      intro c hc x hx y hy hxy
      simp only [Jc, mem_filter] at hx hy
      have hzU : zc c ∈ U := hU'U (hHU' (mem_filter.1 (hzcH c hc)).1)
      exact htriC c (zc c) (mem_filter.2 ⟨hzU, hzcc c hc⟩) x
        (mem_filter.2 ⟨hU'U hx.1, hx.2.1⟩) y (mem_filter.2 ⟨hU'U hy.1, hy.2.1⟩)
        hx.2.2 hy.2.2 hxy
    -- |Hc| ≤ |Cols| * (sh * k)
    have hHcC : Hc.card ≤ Cols.card * (sh * k) := by
      have hmaps : (Hc : Set V).MapsTo col Cols := fun z hz => mem_image_of_mem _ hz
      rw [card_eq_sum_card_fiberwise hmaps]
      calc _ ≤ ∑ _c ∈ Cols, sh * k := by
            apply sum_le_sum; intro c _
            have hmaps' : ((Hc.filter (fun z => col z = c)) : Set V).MapsTo row R :=
              fun z hz => hrowR z (hU'U (hHU' (mem_filter.1 (mem_filter.1 hz).1).1))
            rw [card_eq_sum_card_fiberwise hmaps']
            calc _ ≤ ∑ _r ∈ R, k := by
                  apply sum_le_sum; intro r _
                  refine le_trans (card_le_card ?_) (hcell r c)
                  intro z hz
                  simp only [mem_filter] at hz ⊢
                  exact ⟨hU'U (hHU' (mem_filter.1 hz.1.1).1), hz.2, hz.1.2⟩
              _ = R.card * k := by rw [sum_const, smul_eq_mul]
              _ ≤ sh * k := Nat.mul_le_mul_right _ hRhi
        _ = Cols.card * (sh * k) := by rw [sum_const, smul_eq_mul]
    set W := Cols.biUnion Jc
    have hWc : Cols.card * δ ≤ W.card := by
      have hdisj : (Cols : Set κ).PairwiseDisjoint Jc := by
        intro c _ c' _ hcc'
        rw [Function.onFun, disjoint_left]
        intro z hz hz'
        exact hcc' ((mem_filter.1 hz).2.1.symm.trans (mem_filter.1 hz').2.1)
      rw [card_biUnion hdisj]
      calc Cols.card * δ = ∑ _c ∈ Cols, δ := by rw [sum_const, smul_eq_mul]
        _ ≤ _ := sum_le_sum hJc_card
    have hWU : W ⊆ U := by
      intro z hz
      obtain ⟨c, _, hz⟩ := mem_biUnion.1 hz
      exact hU'U (hJc_sub c hz)
    have hWcol : ∀ z ∈ W, col z ∈ Cols ∧ z ∈ Jc (col z) := by
      intro z hz
      obtain ⟨c, hc, hz⟩ := mem_biUnion.1 hz
      have h1 := (mem_filter.1 hz).2.1
      rw [h1]; exact ⟨hc, hz⟩
    have hIr : ∀ r, ∃ I ⊆ W.filter (fun z => row z = r), Ind G I ∧
        (W.filter (fun z => row z = r)).card ≤ e * I.card := by
      intro r
      refine sqrt_ind _ ((htriR r).mono ?_) e ?_
      · intro z hz; rw [mem_filter] at hz ⊢; exact ⟨hWU hz.1, hz.2⟩
      · refine le_trans (card_le_card ?_) ((hrowhi r).trans he)
        intro z hz; rw [mem_filter] at hz ⊢; exact ⟨hWU hz.1, hz.2⟩
    choose Ir hIrW hIri hIrc using hIr
    set I := R.biUnion Ir
    have hIind : Ind G I := by
      intro x hx y hy hxy
      obtain ⟨r, _, hxr⟩ := mem_biUnion.1 hx
      obtain ⟨r', _, hyr⟩ := mem_biUnion.1 hy
      have hx1 := mem_filter.1 (hIrW r hxr)
      have hy1 := mem_filter.1 (hIrW r' hyr)
      rcases hedge x (hWU hx1.1) y (hWU hy1.1) hxy with h | h
      · have : r = r' := by rw [← hx1.2, ← hy1.2, h]
        subst this
        exact hIri r x hxr y hyr hxy
      · have hxJ := (hWcol x hx1.1).2
        have hyJ := (hWcol y hy1.1).2
        rw [h] at hxJ
        exact hJc_ind _ (hWcol y hy1.1).1 x hxJ y hyJ hxy
    have hIa := ha I hIind
    have hWI : W.card ≤ e * I.card := by
      have hmaps : (W : Set V).MapsTo row R := fun z hz => hrowR z (hWU hz)
      have hdisj : (R : Set ρ).PairwiseDisjoint Ir := by
        intro r _ r' _ hrr'
        rw [Function.onFun, disjoint_left]
        intro z hz hz'
        exact hrr' ((mem_filter.1 (hIrW r hz)).2.symm.trans (mem_filter.1 (hIrW r' hz')).2)
      rw [card_eq_sum_card_fiberwise hmaps, card_biUnion hdisj, mul_sum]
      exact sum_le_sum (fun r _ => hIrc r)
    have h1 : h * δ ≤ 2 * Cols.card * (sh * k) * δ := by
      have := Nat.mul_le_mul_right δ (hHc.trans (Nat.mul_le_mul_left 2 hHcC))
      calc h * δ ≤ 2 * (Cols.card * (sh * k)) * δ := this
        _ = 2 * Cols.card * (sh * k) * δ := by ring
    have h2 : 2 * Cols.card * (sh * k) * δ ≤ 2 * (sh * k) * W.card := by
      have := Nat.mul_le_mul_left (2 * (sh * k)) hWc
      calc 2 * Cols.card * (sh * k) * δ = 2 * (sh * k) * (Cols.card * δ) := by ring
        _ ≤ _ := this
    have h3 : 2 * (sh * k) * W.card ≤ 2 * e * a * sh * k := by
      have : W.card ≤ e * a := hWI.trans (Nat.mul_le_mul_left _ hIa.le)
      calc 2 * (sh * k) * W.card ≤ 2 * (sh * k) * (e * a) := Nat.mul_le_mul_left _ this
        _ = 2 * e * a * sh * k := by ring
    omega

end

end E813

end S_G1

-- ===== O1 =====
section S_O1

/-! Out-neighbourhoods with independent-set expansion, and disjoint stars via Hall (original). -/

open Finset

namespace E813

noncomputable section
open Classical

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- vertices adjacent to some element of `X` -/
def nbr (X : Finset V) : Finset V := univ.filter (fun z => ∃ y ∈ X, G.Adj y z)

/-- admissible non-expanding sets in `N(v)` -/
def GoodX (x : ℕ) (v : V) (X : Finset V) : Prop :=
  X ⊆ Nb G v ∧ Ind G X ∧ (nbr G X ∩ Nb G v).card ≤ x * X.card

lemma exists_maxX (x : ℕ) (v : V) :
    ∃ X, GoodX G x v X ∧ ∀ X', GoodX G x v X' → X'.card ≤ X.card := by
  obtain ⟨X, hX, hmax⟩ := ((Nb G v).powerset.filter (GoodX G x v)).exists_max_image card
    ⟨∅, by simp [GoodX, ind_empty, nbr]⟩
  rw [mem_filter] at hX
  refine ⟨X, hX.2, fun X' hX' => hmax X' (mem_filter.2 ⟨mem_powerset.2 hX'.1, hX'⟩)⟩

/-- the chosen maximal non-expanding set -/
def Xv (x : ℕ) (v : V) : Finset V := (exists_maxX G x v).choose

/-- out-neighbourhood of `v` -/
def out (x : ℕ) (v : V) : Finset V :=
  (Nb G v).filter (fun z => z ∉ Xv G x v ∧ ∀ y ∈ Xv G x v, ¬ G.Adj y z)

lemma Xv_spec (x : ℕ) (v : V) : GoodX G x v (Xv G x v) ∧
    ∀ X', GoodX G x v X' → X'.card ≤ (Xv G x v).card := (exists_maxX G x v).choose_spec

variable {G}

lemma out_sub (x : ℕ) (v : V) : out G x v ⊆ Nb G v := filter_subset _ _

lemma out_adj {x : ℕ} {v z : V} (h : z ∈ out G x v) : G.Adj v z :=
  mem_Nb.1 (out_sub x v h)

lemma out_card {a : ℕ} (ha : IndLt G a) (x : ℕ) (v : V) :
    (Nb G v).card ≤ (out G x v).card + a * (x + 1) := by
  obtain ⟨⟨hXs, hXi, hXc⟩, -⟩ := Xv_spec G x v
  set X := Xv G x v
  have hXa := ha X hXi
  have hsub : Nb G v ⊆ out G x v ∪ (X ∪ (nbr G X ∩ Nb G v)) := by
    intro z hz
    by_cases h1 : z ∈ X
    · exact mem_union_right _ (mem_union_left _ h1)
    by_cases h2 : ∃ y ∈ X, G.Adj y z
    · exact mem_union_right _ (mem_union_right _ (mem_inter.2 ⟨by simp [nbr, h2], hz⟩))
    · push_neg at h2
      exact mem_union_left _ (mem_filter.2 ⟨hz, h1, h2⟩)
  calc (Nb G v).card ≤ _ := card_le_card hsub
    _ ≤ (out G x v).card + (X.card + x * X.card) := by
      refine (card_union_le _ _).trans ?_
      gcongr
      exact (card_union_le _ _).trans (by gcongr)
    _ ≤ (out G x v).card + a * (x + 1) := by
      have : X.card + x * X.card ≤ a * (x + 1) := by nlinarith
      omega

/-- expansion inside the out-neighbourhood -/
lemma out_expand (x : ℕ) (v : V) (Y : Finset V) (hY : Y ⊆ out G x v) (hYi : Ind G Y)
    (hYn : Y.Nonempty) :
    x * Y.card < ((out G x v).filter (fun z => ∃ y ∈ Y, G.Adj y z)).card := by
  obtain ⟨⟨hXs, hXi, hXc⟩, hmax⟩ := Xv_spec G x v
  set X := Xv G x v
  have hYX : ∀ y ∈ Y, y ∉ X ∧ ∀ y' ∈ X, ¬ G.Adj y' y := fun y hy => (mem_filter.1 (hY hy)).2
  have hdisj : Disjoint X Y := by
    rw [disjoint_right]; intro y hy; exact (hYX y hy).1
  by_contra hcon
  push_neg at hcon
  have hgood : GoodX G x v (X ∪ Y) := by
    refine ⟨union_subset hXs (hY.trans (out_sub x v)), ?_, ?_⟩
    · intro p hp q hq hpq
      rw [mem_union] at hp hq
      rcases hp with hp | hp <;> rcases hq with hq | hq
      · exact hXi p hp q hq hpq
      · exact (hYX q hq).2 p hp hpq
      · exact (hYX p hp).2 q hq hpq.symm
      · exact hYi p hp q hq hpq
    · have hsub : nbr G (X ∪ Y) ∩ Nb G v ⊆ (nbr G X ∩ Nb G v) ∪
          (out G x v).filter (fun z => ∃ y ∈ Y, G.Adj y z) := by
        intro z hz
        simp only [mem_inter, nbr, mem_filter, mem_univ, true_and, mem_union] at hz
        obtain ⟨⟨y, hy, hyz⟩, hzv⟩ := hz
        by_cases hzX : ∃ y' ∈ X, G.Adj y' z
        · exact mem_union_left _ (mem_inter.2 ⟨by simp [nbr, hzX], hzv⟩)
        · rcases hy with hy | hy
          · exact absurd ⟨y, hy, hyz⟩ hzX
          · push_neg at hzX
            refine mem_union_right _ (mem_filter.2 ⟨mem_filter.2 ⟨hzv, ?_, hzX⟩, y, hy, hyz⟩)
            intro hzX'
            exact (hYX y hy).2 z hzX' hyz.symm
      calc (nbr G (X ∪ Y) ∩ Nb G v).card ≤ _ := card_le_card hsub
        _ ≤ (nbr G X ∩ Nb G v).card + ((out G x v).filter (fun z => ∃ y ∈ Y, G.Adj y z)).card :=
            card_union_le _ _
        _ ≤ x * X.card + x * Y.card := add_le_add hXc hcon
        _ = x * (X ∪ Y).card := by rw [card_union_of_disjoint hdisj]; ring
  have := hmax _ hgood
  rw [card_union_of_disjoint hdisj] at this
  have := hYn.card_pos
  omega

/-- Hall: disjoint `k`-sets inside prescribed sets -/
lemma hall_stars (Y0 : Finset V) (Nf : V → Finset V) (k : ℕ)
    (hcond : ∀ Y ⊆ Y0, k * Y.card ≤ (Y.biUnion Nf).card) :
    ∃ E : V → Finset V, (∀ w ∈ Y0, E w ⊆ Nf w ∧ (E w).card = k) ∧
      ∀ w ∈ Y0, ∀ w' ∈ Y0, w ≠ w' → Disjoint (E w) (E w') := by
  let ι := {p : V × Fin k // p.1 ∈ Y0}
  let t : ι → Finset V := fun i => Nf i.1.1
  have hH : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card := by
    intro s
    set Y := s.image (fun i => i.1.1)
    have hY : Y ⊆ Y0 := by
      intro w hw; obtain ⟨i, _, rfl⟩ := mem_image.1 hw; exact i.2
    have h1 : s.card ≤ k * Y.card := by
      have : (s.map (Function.Embedding.subtype _)) ⊆ Y ×ˢ (univ : Finset (Fin k)) := by
        intro p hp
        obtain ⟨i, hi, rfl⟩ := mem_map.1 hp
        exact mem_product.2 ⟨mem_image_of_mem _ hi, mem_univ _⟩
      have := card_le_card this
      rw [card_map, card_product, card_univ, Fintype.card_fin] at this
      linarith
    have h2 : s.biUnion t = Y.biUnion Nf := by
      ext z
      simp only [mem_biUnion, Y, mem_image, t]
      constructor
      · rintro ⟨i, hi, hz⟩; exact ⟨i.1.1, ⟨i, hi, rfl⟩, hz⟩
      · rintro ⟨w, ⟨i, hi, rfl⟩, hz⟩; exact ⟨i, hi, hz⟩
    rw [h2]
    exact h1.trans (hcond Y hY)
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hH
  refine ⟨fun w => if hw : w ∈ Y0 then univ.image (fun j : Fin k => f ⟨(w, j), hw⟩) else ∅,
    ?_, ?_⟩
  · intro w hw
    dsimp only
    rw [dif_pos hw]
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨j, _, rfl⟩ := mem_image.1 hz
      exact hft _
    · rw [card_image_of_injective, card_univ, Fintype.card_fin]
      intro j j' hjj'
      have := congrArg (fun i : ι => i.1.2) (hfinj hjj')
      exact this
  · intro w hw w' hw' hne
    dsimp only
    rw [dif_pos hw, dif_pos hw', disjoint_left]
    intro z hz hz'
    obtain ⟨j, _, rfl⟩ := mem_image.1 hz
    obtain ⟨j', _, hj'⟩ := mem_image.1 hz'
    have := congrArg (fun i : ι => i.1.1) (hfinj hj')
    exact hne this.symm

end

end E813

end S_O1

-- ===== P1 =====
section S_P1

/-! The L / C / I partition of `v`-extending vertices, with centres (original). -/

open Finset

namespace E813

noncomputable section
open Classical

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- ordered `v`-triangle edges through `z` -/
def tri (v z : V) : Finset (V × V) :=
  ((Nb G v) ×ˢ (Nb G v)).filter (fun e => G.Adj e.1 e.2 ∧ G.Adj e.1 z ∧ G.Adj e.2 z)

def Ext (v z : V) : Prop := z ≠ v ∧ ¬ G.Adj v z

def isH (v z : V) : Prop := Ext G v z ∧ 9 ≤ (tri G v z).card

def isL (v z : V) : Prop := (tri G v z).card ≤ 8

def isC (v z : V) : Prop := isH G v z ∧ ∃ z', G.Adj z z' ∧ isH G v z'

def isI (v z : V) : Prop := isH G v z ∧ ¬ ∃ z', G.Adj z z' ∧ isH G v z'

/-- `e` contains `c` -/
def Cont (e : V × V) (c : V) : Prop := e.1 = c ∨ e.2 = c

def Meets (e e' : V × V) : Prop := ∃ w, Cont e w ∧ Cont e' w

def cen (v z : V) : V :=
  if h : ∃ c, ∀ e ∈ tri G v z, Cont e c then h.choose else v

variable {G}

lemma mem_tri {v z : V} {e : V × V} : e ∈ tri G v z ↔
    G.Adj v e.1 ∧ G.Adj v e.2 ∧ G.Adj e.1 e.2 ∧ G.Adj e.1 z ∧ G.Adj e.2 z := by
  simp [tri, and_assoc]

lemma ext_of_tri (hK : K4free G) {v z : V} {e : V × V} (he : e ∈ tri G v z) (hz : z ≠ v) :
    Ext G v z := by
  rw [mem_tri] at he
  exact ⟨hz, fun h => hK v e.1 e.2 z he.1 he.2.1 h he.2.2.1 he.2.2.2.1 he.2.2.2.2⟩

lemma part_cases (v z : V) (hz : Ext G v z) : isL G v z ∨ isC G v z ∨ isI G v z := by
  by_cases h : (tri G v z).card ≤ 8
  · exact Or.inl h
  · have hH : isH G v z := ⟨hz, by omega⟩
    by_cases h' : ∃ z', G.Adj z z' ∧ isH G v z'
    · exact Or.inr (Or.inl ⟨hH, h'⟩)
    · exact Or.inr (Or.inr ⟨hH, h'⟩)

lemma I_ind {v z z' : V} (hz : isI G v z) (hz' : isI G v z') : ¬ G.Adj z z' :=
  fun h => hz.2 ⟨z', h, hz'.1⟩

lemma not_C_and_I {v z : V} (hC : isC G v z) (hI : isI G v z) : False := hI.2 hC.2

lemma not_L_and_H {v z : V} (hL : isL G v z) (hH : isH G v z) : False := by
  unfold isL at hL; have := hH.2; omega

/-- edges of `v`-triangles at adjacent extending vertices meet (`H7`) -/
lemma tri_meets (hS : Seven3 G) (hK : K4free G) {v z z' : V} (hz : Ext G v z)
    (hz' : Ext G v z') (hzz' : G.Adj z z') {e e' : V × V} (he : e ∈ tri G v z)
    (he' : e' ∈ tri G v z') : Meets e e' := by
  rw [mem_tri] at he he'
  by_contra hm
  have h1 : e.1 ≠ e'.1 := fun h => hm ⟨e.1, Or.inl rfl, Or.inl h.symm⟩
  have h2 : e.1 ≠ e'.2 := fun h => hm ⟨e.1, Or.inl rfl, Or.inr h.symm⟩
  have h3 : e.2 ≠ e'.1 := fun h => hm ⟨e.2, Or.inr rfl, Or.inl h.symm⟩
  have h4 : e.2 ≠ e'.2 := fun h => hm ⟨e.2, Or.inr rfl, Or.inr h.symm⟩
  exact h7 hS hK he.1 he.2.1 he.2.2.1 he'.1 he'.2.1 he'.2.2.1 he.2.2.2.1.symm
    he.2.2.2.2.symm he'.2.2.2.1.symm he'.2.2.2.2.symm hz.1 hz'.1 h1 h2 h3 h4 hzz'

/-- inside `tri z` no two edges are disjoint, if `z` has an adjacent high vertex -/
lemma tri_self_meets (hS : Seven3 G) (hK : K4free G) {v z z' : V} (hz : Ext G v z)
    (hz' : isH G v z') (hzz' : G.Adj z z') {e1 e2 : V × V} (he1 : e1 ∈ tri G v z)
    (he2 : e2 ∈ tri G v z) : Meets e1 e2 := by
  by_contra hm
  have hsub : tri G v z' ⊆ ({e1.1, e1.2} ×ˢ {e2.1, e2.2}) ∪ ({e2.1, e2.2} ×ˢ {e1.1, e1.2}) := by
    intro e he
    have hadj : e.1 ≠ e.2 := G.ne_of_adj (mem_tri.1 he).2.2.1
    obtain ⟨w1, hw1, hw1'⟩ := tri_meets hS hK hz hz'.1 hzz' he1 he
    obtain ⟨w2, hw2, hw2'⟩ := tri_meets hS hK hz hz'.1 hzz' he2 he
    have hne : w1 ≠ w2 := by
      rintro rfl; exact hm ⟨w1, hw1, hw2⟩
    simp only [Cont] at hw1 hw2 hw1' hw2'
    simp only [mem_union, mem_product, mem_insert, mem_singleton]
    rcases hw1' with h | h <;> rcases hw2' with h' | h'
    · exact absurd (h.symm.trans h') hne
    · left; exact ⟨by rcases hw1 with h1 | h1 <;> [left; right] <;> rw [h, h1],
        by rcases hw2 with h2 | h2 <;> [left; right] <;> rw [h', h2]⟩
    · right; exact ⟨by rcases hw2 with h2 | h2 <;> [left; right] <;> rw [h', h2],
        by rcases hw1 with h1 | h1 <;> [left; right] <;> rw [h, h1]⟩
    · exact absurd (h.symm.trans h') hne
  have h1 := card_le_card hsub
  have h2 := card_union_le ({e1.1, e1.2} ×ˢ {e2.1, e2.2} : Finset (V × V))
    ({e2.1, e2.2} ×ˢ {e1.1, e1.2})
  rw [card_product, card_product] at h2
  have c1 : ({e1.1, e1.2} : Finset V).card ≤ 2 := card_le_two
  have c2 : ({e2.1, e2.2} : Finset V).card ≤ 2 := card_le_two
  have := hz'.2
  nlinarith

/-- a pairwise meeting family of edges in `N(v)` is a star -/
lemma star_of_meets (hK : K4free G) {v : V} (F : Finset (V × V))
    (hF : ∀ e ∈ F, G.Adj v e.1 ∧ G.Adj v e.2 ∧ G.Adj e.1 e.2)
    (hm : ∀ e ∈ F, ∀ e' ∈ F, Meets e e') {e0 : V × V} (he0 : e0 ∈ F) :
    ∃ c, ∀ e ∈ F, Cont e c := by
  by_contra hc
  push_neg at hc
  obtain ⟨e1, he1, h1⟩ := hc e0.1
  obtain ⟨e2, he2, h2⟩ := hc e0.2
  simp only [Cont, not_or] at h1 h2
  -- e1 contains e0.2, e2 contains e0.1
  have hb : ∃ c1, G.Adj e0.2 c1 ∧ G.Adj v c1 ∧ c1 ≠ e0.1 ∧ ∀ w, Cont e1 w → w = e0.2 ∨ w = c1 := by
    obtain ⟨w, hw, hw'⟩ := hm e1 he1 e0 he0
    simp only [Cont] at hw hw'
    have hw2 : w = e0.2 := by
      rcases hw' with h | h
      · rcases hw with h' | h' <;> [exact absurd (h'.trans h.symm) h1.1;
          exact absurd (h'.trans h.symm) h1.2]
      · exact h.symm
    subst hw2
    obtain ⟨ha1, ha2, ha3⟩ := hF e1 he1
    rcases hw with h | h
    · refine ⟨e1.2, h ▸ ha3, ha2, h1.2, fun w hw => ?_⟩
      rcases hw with hw | hw <;> [left; right] <;> [exact (h ▸ hw).symm ▸ rfl; exact hw.symm]
    · refine ⟨e1.1, h ▸ ha3.symm, ha1, h1.1, fun w hw => ?_⟩
      rcases hw with hw | hw <;> [right; left] <;> [exact hw.symm; exact (h ▸ hw).symm ▸ rfl]
  have ha : ∃ c2, G.Adj e0.1 c2 ∧ c2 ≠ e0.2 ∧ ∀ w, Cont e2 w → w = e0.1 ∨ w = c2 := by
    obtain ⟨w, hw, hw'⟩ := hm e2 he2 e0 he0
    simp only [Cont] at hw hw'
    have hw2 : w = e0.1 := by
      rcases hw' with h | h
      · exact h.symm
      · rcases hw with h' | h' <;> [exact absurd (h'.trans h.symm) h2.1;
          exact absurd (h'.trans h.symm) h2.2]
    subst hw2
    obtain ⟨ha1, ha2, ha3⟩ := hF e2 he2
    rcases hw with h | h
    · refine ⟨e2.2, h ▸ ha3, h2.2, fun w hw => ?_⟩
      rcases hw with hw | hw <;> [left; right] <;> [exact (h ▸ hw).symm ▸ rfl; exact hw.symm]
    · refine ⟨e2.1, h ▸ ha3.symm, h2.1, fun w hw => ?_⟩
      rcases hw with hw | hw <;> [right; left] <;> [exact hw.symm; exact (h ▸ hw).symm ▸ rfl]
  obtain ⟨c1, hbc1, hvc1, hc1a, hc1⟩ := hb
  obtain ⟨c2, hac2, hc2b, hc2⟩ := ha
  obtain ⟨w, hw1, hw2⟩ := hm e1 he1 e2 he2
  have hab := (hF e0 he0).2.2
  rcases hc1 w hw1 with h | h <;> rcases hc2 w hw2 with h' | h'
  · exact G.ne_of_adj hab (h'.symm.trans h)
  · exact hc2b (h'.symm.trans h)
  · exact hc1a (h.symm.trans h')
  · have hc : c1 = c2 := h.symm.trans h'
    subst hc
    exact hK v e0.1 e0.2 c1 (hF e0 he0).1 (hF e0 he0).2.1 hvc1 hab hac2 hbc1

/-- a star centre is unique when there are at least 3 ordered edges -/
lemma centre_unique {v z : V} {c c' : V} (h3 : 3 ≤ (tri G v z).card)
    (hc : ∀ e ∈ tri G v z, Cont e c) (hc' : ∀ e ∈ tri G v z, Cont e c') : c = c' := by
  by_contra hne
  have hsub : tri G v z ⊆ {(c, c'), (c', c)} := by
    intro e he
    have hadj : e.1 ≠ e.2 := G.ne_of_adj (mem_tri.1 he).2.2.1
    have h1 := hc e he
    have h2 := hc' e he
    simp only [Cont] at h1 h2
    simp only [mem_insert, mem_singleton]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.symm.trans h2) hne
    · left; exact Prod.ext h1 h2
    · right; exact Prod.ext h2 h1
    · exact absurd (h1.symm.trans h2) hne
  have := (card_le_card hsub).trans card_le_two
  omega

/-- centres of adjacent high vertices -/
lemma cen_spec (hS : Seven3 G) (hK : K4free G) {v z z' : V} (hz : isH G v z)
    (hz' : isH G v z') (hzz' : G.Adj z z') :
    (∀ e ∈ tri G v z, Cont e (cen G v z)) ∧ cen G v z = cen G v z' := by
  set F := tri G v z ∪ tri G v z'
  have hF : ∀ e ∈ F, G.Adj v e.1 ∧ G.Adj v e.2 ∧ G.Adj e.1 e.2 := by
    intro e he
    rcases mem_union.1 he with he | he <;>
      exact ⟨(mem_tri.1 he).1, (mem_tri.1 he).2.1, (mem_tri.1 he).2.2.1⟩
  have hm : ∀ e ∈ F, ∀ e' ∈ F, Meets e e' := by
    intro e he e' he'
    rcases mem_union.1 he with he | he <;> rcases mem_union.1 he' with he' | he'
    · exact tri_self_meets hS hK hz.1 hz' hzz' he he'
    · exact tri_meets hS hK hz.1 hz'.1 hzz' he he'
    · obtain ⟨w, h1, h2⟩ := tri_meets hS hK hz.1 hz'.1 hzz' he' he; exact ⟨w, h2, h1⟩
    · exact tri_self_meets hS hK hz'.1 hz hzz'.symm he he'
  have hne : (tri G v z).Nonempty := card_pos.1 (by have := hz.2; omega)
  obtain ⟨e0, he0⟩ := hne
  obtain ⟨c, hc⟩ := star_of_meets hK F hF hm (mem_union_left _ he0)
  have hcz : ∀ e ∈ tri G v z, Cont e c := fun e he => hc e (mem_union_left _ he)
  have hcz' : ∀ e ∈ tri G v z', Cont e c := fun e he => hc e (mem_union_right _ he)
  have hex : ∃ c, ∀ e ∈ tri G v z, Cont e c := ⟨c, hcz⟩
  have hex' : ∃ c, ∀ e ∈ tri G v z', Cont e c := ⟨c, hcz'⟩
  have e1 : cen G v z = hex.choose := by unfold cen; rw [dif_pos hex]
  have e2 : cen G v z' = hex'.choose := by unfold cen; rw [dif_pos hex']
  have u1 : hex.choose = c := centre_unique (by have := hz.2; omega) hex.choose_spec hcz
  have u2 : hex'.choose = c := centre_unique (by have := hz'.2; omega) hex'.choose_spec hcz'
  refine ⟨?_, by rw [e1, e2, u1, u2]⟩
  rw [e1]; exact hex.choose_spec

lemma C_cont (hS : Seven3 G) (hK : K4free G) {v z : V} (hz : isC G v z) {e : V × V}
    (he : e ∈ tri G v z) : Cont e (cen G v z) := by
  obtain ⟨z', hzz', hz'⟩ := hz.2
  exact (cen_spec hS hK hz.1 hz' hzz').1 e he

lemma C_cen_eq (hS : Seven3 G) (hK : K4free G) {v z z' : V} (hz : isC G v z)
    (hz' : isC G v z') (hzz' : G.Adj z z') : cen G v z = cen G v z' :=
  (cen_spec hS hK hz.1 hz'.1 hzz').2

end

end E813

end S_P1

-- ===== S1 =====
section S_S1

/-! Star lemma: set-up and the matching regime (original). -/

open Finset

namespace E813

noncomputable section
open Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- data of a star at `v`: leaves `S`, sinks `T u`, disjoint extending sets `E u w` -/
structure Star (G : SimpleGraph V) (out : V → Finset V) (v : V) (S : Finset V)
    (T : V → Finset V) (E : V → V → Finset V) (t k : ℕ) : Prop where
  out_nb : ∀ u, out u ⊆ Nb G u
  S_nb : S ⊆ Nb G v
  T_out : ∀ u ∈ S, T u ⊆ out u
  T_nb : ∀ u ∈ S, T u ⊆ Nb G v
  T_card : ∀ u ∈ S, (T u).card = t
  E_out : ∀ u ∈ S, ∀ w ∈ T u, E u w ⊆ out u
  E_nb : ∀ u ∈ S, ∀ w ∈ T u, E u w ⊆ Nb G w
  E_v : ∀ u ∈ S, ∀ w ∈ T u, v ∉ E u w
  E_card : ∀ u ∈ S, ∀ w ∈ T u, (E u w).card = k
  E_disj : ∀ u ∈ S, ∀ w ∈ T u, ∀ w' ∈ T u, w ≠ w' → Disjoint (E u w) (E u w')

/-- leaf/sink pairs -/
def pairs (S : Finset V) (T : V → Finset V) : Finset (V × V) :=
  (S ×ˢ univ).filter (fun e => e.2 ∈ T e.1)

lemma mem_pairs {S : Finset V} {T : V → Finset V} {e : V × V} :
    e ∈ pairs S T ↔ e.1 ∈ S ∧ e.2 ∈ T e.1 := by
  simp [pairs]

lemma sum_pairs {β : Type*} [AddCommMonoid β] (S : Finset V) (T : V → Finset V)
    (f : V × V → β) : ∑ e ∈ pairs S T, f e = ∑ u ∈ S, ∑ w ∈ T u, f (u, w) := by
  rw [pairs, sum_filter, sum_product]
  refine sum_congr rfl (fun u _ => ?_)
  rw [← sum_filter]
  congr 1
  ext w; simp

/-- sum of the I-parts of out-neighbourhoods of leaves -/
def SI (G : SimpleGraph V) (out : V → Finset V) (v : V) (S : Finset V) : ℕ :=
  ∑ u ∈ S, ((out u).filter (isI G v)).card

section
variable {out : V → Finset V} {v : V} {S : Finset V} {T : V → Finset V}
  {E : V → V → Finset V} {t k : ℕ}

lemma Star.facts (h : Star G out v S T E t k) {u w z : V} (hu : u ∈ S) (hw : w ∈ T u)
    (hz : z ∈ E u w) :
    G.Adj v u ∧ G.Adj v w ∧ G.Adj u w ∧ G.Adj u z ∧ G.Adj w z ∧ z ≠ v := by
  refine ⟨mem_Nb.1 (h.S_nb hu), mem_Nb.1 (h.T_nb u hu hw),
    mem_Nb.1 (h.out_nb u (h.T_out u hu hw)), mem_Nb.1 (h.out_nb u (h.E_out u hu w hw hz)),
    mem_Nb.1 (h.E_nb u hu w hw hz), ?_⟩
  rintro rfl; exact h.E_v u hu w hw hz

lemma Star.tri_mem (h : Star G out v S T E t k) {u w z : V} (hu : u ∈ S) (hw : w ∈ T u)
    (hz : z ∈ E u w) : (u, w) ∈ tri G v z := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := h.facts hu hw hz
  rw [mem_tri]; exact ⟨h1, h2, h3, h4, h5⟩

lemma Star.ext (h : Star G out v S T E t k) (hK : K4free G) {u w z : V} (hu : u ∈ S)
    (hw : w ∈ T u) (hz : z ∈ E u w) : Ext G v z :=
  ext_of_tri hK (h.tri_mem hu hw hz) (h.facts hu hw hz).2.2.2.2.2

lemma Star.T_ind (h : Star G out v S T E t k) (hK : K4free G) {u : V} (hu : u ∈ S) :
    Ind G (T u) := by
  refine (ind_common hK (mem_Nb.1 (h.S_nb hu))).mono ?_
  intro w hw
  exact mem_filter.2 ⟨h.T_nb u hu hw, mem_Nb.1 (h.out_nb u (h.T_out u hu hw))⟩

lemma Star.t_lt (h : Star G out v S T E t k) (hK : K4free G) {a : ℕ} (ha : IndLt G a)
    {u : V} (hu : u ∈ S) : t < a := by
  rw [← h.T_card u hu]; exact ha _ (h.T_ind hK hu)

lemma Star.card_pairs (h : Star G out v S T E t k) : (pairs S T).card = S.card * t := by
  rw [card_eq_sum_ones, sum_pairs]
  simp only [sum_const, smul_eq_mul, mul_one]
  rw [sum_congr rfl (fun u hu => h.T_card u hu), sum_const, smul_eq_mul]

lemma Star.sumI_le (h : Star G out v S T E t k) :
    ∑ u ∈ S, ∑ w ∈ T u, ((E u w).filter (isI G v)).card ≤ SI G out v S := by
  unfold SI
  refine sum_le_sum (fun u hu => ?_)
  have hdisj : ((T u : Set V)).PairwiseDisjoint (fun w => (E u w).filter (isI G v)) := by
    intro w hw w' hw' hne
    exact disjoint_filter_filter (h.E_disj u hu w hw w' hw' hne)
  rw [← card_biUnion hdisj]
  refine card_le_card ?_
  intro z hz
  obtain ⟨w, hw, hz⟩ := mem_biUnion.1 hz
  rw [mem_filter] at hz ⊢
  exact ⟨h.E_out u hu w hw hz.1, hz.2⟩

end

/-- double counting with multiplicities -/
lemma sum_card_eq {β : Type*} (Q : Finset β) (A : β → Finset V) :
    ∑ e ∈ Q, (A e).card = ∑ z ∈ Q.biUnion A, (Q.filter (fun e => z ∈ A e)).card := by
  have h1 : ∀ e ∈ Q, (A e).card = ∑ z ∈ Q.biUnion A, if z ∈ A e then 1 else 0 := by
    intro e he
    rw [← card_filter]
    congr 1
    ext z
    simp only [mem_filter, mem_biUnion]
    exact ⟨fun hz => ⟨⟨e, he, hz⟩, hz⟩, fun hz => hz.2⟩
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl (fun z _ => ?_)
  rw [card_filter]

/-- Star lemma, matching regime -/
lemma starA (hS7 : Seven3 G) (hK : K4free G) {a : ℕ} (ha : IndLt G a)
    {out : V → Finset V} {v : V} {S : Finset V} {T : V → Finset V}
    {E : V → V → Finset V} {t k : ℕ} (h : Star G out v S T E t k)
    (hA : 210 * a * a ≤ S.card * t * k) : S.card * t * k ≤ 9 * SI G out v S := by
  have ha0 : 0 < a := by have := ha ∅ ind_empty; simpa using this
  by_contra hlt
  push_neg at hlt
  set P0 := pairs S T
  set g := fun e : V × V => ((E e.1 e.2).filter (fun z => ¬ isI G v z)).card
  set i := fun e : V × V => ((E e.1 e.2).filter (isI G v)).card
  have hgi : ∀ e ∈ P0, g e + i e = k := by
    intro e he
    rw [mem_pairs] at he
    simp only [g, i]
    rw [add_comm, card_filter_add_card_filter_not, h.E_card _ he.1 _ he.2]
  have hsumi : ∑ e ∈ P0, i e ≤ SI G out v S := by
    rw [sum_pairs]; exact h.sumI_le
  have hsumgi : ∑ e ∈ P0, g e + ∑ e ∈ P0, i e = S.card * t * k := by
    rw [← sum_add_distrib, sum_congr rfl hgi, sum_const, smul_eq_mul, h.card_pairs]
  set P := P0.filter (fun e => k ≤ 2 * g e)
  have hmark : 2 * ∑ e ∈ P0, g e ≤ 2 * k * P.card + k * P0.card := by
    rw [← sum_filter_add_sum_filter_not P0 (fun e => k ≤ 2 * g e), mul_add]
    change 2 * ∑ e ∈ P, g e + 2 * ∑ e ∈ P0.filter (fun e => ¬ k ≤ 2 * g e), g e ≤ _
    have h1 : 2 * ∑ e ∈ P, g e ≤ 2 * k * P.card := by
      rw [mul_sum]
      calc ∑ e ∈ P, 2 * g e ≤ ∑ _e ∈ P, 2 * k := by
            apply sum_le_sum; intro e he
            have he' := (mem_filter.1 he).1
            have := hgi e he'
            omega
        _ = 2 * k * P.card := by rw [sum_const, smul_eq_mul]; ring
    have h2 : 2 * ∑ e ∈ P0.filter (fun e => ¬ k ≤ 2 * g e), g e ≤ k * P0.card := by
      rw [mul_sum]
      calc ∑ e ∈ P0.filter (fun e => ¬ k ≤ 2 * g e), 2 * g e
          ≤ ∑ _e ∈ P0.filter (fun e => ¬ k ≤ 2 * g e), k := by
            apply sum_le_sum; intro e he
            have := (mem_filter.1 he).2; omega
        _ ≤ ∑ _e ∈ P0, k := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _)
        _ = k * P0.card := by rw [sum_const, smul_eq_mul]; ring
    omega
  have hP : 7 * (S.card * t * k) < 18 * (k * P.card) := by
    rw [h.card_pairs] at hmark
    have : k * (S.card * t) = S.card * t * k := by ring
    nlinarith
  -- conflict degrees
  have hdeg : ∀ e ∈ P, (P.filter (Meets e)).card ≤ 4 * a := by
    intro e he
    have he0 := (mem_filter.1 he).1
    rw [mem_pairs] at he0
    have hA1 : ∀ c, (P0.filter (fun e' => e'.1 = c)).card ≤ a := by
      intro c
      by_cases hc : c ∈ S
      · have : (P0.filter (fun e' => e'.1 = c)) ⊆ (T c).image (fun w => (c, w)) := by
          intro e' he'
          rw [mem_filter, mem_pairs] at he'
          refine mem_image.2 ⟨e'.2, he'.2 ▸ he'.1.2, ?_⟩
          rw [← he'.2]
        exact (card_le_card this).trans (card_image_le.trans
          (by rw [h.T_card c hc]; exact (h.t_lt hK ha hc).le))
      · have : (P0.filter (fun e' => e'.1 = c)) = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro e' he'
          rw [mem_filter, mem_pairs] at he'
          exact hc (he'.2 ▸ he'.1.1)
        rw [this]; exact Nat.zero_le _
    have hA2 : ∀ c, (P0.filter (fun e' => e'.2 = c)).card ≤ a := by
      intro c
      by_cases hne : (P0.filter (fun e' => e'.2 = c)).Nonempty
      · obtain ⟨e1, he1⟩ := hne
        rw [mem_filter, mem_pairs] at he1
        have hvc : G.Adj v c := mem_Nb.1 (h.T_nb _ he1.1.1 (he1.2 ▸ he1.1.2))
        have hsub : (P0.filter (fun e' => e'.2 = c)).image Prod.fst ⊆
            (Nb G v).filter (G.Adj c) := by
          intro u hu
          obtain ⟨e', he', rfl⟩ := mem_image.1 hu
          rw [mem_filter, mem_pairs] at he'
          refine mem_filter.2 ⟨h.S_nb he'.1.1, ?_⟩
          have := mem_Nb.1 (h.out_nb _ (h.T_out _ he'.1.1 he'.1.2))
          rw [he'.2] at this
          exact this.symm
        have hinj : Set.InjOn Prod.fst ((P0.filter (fun e' => e'.2 = c)) : Set (V × V)) := by
          intro x hx y hy hxy
          have hx' := (mem_filter.1 hx).2
          have hy' := (mem_filter.1 hy).2
          exact Prod.ext hxy (hx'.trans hy'.symm)
        rw [← card_image_of_injOn hinj]
        exact (card_le_card hsub).trans (ha _ (ind_common hK hvc)).le
      · rw [not_nonempty_iff_eq_empty.1 hne]; exact Nat.zero_le _
    have hsub : P.filter (Meets e) ⊆ ((P0.filter (fun e' => e'.1 = e.1) ∪
        P0.filter (fun e' => e'.1 = e.2)) ∪ (P0.filter (fun e' => e'.2 = e.1) ∪
        P0.filter (fun e' => e'.2 = e.2))) := by
      intro e' he'
      rw [mem_filter] at he'
      have he'0 := (mem_filter.1 he'.1).1
      obtain ⟨w, hw, hw'⟩ := he'.2
      simp only [Cont] at hw hw'
      simp only [mem_union, mem_filter]
      rcases hw with rfl | rfl <;> rcases hw' with h' | h'
      · exact Or.inl (Or.inl ⟨he'0, h'⟩)
      · exact Or.inr (Or.inl ⟨he'0, h'⟩)
      · exact Or.inl (Or.inr ⟨he'0, h'⟩)
      · exact Or.inr (Or.inr ⟨he'0, h'⟩)
    refine (card_le_card hsub).trans ?_
    refine (card_union_le _ _).trans ?_
    have := card_union_le (P0.filter (fun e' => e'.1 = e.1)) (P0.filter (fun e' => e'.1 = e.2))
    have := card_union_le (P0.filter (fun e' => e'.2 = e.1)) (P0.filter (fun e' => e'.2 = e.2))
    have := hA1 e.1; have := hA1 e.2; have := hA2 e.1; have := hA2 e.2
    omega
  have hsymm : ∀ e e' : V × V, Meets e e' → Meets e' e := by
    rintro e e' ⟨w, h1, h2⟩; exact ⟨w, h2, h1⟩
  obtain ⟨Q, hQP, hQ, hPQ⟩ := greedy P Meets hsymm (4 * a) hdeg
  have hQP0 : ∀ e ∈ Q, e.1 ∈ S ∧ e.2 ∈ T e.1 := fun e he =>
    mem_pairs.1 (mem_filter.1 (hQP he)).1
  set A := fun e : V × V => (E e.1 e.2).filter (fun z => ¬ isI G v z)
  set J := Q.biUnion A
  have hJind : Ind G J := by
    intro z hz z' hz' hzz'
    obtain ⟨e, he, hze⟩ := mem_biUnion.1 hz
    obtain ⟨e', he', hze'⟩ := mem_biUnion.1 hz'
    have hze1 := (mem_filter.1 hze).1
    have hze1' := (mem_filter.1 hze').1
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.facts (hQP0 e he).1 (hQP0 e he).2 hze1
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h.facts (hQP0 e' he').1 (hQP0 e' he').2 hze1'
    by_cases hee : e = e'
    · subst hee
      exact hK e.1 e.2 z z' a3 a4 b4 a5 b5 hzz'
    · have hnm := hQ e he e' he' hee
      have n1 : e.1 ≠ e'.1 := fun h => hnm ⟨e.1, Or.inl rfl, Or.inl h.symm⟩
      have n2 : e.1 ≠ e'.2 := fun h => hnm ⟨e.1, Or.inl rfl, Or.inr h.symm⟩
      have n3 : e.2 ≠ e'.1 := fun h => hnm ⟨e.2, Or.inr rfl, Or.inl h.symm⟩
      have n4 : e.2 ≠ e'.2 := fun h => hnm ⟨e.2, Or.inr rfl, Or.inr h.symm⟩
      exact h7 hS7 hK a1 a2 a3 b1 b2 b3 a4.symm a5.symm b4.symm b5.symm a6 b6 n1 n2 n3 n4 hzz'
  have hJa := ha J hJind
  have hmult : ∀ z ∈ J, (Q.filter (fun e => z ∈ A e)).card ≤ 8 := by
    intro z hz
    obtain ⟨e0, he0, hze0⟩ := mem_biUnion.1 hz
    have hext := h.ext hK (hQP0 e0 he0).1 (hQP0 e0 he0).2 (mem_filter.1 hze0).1
    have hnI := (mem_filter.1 hze0).2
    have hsubt : Q.filter (fun e => z ∈ A e) ⊆ tri G v z := by
      intro e he
      rw [mem_filter] at he
      exact h.tri_mem (hQP0 e he.1).1 (hQP0 e he.1).2 (mem_filter.1 he.2).1
    rcases part_cases v z hext with hL | hC | hI
    · exact (card_le_card hsubt).trans hL
    · refine card_le_one.2 (fun e he e' he' => ?_) |>.trans (by norm_num)
      by_contra hne
      have c1 := C_cont hS7 hK hC (hsubt he)
      have c2 := C_cont hS7 hK hC (hsubt he')
      exact hQ e (mem_filter.1 he).1 e' (mem_filter.1 he').1 hne ⟨_, c1, c2⟩
    · exact absurd hI hnI
  have hsumQ : ∑ e ∈ Q, g e ≤ 8 * J.card := by
    have : ∑ e ∈ Q, g e = ∑ e ∈ Q, (A e).card := rfl
    rw [this, sum_card_eq]
    calc _ ≤ ∑ _z ∈ J, 8 := sum_le_sum hmult
      _ = 8 * J.card := by rw [sum_const, smul_eq_mul]; ring
  have hkQ : k * Q.card ≤ 2 * ∑ e ∈ Q, g e := by
    rw [mul_sum]
    calc k * Q.card = ∑ _e ∈ Q, k := by rw [sum_const, smul_eq_mul]; ring
      _ ≤ _ := sum_le_sum (fun e he => (mem_filter.1 (hQP he)).2)
  have h1 : k * P.card ≤ (4 * a + 1) * (16 * J.card) := by
    calc k * P.card ≤ k * ((4 * a + 1) * Q.card) := Nat.mul_le_mul_left _ hPQ
      _ = (4 * a + 1) * (k * Q.card) := by ring
      _ ≤ (4 * a + 1) * (16 * J.card) := Nat.mul_le_mul_left _ (by omega)
  have h2 : (4 * a + 1) * (16 * J.card) ≤ (4 * a + 1) * (16 * a) :=
    Nat.mul_le_mul_left _ (by omega)
  nlinarith

end

end E813

end S_S1

-- ===== S2 =====
section S_S2

/-! Star lemma, grid regime (original). -/

open Finset

namespace E813

noncomputable section
open Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- the grid parameters exist for every admissible number `r` of rows -/
def GridOK (a s t k : ℕ) : Prop :=
  ∀ r, s ≤ 64 * r → r ≤ s → ∃ j₀ q β s₁ m₁ δ h e φ e' : ℕ,
    a ≤ β * j₀ ∧ s₁ + j₀ ≤ r ∧ m₁ + k * (q * j₀) ≤ t * k / 64 ∧
    h + 2 * a * δ ≤ s₁ * m₁ ∧ t * k ≤ e * e ∧ 2 * e * a * s * k < h * δ ∧
    β ≤ q * φ ∧ s * φ ≤ e' * e' ∧ 2 * β ≤ δ ∧ 4 * (t * k) * e' * a < h * δ

section
variable {out : V → Finset V} {v : V} {S : Finset V} {T : V → Finset V}
  {E : V → V → Finset V} {t k : ℕ}

/-- grid cells: L-vertices and source-centred C-vertices, sinks outside `S` -/
def cellA (G : SimpleGraph V) (v : V) (S : Finset V) (T : V → Finset V)
    (E : V → V → Finset V) (u w : V) : Finset V :=
  if u ∈ S ∧ w ∈ T u ∧ w ∉ S then
    (E u w).filter (fun z => isL G v z ∨ (isC G v z ∧ cen G v z = u)) else ∅

lemma mem_cellA {u w z : V} : z ∈ cellA G v S T E u w ↔ (u ∈ S ∧ w ∈ T u ∧ w ∉ S) ∧
    z ∈ E u w ∧ (isL G v z ∨ (isC G v z ∧ cen G v z = u)) := by
  unfold cellA
  split_ifs with hc
  · rw [mem_filter]; tauto
  · simp only [notMem_empty, false_iff]; tauto

lemma Star.cellA_card (h : Star G out v S T E t k) (u w : V) :
    (cellA G v S T E u w).card ≤ k := by
  unfold cellA
  split_ifs with hc
  · exact (card_le_card (filter_subset _ _)).trans (h.E_card u hc.1 w hc.2.1).le
  · simp

lemma grid_conv (hS7 : Seven3 G) (hK : K4free G) {a : ℕ} (ha : IndLt G a)
    (h : Star G out v S T E t k) (htk : 0 < t * k)
    (hsig : S.card * t * k ≤ 4 * ∑ e ∈ pairs S T, (cellA G v S T E e.1 e.2).card)
    (hpar : GridOK a S.card t k) : False := by
  set P0 := pairs S T
  set A := fun e : V × V => cellA G v S T E e.1 e.2
  set U := P0.biUnion A
  -- multiplicity
  have hmult : ∀ z ∈ U, (P0.filter (fun e => z ∈ A e)).card ≤ 8 := by
    intro z hz
    obtain ⟨e0, he0, hze0⟩ := mem_biUnion.1 hz
    have hA0 := mem_cellA.1 hze0
    rcases hA0.2.2 with hL | ⟨hC, hcen⟩
    · refine (card_le_card ?_).trans hL
      intro e he
      rw [mem_filter] at he
      have := mem_cellA.1 he.2
      exact h.tri_mem this.1.1 this.1.2.1 this.2.1
    · refine card_le_one.2 (fun e he e' he' => ?_) |>.trans (by norm_num)
      have h1 := mem_cellA.1 (mem_filter.1 he).2
      have h2 := mem_cellA.1 (mem_filter.1 he').2
      have hu : e.1 = e'.1 := by
        have c1 : cen G v z = e.1 := by
          rcases h1.2.2 with hL' | ⟨_, hc⟩
          · exact absurd hL' (fun hL' => not_L_and_H hL' hC.1)
          · exact hc
        have c2 : cen G v z = e'.1 := by
          rcases h2.2.2 with hL' | ⟨_, hc⟩
          · exact absurd hL' (fun hL' => not_L_and_H hL' hC.1)
          · exact hc
        exact c1.symm.trans c2
      by_contra hne
      have hw : e.2 ≠ e'.2 := fun hw => hne (Prod.ext hu hw)
      have hd := h.E_disj e.1 h1.1.1 e.2 h1.1.2.1 e'.2 (hu ▸ h2.1.2.1) hw
      rw [hu] at hd
      exact disjoint_left.1 hd (hu ▸ h1.2.1) h2.2.1
  have hsigU : ∑ e ∈ P0, (A e).card ≤ 8 * U.card := by
    rw [sum_card_eq]
    calc _ ≤ ∑ _z ∈ U, 8 := sum_le_sum hmult
      _ = 8 * U.card := by rw [sum_const, smul_eq_mul]; ring
  -- choice of a cell for each vertex
  set cellOf : V → V × V := fun z => if hz : ∃ e ∈ P0, z ∈ A e then hz.choose else (v, v)
  have hcell : ∀ z ∈ U, cellOf z ∈ P0 ∧ z ∈ A (cellOf z) := by
    intro z hz
    have hz' : ∃ e ∈ P0, z ∈ A e := mem_biUnion.1 hz
    simp only [cellOf, dif_pos hz']
    exact hz'.choose_spec
  set row : V → V := fun z => (cellOf z).1
  set col : V → V := fun z => (cellOf z).2
  have hcellA : ∀ z ∈ U, z ∈ cellA G v S T E (row z) (col z) := fun z hz => (hcell z hz).2
  have hrowS : ∀ z ∈ U, row z ∈ S := fun z hz => (mem_cellA.1 (hcellA z hz)).1.1
  have hrowM : ∀ u, (U.filter (fun z => row z = u)).card ≤ t * k := by
    intro u
    by_cases hu : u ∈ S
    · have hsub : U.filter (fun z => row z = u) ⊆ (T u).biUnion (fun w => cellA G v S T E u w) := by
        intro z hz
        rw [mem_filter] at hz
        have := hcellA z hz.1
        rw [hz.2] at this
        exact mem_biUnion.2 ⟨col z, (mem_cellA.1 this).1.2.1, this⟩
      refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
      calc _ ≤ ∑ _w ∈ T u, k := sum_le_sum (fun w _ => h.cellA_card u w)
        _ = t * k := by rw [sum_const, smul_eq_mul, h.T_card u hu]
    · have : U.filter (fun z => row z = u) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro z hz
        rw [mem_filter] at hz
        exact hu (hz.2 ▸ hrowS z hz.1)
      rw [this]; exact Nat.zero_le _
  set m := t * k / 64
  set R := S.filter (fun u => m ≤ (U.filter (fun z => row z = u)).card)
  have hRS : R ⊆ S := filter_subset _ _
  have hUle : U.card ≤ R.card * (t * k) + S.card * m := by
    have hmaps : (U : Set V).MapsTo row S := fun z hz => hrowS z hz
    rw [card_eq_sum_card_fiberwise hmaps,
      ← sum_filter_add_sum_filter_not S (fun u => m ≤ (U.filter (fun z => row z = u)).card)]
    refine add_le_add ?_ ?_
    · calc _ ≤ ∑ _u ∈ R, t * k := sum_le_sum (fun u _ => hrowM u)
        _ = R.card * (t * k) := by rw [sum_const, smul_eq_mul]
    · calc _ ≤ ∑ _u ∈ S.filter (fun u => ¬ m ≤ (U.filter (fun z => row z = u)).card), m :=
            sum_le_sum (fun u hu => by have := (mem_filter.1 hu).2; omega)
        _ ≤ ∑ _u ∈ S, m := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _)
        _ = S.card * m := by rw [sum_const, smul_eq_mul]
  have hm64 : 64 * m ≤ t * k := Nat.mul_div_le _ _
  have hR64 : S.card ≤ 64 * R.card := by
    have h1 : S.card * t * k ≤ 32 * U.card := by
      calc S.card * t * k ≤ 4 * ∑ e ∈ P0, (A e).card := hsig
        _ ≤ 4 * (8 * U.card) := Nat.mul_le_mul_left _ hsigU
        _ = 32 * U.card := by ring
    have h2 : 64 * (S.card * m) ≤ S.card * (t * k) := by nlinarith
    have h3 : S.card * (t * k) ≤ 64 * R.card * (t * k) := by
      have : S.card * (t * k) = S.card * t * k := by ring
      nlinarith
    exact Nat.le_of_mul_le_mul_right h3 htk
  obtain ⟨j₀, q, β, s₁, m₁, δ, hh, e, φ, e', p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ :=
    hpar R.card hR64 (card_le_card hRS)
  set UR := U.filter (fun z => row z ∈ R)
  have hURU : UR ⊆ U := filter_subset _ _
  refine grid_core ha UR R row col k (t * k) m S.card ?_ ?_ ?_ ?_ (card_le_card hRS) ?_ ?_ ?_
    j₀ q β s₁ m₁ δ hh e φ e' p1 p2 p3 p4 p5 p6 p7 p8 p9 p10
  · intro z hz; exact (mem_filter.1 hz).2
  · intro r c
    refine (card_le_card ?_).trans (h.cellA_card r c)
    intro z hz
    rw [mem_filter] at hz
    have := hcellA z (hURU hz.1)
    rw [hz.2.1, hz.2.2] at this
    exact this
  · intro r hr
    have : UR.filter (fun z => row z = r) = U.filter (fun z => row z = r) := by
      ext z
      simp only [UR, mem_filter]
      constructor
      · rintro ⟨⟨hz, _⟩, hzr⟩; exact ⟨hz, hzr⟩
      · rintro ⟨hz, hzr⟩; exact ⟨⟨hz, hzr ▸ hr⟩, hzr⟩
    rw [this]; exact (mem_filter.1 hr).2
  · intro r
    exact (card_le_card (filter_subset_filter _ hURU)).trans (hrowM r)
  · intro z hz z' hz' hzz'
    by_contra hcon
    push_neg at hcon
    have hA := mem_cellA.1 (hcellA z (hURU hz))
    have hA' := mem_cellA.1 (hcellA z' (hURU hz'))
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.facts hA.1.1 hA.1.2.1 hA.2.1
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h.facts hA'.1.1 hA'.1.2.1 hA'.2.1
    have n2 : row z ≠ col z' := fun he => hA'.1.2.2 (he ▸ hA.1.1)
    have n3 : col z ≠ row z' := fun he => hA.1.2.2 (he ▸ hA'.1.1)
    exact h7 hS7 hK a1 a2 a3 b1 b2 b3 a4.symm a5.symm b4.symm b5.symm a6 b6 hcon.1 n2 n3
      hcon.2 hzz'
  · intro r
    refine (trifree_nb hK r).mono ?_
    intro z hz
    rw [mem_filter] at hz
    have hA := mem_cellA.1 (hcellA z (hURU hz.1))
    have := h.out_nb _ (h.E_out _ hA.1.1 _ hA.1.2.1 hA.2.1)
    rw [hz.2] at this; exact this
  · intro c
    refine (trifree_nb hK c).mono ?_
    intro z hz
    rw [mem_filter] at hz
    have hA := mem_cellA.1 (hcellA z (hURU hz.1))
    have := h.E_nb _ hA.1.1 _ hA.1.2.1 hA.2.1
    rw [hz.2] at this; exact this

/-- Star lemma, grid regime -/
lemma starB (hS7 : Seven3 G) (hK : K4free G) {a : ℕ} (ha : IndLt G a)
    (h : Star G out v S T E t k) (hB1 : 12 * S.card ≤ t) (hB2 : 8 * a ≤ t * k)
    (hpar : GridOK a S.card t k) : S.card * t * k ≤ 9 * SI G out v S := by
  have ha0 : 0 < a := by have := ha ∅ ind_empty; simpa using this
  have htk : 0 < t * k := by omega
  have hsig : ¬ S.card * t * k ≤ 4 * ∑ e ∈ pairs S T, (cellA G v S T E e.1 e.2).card :=
    fun hs => grid_conv hS7 hK ha h htk hs hpar
  push_neg at hsig
  -- per-pair split
  have hsplit : ∀ u ∈ S, ∀ w ∈ T u, k ≤ ((E u w).filter (isI G v)).card +
      ((E u w).filter (fun z => isC G v z ∧ cen G v z = w)).card +
      (cellA G v S T E u w).card + (if w ∈ S then k else 0) := by
    intro u hu w hw
    rw [← h.E_card u hu w hw]
    by_cases hwS : w ∈ S
    · rw [if_pos hwS]; omega
    rw [if_neg hwS, add_zero]
    have hsub : E u w ⊆ ((E u w).filter (isI G v) ∪
        (E u w).filter (fun z => isC G v z ∧ cen G v z = w)) ∪ cellA G v S T E u w := by
      intro z hz
      have hext := h.ext hK hu hw hz
      rcases part_cases v z hext with hL | hC | hI
      · exact mem_union_right _ (mem_cellA.2 ⟨⟨hu, hw, hwS⟩, hz, Or.inl hL⟩)
      · rcases C_cont hS7 hK hC (h.tri_mem hu hw hz) with hc | hc
        · exact mem_union_right _ (mem_cellA.2 ⟨⟨hu, hw, hwS⟩, hz, Or.inr ⟨hC, hc.symm⟩⟩)
        · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hz, hC, hc.symm⟩))
      · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hz, hI⟩))
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    have := card_union_le ((E u w).filter (isI G v))
      ((E u w).filter (fun z => isC G v z ∧ cen G v z = w))
    omega
  -- sink part is small
  have hsink : ∀ u ∈ S, ∑ w ∈ T u, ((E u w).filter (fun z => isC G v z ∧ cen G v z = w)).card
      ≤ a := by
    intro u hu
    have hdisj : ((T u : Set V)).PairwiseDisjoint
        (fun w => (E u w).filter (fun z => isC G v z ∧ cen G v z = w)) := by
      intro w hw w' hw' hne
      exact disjoint_filter_filter (h.E_disj u hu w hw w' hw' hne)
    rw [← card_biUnion hdisj]
    refine (ha _ ?_).le
    intro z hz z' hz' hzz'
    obtain ⟨w, hw, hz⟩ := mem_biUnion.1 hz
    obtain ⟨w', hw', hz'⟩ := mem_biUnion.1 hz'
    rw [mem_filter] at hz hz'
    have heq : w = w' := by
      rw [← hz.2.2, ← hz'.2.2]; exact C_cen_eq hS7 hK hz.2.1 hz'.2.1 hzz'
    subst heq
    obtain ⟨-, -, a3, a4, a5, -⟩ := h.facts hu hw hz.1
    obtain ⟨-, -, -, b4, b5, -⟩ := h.facts hu hw hz'.1
    exact hK u w z z' a3 a4 b4 a5 b5 hzz'
  have hleafS : ∀ u ∈ S, ∑ w ∈ T u, (if w ∈ S then k else 0) ≤ S.card * k := by
    intro u hu
    rw [← sum_filter, sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (card_le_card (fun w hw => (mem_filter.1 hw).2))
  have htot : S.card * t * k ≤ SI G out v S + S.card * a +
      ∑ e ∈ pairs S T, (cellA G v S T E e.1 e.2).card + S.card * (S.card * k) := by
    rw [sum_pairs]
    dsimp only
    have h1 : S.card * t * k = ∑ u ∈ S, ∑ _w ∈ T u, k := by
      rw [sum_congr rfl (fun u hu => by rw [sum_const, smul_eq_mul, h.T_card u hu])]
      rw [sum_const, smul_eq_mul]; ring
    have h2 : ∑ u ∈ S, ∑ _w ∈ T u, k ≤ ∑ u ∈ S, ∑ w ∈ T u,
        (((E u w).filter (isI G v)).card +
        ((E u w).filter (fun z => isC G v z ∧ cen G v z = w)).card +
        (cellA G v S T E u w).card + (if w ∈ S then k else 0)) :=
      sum_le_sum (fun u hu => sum_le_sum (fun w hw => hsplit u hu w hw))
    simp only [sum_add_distrib] at h2
    have h3 := h.sumI_le
    have h4 : ∑ u ∈ S, ∑ w ∈ T u, ((E u w).filter (fun z => isC G v z ∧ cen G v z = w)).card
        ≤ S.card * a := by
      calc _ ≤ ∑ _u ∈ S, a := sum_le_sum hsink
        _ = S.card * a := by rw [sum_const, smul_eq_mul]
    have h5 : ∑ u ∈ S, ∑ w ∈ T u, (if w ∈ S then k else 0) ≤ S.card * (S.card * k) := by
      calc _ ≤ ∑ _u ∈ S, S.card * k := sum_le_sum hleafS
        _ = S.card * (S.card * k) := by rw [sum_const, smul_eq_mul]
    omega
  have e1 : 12 * (S.card * (S.card * k)) ≤ S.card * t * k := by
    have := Nat.mul_le_mul_right (S.card * k) hB1
    calc 12 * (S.card * (S.card * k)) = 12 * S.card * (S.card * k) := by ring
      _ ≤ t * (S.card * k) := this
      _ = S.card * t * k := by ring
  have e2 : 8 * (S.card * a) ≤ S.card * t * k := by
    have := Nat.mul_le_mul_left S.card hB2
    calc 8 * (S.card * a) = S.card * (8 * a) := by ring
      _ ≤ S.card * (t * k) := this
      _ = S.card * t * k := by ring
  omega

end

end

end E813

end S_S2

-- ===== C1 =====
section S_C1

/-! Counting `K4`-minus-an-edge configurations: identities and per-vertex lower bounds
(original). -/

open Finset

namespace E813

noncomputable section
open Classical

variable {V : Type*} [Fintype V] (G : SimpleGraph V) (x : ℕ)

/-- common out-neighbours -/
def Dp (p q : V) : Finset V := out G x p ∩ out G x q

def Tsum : ℕ := ∑ p, ∑ q ∈ Nb G p, (Dp G x p q).card ^ 2

def inn (v : V) : Finset V := univ.filter (fun u => v ∈ out G x u)

def C1v (v : V) : ℕ := ∑ p ∈ inn G x v, ∑ q ∈ (inn G x v).filter (G.Adj p), (Dp G x p q).card

def C2v (v : V) : ℕ := ∑ p ∈ Nb G v, ∑ q ∈ (Nb G v).filter (G.Adj p), (Dp G x p q).card ^ 2

def sv (v : V) : ℕ := ∑ u ∈ Nb G v, (Dp G x v u).card ^ 2

variable {G x}

lemma ite_sum' {β : Type*} (c : Prop) [Decidable c] (s : Finset β) (f : β → ℕ) :
    (if c then ∑ y ∈ s, f y else 0) = ∑ y ∈ s, if c then f y else 0 := by
  split_ifs <;> simp

/-- generic double counting of labelled edges -/
lemma label_count {β : Type*} (S : Finset V) (Y : Finset β) (Rel : β → V → Prop)
    [∀ y, DecidablePred (Rel y)] :
    ∑ p ∈ S, ∑ q ∈ S.filter (G.Adj p), (Y.filter (fun y => Rel y p ∧ Rel y q)).card =
      ∑ y ∈ Y, edges G (S.filter (Rel y)) := by
  unfold edges
  simp only [card_eq_sum_ones, sum_filter, ite_sum']
  symm
  rw [sum_comm]
  refine sum_congr rfl (fun p _ => ?_)
  rw [sum_comm]
  refine sum_congr rfl (fun q _ => ?_)
  refine sum_congr rfl (fun y _ => ?_)
  by_cases h1 : G.Adj p q <;> by_cases h2 : Rel y p <;> by_cases h3 : Rel y q <;> simp [h1, h2, h3]

lemma sum_label {β : Type*} (S : Finset V) (Y : Finset β) (Rel : β → V → Prop)
    [∀ y, DecidablePred (Rel y)] :
    ∑ y ∈ Y, (S.filter (Rel y)).card = ∑ p ∈ S, (Y.filter (fun y => Rel y p)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  exact sum_comm

lemma Tsum_eq : Tsum G x = ∑ v, C1v G x v := by
  unfold Tsum C1v inn
  have : ∀ v : V, ∑ p ∈ univ.filter (fun u => v ∈ out G x u),
      ∑ q ∈ (univ.filter (fun u => v ∈ out G x u)).filter (G.Adj p), (Dp G x p q).card =
      ∑ p, ∑ q ∈ Nb G p, if v ∈ Dp G x p q then (Dp G x p q).card else 0 := by
    intro v
    rw [sum_filter]
    refine sum_congr rfl (fun p _ => ?_)
    rw [Nb, filter_filter, sum_filter, sum_filter, ite_sum']
    refine sum_congr rfl (fun q _ => ?_)
    simp only [Dp, mem_inter]
    by_cases h1 : v ∈ out G x p <;> by_cases h2 : v ∈ out G x q <;> by_cases h3 : G.Adj p q <;>
      simp [h1, h2, h3]
  rw [sum_congr rfl (fun v _ => this v), sum_comm]
  refine sum_congr rfl (fun p _ => ?_)
  rw [sum_comm]
  refine sum_congr rfl (fun q _ => ?_)
  rw [← sum_filter, sum_const, smul_eq_mul, filter_mem_eq_inter, univ_inter, sq]

lemma C2_sum_le (hK : K4free G) {a : ℕ} (ha : IndLt G a) : ∑ v, C2v G x v ≤ a * Tsum G x := by
  unfold C2v Tsum
  have : ∀ v : V, ∑ p ∈ Nb G v, ∑ q ∈ (Nb G v).filter (G.Adj p), (Dp G x p q).card ^ 2 =
      ∑ p, ∑ q ∈ Nb G p, if v ∈ (Nb G p).filter (G.Adj q) then (Dp G x p q).card ^ 2 else 0 := by
    intro v
    rw [Nb, sum_filter]
    refine sum_congr rfl (fun p _ => ?_)
    rw [Nb, filter_filter, sum_filter, sum_filter, ite_sum']
    refine sum_congr rfl (fun q _ => ?_)
    simp only [mem_filter, mem_univ, true_and]
    by_cases h1 : G.Adj v p <;> by_cases h2 : G.Adj v q <;> by_cases h3 : G.Adj p q <;>
      simp [h1, h2, h3, G.adj_comm]
  rw [sum_congr rfl (fun v _ => this v), sum_comm, mul_sum]
  refine sum_le_sum (fun p _ => ?_)
  rw [sum_comm, mul_sum]
  refine sum_le_sum (fun q hq => ?_)
  rw [← sum_filter, sum_const, smul_eq_mul, filter_mem_eq_inter, univ_inter]
  refine Nat.mul_le_mul_right _ (ha _ (ind_common hK (mem_Nb.1 hq))).le

lemma inn_sub (v : V) : inn G x v ⊆ Nb G v := by
  intro u hu
  simp only [inn, mem_filter, mem_univ, true_and] at hu
  exact mem_Nb.2 (out_adj hu).symm

lemma sum_inn : ∑ v, (inn G x v).card = ∑ u, (out G x u).card := by
  have : ∀ u, (out G x u).card = ∑ v, if v ∈ out G x u then 1 else 0 := fun u => by
    rw [← card_filter, filter_mem_eq_inter, univ_inter]
  simp_rw [this]
  simp only [inn, card_filter]
  exact sum_comm

/-- the I-part -/
def Ipart (G : SimpleGraph V) (v : V) : Finset V := univ.filter (isI G v)

lemma Ipart_card {a : ℕ} (ha : IndLt G a) (v : V) : (Ipart G v).card < a := by
  refine ha _ (fun y hy y' hy' => ?_)
  simp only [Ipart, mem_filter, mem_univ, true_and] at hy hy'
  exact I_ind hy hy'

/-- Claim-1 type bound: `m * SI ≤ C1v + a² m²` -/
lemma C1_lower {a : ℕ} (ha : IndLt G a) (v : V) (m : ℕ) :
    m * SI G (out G x) v (inn G x v) ≤ C1v G x v + a * a * m ^ 2 := by
  have h1 : SI G (out G x) v (inn G x v) =
      ∑ y ∈ Ipart G v, ((inn G x v).filter (fun p => y ∈ out G x p)).card := by
    rw [sum_label (inn G x v) (Ipart G v) (fun y p => y ∈ out G x p)]
    unfold SI
    refine sum_congr rfl (fun p _ => ?_)
    congr 1; ext y; simp only [Ipart, mem_filter, mem_univ, true_and]; tauto
  have h2 : ∑ y ∈ Ipart G v, edges G ((inn G x v).filter (fun p => y ∈ out G x p)) ≤
      C1v G x v := by
    rw [← label_count (inn G x v) (Ipart G v) (fun y p => y ∈ out G x p)]
    unfold C1v
    refine sum_le_sum (fun p _ => sum_le_sum (fun q _ => card_le_card ?_))
    intro y hy
    rw [mem_filter] at hy
    exact mem_inter.2 hy.2
  have h4 : ∑ y ∈ Ipart G v, m * ((inn G x v).filter (fun p => y ∈ out G x p)).card ≤
      ∑ y ∈ Ipart G v, (edges G ((inn G x v).filter (fun p => y ∈ out G x p)) + a * m ^ 2) :=
    sum_le_sum (fun y _ => turan_lite ha _ m)
  rw [← mul_sum, sum_add_distrib, sum_const, smul_eq_mul] at h4
  have h5 : (Ipart G v).card * (a * m ^ 2) ≤ a * a * m ^ 2 := by
    have := (Ipart_card ha v).le
    calc (Ipart G v).card * (a * m ^ 2) ≤ a * (a * m ^ 2) := Nat.mul_le_mul_right _ this
      _ = a * a * m ^ 2 := by ring
  rw [h1]; omega

/-- Claim-2 type bound -/
lemma C2_lower {a : ℕ} (ha : IndLt G a) (v : V) (S : Finset V) (hS : S ⊆ Nb G v) (m : ℕ) :
    m * ∑ u ∈ S, ((out G x u).filter (isI G v)).card ^ 2 ≤ C2v G x v + a * a * a * m ^ 2 := by
  have h1 : ∑ u ∈ S, ((out G x u).filter (isI G v)).card ^ 2 =
      ∑ y ∈ Ipart G v ×ˢ Ipart G v,
        (S.filter (fun p => y.1 ∈ out G x p ∧ y.2 ∈ out G x p)).card := by
    rw [sum_label S (Ipart G v ×ˢ Ipart G v) (fun y p => y.1 ∈ out G x p ∧ y.2 ∈ out G x p)]
    refine sum_congr rfl (fun p _ => ?_)
    have : (Ipart G v ×ˢ Ipart G v).filter (fun y => y.1 ∈ out G x p ∧ y.2 ∈ out G x p) =
        ((out G x p).filter (isI G v)) ×ˢ ((out G x p).filter (isI G v)) := by
      ext ⟨y, y'⟩
      simp only [Ipart, mem_filter, mem_product, mem_univ, true_and]; tauto
    rw [this, card_product, sq]
  have h2 : ∑ y ∈ Ipart G v ×ˢ Ipart G v,
      edges G (S.filter (fun p => y.1 ∈ out G x p ∧ y.2 ∈ out G x p)) ≤ C2v G x v := by
    rw [← label_count S (Ipart G v ×ˢ Ipart G v)
      (fun y p => y.1 ∈ out G x p ∧ y.2 ∈ out G x p)]
    unfold C2v
    calc _ ≤ ∑ p ∈ S, ∑ q ∈ S.filter (G.Adj p), (Dp G x p q).card ^ 2 := by
          refine sum_le_sum (fun p _ => sum_le_sum (fun q _ => ?_))
          rw [sq, ← card_product]
          refine card_le_card ?_
          intro yy hyy
          simp only [mem_filter] at hyy
          exact mem_product.2 ⟨mem_inter.2 ⟨hyy.2.1.1, hyy.2.2.1⟩,
            mem_inter.2 ⟨hyy.2.1.2, hyy.2.2.2⟩⟩
      _ ≤ ∑ p ∈ S, ∑ q ∈ (Nb G v).filter (G.Adj p), (Dp G x p q).card ^ 2 :=
          sum_le_sum (fun p _ => sum_le_sum_of_subset_of_nonneg
            (filter_subset_filter _ hS) (fun _ _ _ => Nat.zero_le _))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)
  have h4 : ∑ y ∈ Ipart G v ×ˢ Ipart G v,
      m * (S.filter (fun p => y.1 ∈ out G x p ∧ y.2 ∈ out G x p)).card ≤
      ∑ y ∈ Ipart G v ×ˢ Ipart G v,
        (edges G (S.filter (fun p => y.1 ∈ out G x p ∧ y.2 ∈ out G x p)) + a * m ^ 2) :=
    sum_le_sum (fun y _ => turan_lite ha _ m)
  rw [← mul_sum, sum_add_distrib, sum_const, smul_eq_mul] at h4
  have h5 : (Ipart G v ×ˢ Ipart G v).card * (a * m ^ 2) ≤ a * a * a * m ^ 2 := by
    have := (Ipart_card ha v).le
    have hY : (Ipart G v ×ˢ Ipart G v).card ≤ a * a := by
      rw [card_product]; exact Nat.mul_le_mul this this
    calc _ ≤ a * a * (a * m ^ 2) := Nat.mul_le_mul_right _ hY
      _ = a * a * a * m ^ 2 := by ring
  rw [h1]; omega

/-- building the star data via Hall -/
lemma mk_star (hK : K4free G) {v : V} {S : Finset V} {T : V → Finset V} {t : ℕ}
    (hS : S ⊆ Nb G v) (hT : ∀ u ∈ S, T u ⊆ out G x u ∧ T u ⊆ Nb G v ∧ (T u).card = t) :
    ∃ E, Star G (out G x) v S T E t x := by
  have hE : ∀ u ∈ S, ∃ Eu : V → Finset V,
      (∀ w ∈ T u, Eu w ⊆ ((out G x u).filter (G.Adj w)).erase v ∧ (Eu w).card = x) ∧
      ∀ w ∈ T u, ∀ w' ∈ T u, w ≠ w' → Disjoint (Eu w) (Eu w') := by
    intro u hu
    obtain ⟨hTo, hTv, -⟩ := hT u hu
    have hvu : G.Adj v u := mem_Nb.1 (hS hu)
    have hind : Ind G (T u) := by
      refine (ind_common hK hvu).mono ?_
      intro w hw
      exact mem_filter.2 ⟨hTv hw, out_adj (hTo hw)⟩
    refine hall_stars (T u) (fun w => ((out G x u).filter (G.Adj w)).erase v) x ?_
    intro Y hY
    rcases Y.eq_empty_or_nonempty with hY0 | hY0
    · simp [hY0]
    have := out_expand x u Y (hY.trans hTo) (hind.mono hY) hY0
    have hsub : (out G x u).filter (fun z => ∃ y ∈ Y, G.Adj y z) ⊆
        insert v (Y.biUnion (fun w => ((out G x u).filter (G.Adj w)).erase v)) := by
      intro z hz
      rw [mem_filter] at hz
      obtain ⟨y, hy, hyz⟩ := hz.2
      by_cases hzv : z = v
      · rw [hzv]; exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_biUnion.2 ⟨y, hy, mem_erase.2 ⟨hzv, mem_filter.2 ⟨hz.1, hyz⟩⟩⟩)
    have := (card_le_card hsub).trans (card_insert_le _ _)
    omega
  choose! Eu hEu1 hEu2 using hE
  refine ⟨fun u w => Eu u w, ⟨fun u => out_sub x u, hS, fun u hu => (hT u hu).1,
    fun u hu => (hT u hu).2.1, fun u hu => (hT u hu).2.2, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro u hu w hw z hz
    exact (mem_filter.1 (mem_of_mem_erase ((hEu1 u hu w hw).1 hz))).1
  · intro u hu w hw z hz
    exact mem_Nb.2 (mem_filter.1 (mem_of_mem_erase ((hEu1 u hu w hw).1 hz))).2
  · intro u hu w hw hv
    exact (notMem_erase v _) ((hEu1 u hu w hw).1 hv)
  · intro u hu w hw; exact (hEu1 u hu w hw).2
  · intro u hu w hw w' hw' hne; exact hEu2 u hu w hw w' hw' hne

/-- Claim 1 at a vertex, uniform form -/
lemma claim1_v (hS7 : Seven3 G) (hK : K4free G) {a : ℕ} (ha : IndLt G a) (v : V) (m : ℕ) :
    m * ((inn G x v).card * x * x) ≤ 9 * C1v G x v + 9 * (a * a * m ^ 2) + 210 * a * a * m := by
  by_cases hbig : 210 * a * a ≤ (inn G x v).card * x * x
  · have hT : ∀ u ∈ inn G x v, ∃ Tu ⊆ (out G x u).filter (G.Adj v), Tu.card = x := by
      intro u hu
      have hvu : v ∈ out G x u := by simp [inn] at hu; exact hu
      have := out_expand x u {v} (by simpa using hvu) (by
        intro y hy y' hy'; simp at hy hy'; subst hy; subst hy'; exact G.irrefl) (by simp)
      simp only [mem_singleton, exists_eq_left, card_singleton, mul_one] at this
      exact exists_subset_card_eq this.le
    choose! T hT1 hT2 using hT
    obtain ⟨E, hE⟩ := mk_star (x := x) hK (inn_sub v) (T := T) (t := x) (fun u hu =>
      ⟨(hT1 u hu).trans (filter_subset _ _), fun w hw => mem_Nb.2 (mem_filter.1 (hT1 u hu hw)).2,
        hT2 u hu⟩)
    have h1 := starA hS7 hK ha hE hbig
    have h2 := C1_lower (x := x) ha v m
    have : m * ((inn G x v).card * x * x) ≤ m * (9 * SI G (out G x) v (inn G x v)) :=
      Nat.mul_le_mul_left _ h1
    nlinarith
  · push_neg at hbig
    have : m * ((inn G x v).card * x * x) ≤ m * (210 * a * a) := Nat.mul_le_mul_left _ hbig.le
    nlinarith

end

end E813

end S_C1

-- ===== C2 =====
section S_C2

/-! Claim 2 at a vertex: dyadic regularisation of a star and the 4-tuple count (original). -/

open Finset

namespace E813

noncomputable section
open Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {x : ℕ}

lemma Dp_sub (hK : K4free G) {v u : V} (hvu : G.Adj v u) :
    Dp G x v u ⊆ (Nb G v).filter (G.Adj u) := by
  intro z hz
  rw [Dp, mem_inter] at hz
  exact mem_filter.2 ⟨out_sub x v hz.1, out_adj hz.2⟩

lemma Dp_lt (hK : K4free G) {a : ℕ} (ha : IndLt G a) {v u : V} (hvu : G.Adj v u) :
    (Dp G x v u).card < a :=
  lt_of_le_of_lt (card_le_card (Dp_sub hK hvu)) (ha _ (ind_common hK hvu))

/-- dyadic bound for a single term -/
lemma sq_le_dyadic (d L : ℕ) (hd : d < 2 ^ L) :
    d ^ 2 ≤ ∑ j ∈ range L, if 2 ^ j ≤ d ∧ d < 2 ^ (j + 1) then 4 ^ (j + 1) else 0 := by
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · subst h0; simp
  set j0 := Nat.log 2 d
  have hj0 : j0 < L := Nat.log_lt_of_lt_pow (by omega) hd
  have h1 : 2 ^ j0 ≤ d := Nat.pow_log_le_self 2 (by omega)
  have h2 : d < 2 ^ (j0 + 1) := Nat.lt_pow_succ_log_self (by norm_num) d
  have h3 : d ^ 2 ≤ 4 ^ (j0 + 1) := by
    have : (4 : ℕ) ^ (j0 + 1) = (2 ^ (j0 + 1)) ^ 2 := by
      rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
    rw [this]; exact Nat.pow_le_pow_left h2.le 2
  refine le_trans ?_ (single_le_sum (f := fun j => if 2 ^ j ≤ d ∧ d < 2 ^ (j + 1) then
    4 ^ (j + 1) else 0) (fun _ _ => Nat.zero_le _) (mem_range.2 hj0))
  simp only [h1, h2, and_self, if_true]; exact h3

/-- Claim 2 at a vertex -/
lemma claim2_v (hS7 : Seven3 G) (hK : K4free G) {a : ℕ} (ha : IndLt G a) (v : V) (L : ℕ)
    (hL : ∀ u ∈ Nb G v, (Dp G x v u).card < 2 ^ L) (hL1 : 1 ≤ L)
    (hreg : ∀ s t : ℕ, 1 ≤ s → 1 ≤ t → t < a → sv G x v ≤ 4 * L * (s * t ^ 2) →
      648 * a ^ 3 ≤ s * t ^ 2 * x ^ 2 ∧
      (210 * a * a ≤ s * t * x ∨ (12 * s ≤ t ∧ 8 * a ≤ t * x ∧ GridOK a s t x))) :
    7 * sv G x v ^ 2 * x ^ 4 ≤ 16 * 6561 * 128 * L ^ 2 * a ^ 3 * C2v G x v := by
  set cls := fun j : ℕ => (Nb G v).filter (fun u =>
    2 ^ j ≤ (Dp G x v u).card ∧ (Dp G x v u).card < 2 ^ (j + 1))
  have h1 : sv G x v ≤ ∑ j ∈ range L, (cls j).card * 4 ^ (j + 1) := by
    unfold sv
    calc _ ≤ ∑ u ∈ Nb G v, ∑ j ∈ range L, if 2 ^ j ≤ (Dp G x v u).card ∧
          (Dp G x v u).card < 2 ^ (j + 1) then 4 ^ (j + 1) else 0 :=
          sum_le_sum (fun u hu => sq_le_dyadic _ L (hL u hu))
      _ = _ := by
          rw [sum_comm]
          refine sum_congr rfl (fun j _ => ?_)
          rw [← sum_filter, sum_const, smul_eq_mul]
  obtain ⟨j0, hj0, hmax⟩ := (range L).exists_max_image (fun j => (cls j).card * 4 ^ j)
    ⟨0, mem_range.2 hL1⟩
  set s := (cls j0).card
  set t := 2 ^ j0
  have ht4 : (4 : ℕ) ^ j0 = t ^ 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
  have h2 : sv G x v ≤ 4 * L * (s * t ^ 2) := by
    refine h1.trans ?_
    calc ∑ j ∈ range L, (cls j).card * 4 ^ (j + 1)
        ≤ ∑ _j ∈ range L, 4 * (s * 4 ^ j0) := by
          refine sum_le_sum (fun j hj => ?_)
          have := hmax j hj
          calc (cls j).card * 4 ^ (j + 1) = 4 * ((cls j).card * 4 ^ j) := by ring
            _ ≤ 4 * (s * 4 ^ j0) := Nat.mul_le_mul_left _ this
      _ = 4 * L * (s * t ^ 2) := by rw [sum_const, card_range, smul_eq_mul, ht4]; ring
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · have : sv G x v = 0 := by rw [hs0] at h2; simpa using h2
    rw [this]; simp
  obtain ⟨u0, hu0⟩ := card_pos.1 hspos
  have hu0' := mem_filter.1 hu0
  have ht1 : 1 ≤ t := Nat.one_le_two_pow
  have hta : t < a := lt_of_le_of_lt hu0'.2.1 (Dp_lt hK ha (mem_Nb.1 hu0'.1))
  obtain ⟨hX8, hcase⟩ := hreg s t hspos ht1 hta h2
  -- the star
  have hT : ∀ u ∈ cls j0, ∃ Tu ⊆ Dp G x v u, Tu.card = t := fun u hu =>
    exists_subset_card_eq (mem_filter.1 hu).2.1
  choose! T hT1 hT2 using hT
  have hclsNb : cls j0 ⊆ Nb G v := filter_subset _ _
  obtain ⟨E, hE⟩ := mk_star (x := x) hK hclsNb (T := T) (t := t) (fun u hu =>
    ⟨(hT1 u hu).trans inter_subset_right,
     (hT1 u hu).trans (inter_subset_left.trans (out_sub x v)), hT2 u hu⟩)
  have hstar : s * t * x ≤ 9 * SI G (out G x) v (cls j0) := by
    rcases hcase with hA | ⟨hB1, hB2, hgrid⟩
    · exact starA hS7 hK ha hE hA
    · exact starB hS7 hK ha hE hB1 hB2 hgrid
  set X := ∑ u ∈ cls j0, ((out G x u).filter (isI G v)).card ^ 2
  have hCS : SI G (out G x) v (cls j0) ^ 2 ≤ s * X := sq_sum_le_card_mul_sum_sq
  have hX : s * t ^ 2 * x ^ 2 ≤ 81 * X := by
    have e1 : (s * t * x) ^ 2 ≤ 81 * (s * X) := by
      calc (s * t * x) ^ 2 ≤ (9 * SI G (out G x) v (cls j0)) ^ 2 := Nat.pow_le_pow_left hstar 2
        _ = 81 * SI G (out G x) v (cls j0) ^ 2 := by ring
        _ ≤ 81 * (s * X) := Nat.mul_le_mul_left _ hCS
    have e2 : s * (s * t ^ 2 * x ^ 2) ≤ s * (81 * X) := by
      calc s * (s * t ^ 2 * x ^ 2) = (s * t * x) ^ 2 := by ring
        _ ≤ 81 * (s * X) := e1
        _ = s * (81 * X) := by ring
    exact Nat.le_of_mul_le_mul_left e2 hspos
  have ha3 : 0 < a ^ 3 := by have := ha ∅ ind_empty; simp at this; positivity
  set m := X / (8 * a ^ 3)
  have hm1 : 8 * a ^ 3 * m ≤ X := Nat.mul_div_le X (8 * a ^ 3)
  have hm2 : X < 8 * a ^ 3 * (m + 1) := by
    have := Nat.lt_div_mul_add (a := X) (show 0 < 8 * a ^ 3 by positivity)
    calc X < X / (8 * a ^ 3) * (8 * a ^ 3) + 8 * a ^ 3 := this
      _ = 8 * a ^ 3 * (m + 1) := by ring
  have hX8' : 8 * a ^ 3 ≤ X := by omega
  have hm0 : 1 ≤ m := (Nat.le_div_iff_mul_le (by positivity)).2 (by linarith)
  have hX16 : X ≤ 16 * a ^ 3 * m := by nlinarith
  have hC2 : m * X ≤ C2v G x v + a * a * a * m ^ 2 := C2_lower (x := x) ha v (cls j0) hclsNb m
  have h7 : 7 * (m * X) ≤ 8 * C2v G x v := by
    have : 8 * (a * a * a * m ^ 2) ≤ m * X := by
      calc 8 * (a * a * a * m ^ 2) = m * (8 * a ^ 3 * m) := by ring
        _ ≤ m * X := Nat.mul_le_mul_left _ hm1
    omega
  have hXX : 7 * X ^ 2 ≤ 128 * a ^ 3 * C2v G x v := by
    calc 7 * X ^ 2 = 7 * X * X := by ring
      _ ≤ 7 * X * (16 * a ^ 3 * m) := Nat.mul_le_mul_left _ hX16
      _ = 16 * a ^ 3 * (7 * (m * X)) := by ring
      _ ≤ 16 * a ^ 3 * (8 * C2v G x v) := Nat.mul_le_mul_left _ h7
      _ = 128 * a ^ 3 * C2v G x v := by ring
  calc 7 * sv G x v ^ 2 * x ^ 4 ≤ 7 * (4 * L * (s * t ^ 2)) ^ 2 * x ^ 4 := by
        gcongr
    _ = 16 * L ^ 2 * (7 * (s * t ^ 2 * x ^ 2) ^ 2) := by ring
    _ ≤ 16 * L ^ 2 * (7 * (81 * X) ^ 2) := by gcongr
    _ = 16 * 6561 * L ^ 2 * (7 * X ^ 2) := by ring
    _ ≤ 16 * 6561 * L ^ 2 * (128 * a ^ 3 * C2v G x v) := Nat.mul_le_mul_left _ hXX
    _ = 16 * 6561 * 128 * L ^ 2 * a ^ 3 * C2v G x v := by ring

end

end E813

end S_C2

-- ===== M1 =====
section S_M1

/-! The global counting facts (original). -/

open Finset

namespace E813

noncomputable section
open Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- the constant of Claim 2 -/
def C0 : ℕ := 16 * 6561 * 128

/-- The four global facts. -/
theorem core (hS7 : Seven3 G) (hK : K4free G) {a : ℕ} (ha : IndLt G a) (x L : ℕ)
    (hL : a ≤ 2 ^ L) (hL1 : 1 ≤ L) :
    let n := Fintype.card V
    let T := Tsum G x
    let Dsum := ∑ u, (out G x u).card
    let E := ∑ u, (Nb G u).card
    (∀ m : ℕ, m * n ≤ E + a * m ^ 2) ∧ E ≤ Dsum + n * (a * (x + 1)) ∧
    (∀ m : ℕ, m * (x * x) * Dsum ≤ 9 * T + n * (9 * (a * a * m ^ 2) + 210 * a * a * m)) ∧
    ((∀ s t : ℕ, 1 ≤ s → 1 ≤ t → t < a → T ≤ 16 * n * L * (s * t ^ 2) →
      648 * a ^ 3 ≤ s * t ^ 2 * x ^ 2 ∧
      (210 * a * a ≤ s * t * x ∨ (12 * s ≤ t ∧ 8 * a ≤ t * x ∧ GridOK a s t x))) →
      7 * x ^ 4 * T ≤ n * (2 * C0 * L ^ 2 * a ^ 4 + 7 * x ^ 4)) := by
  intro n T Dsum E
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    have := turan_lite ha (univ : Finset V) m
    rw [card_univ] at this
    have hE : edges G univ = E := rfl
    linarith
  · calc E ≤ ∑ u, ((out G x u).card + a * (x + 1)) := sum_le_sum (fun u _ => out_card ha x u)
      _ = Dsum + n * (a * (x + 1)) := by rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul]
  · intro m
    have h := sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) => claim1_v (x := x) hS7 hK ha v m)
    rw [← mul_sum, ← sum_mul, ← sum_mul, sum_inn, sum_add_distrib, sum_add_distrib,
      ← mul_sum, ← Tsum_eq, sum_const, sum_const, card_univ, smul_eq_mul, smul_eq_mul] at h
    have : m * (Dsum * x * x) = m * (x * x) * Dsum := by ring
    calc m * (x * x) * Dsum = m * (Dsum * x * x) := by ring
      _ ≤ _ := h
      _ = 9 * T + n * (9 * (a * a * m ^ 2) + 210 * a * a * m) := by ring
  · intro hreg
    have hLu : ∀ v, ∀ u ∈ Nb G v, (Dp G x v u).card < 2 ^ L := fun v u hu =>
      lt_of_lt_of_le (Dp_lt hK ha (mem_Nb.1 hu)) hL
    rcases Nat.eq_zero_or_pos T with hT0 | hTpos
    · rw [hT0]; simp
    have hnpos : 0 < n := by
      by_contra hn; push_neg at hn
      have hn0 : n = 0 := by omega
      have : (univ : Finset V) = ∅ := card_eq_zero.1 (by rw [card_univ]; exact hn0)
      have : T = 0 := by
        show Tsum G x = 0
        unfold Tsum; rw [this]; simp
      omega
    set lam := T / n
    have hlam : n * lam ≤ T := Nat.mul_div_le T n
    have hv : ∀ v, 56 * n * x ^ 4 * lam * sv G x v ≤
        4 * n * C0 * L ^ 2 * a ^ 3 * C2v G x v + (28 * n * x ^ 4 * lam ^ 2 + 14 * x ^ 4 * lam * T) := by
      intro v
      by_cases hgood : T ≤ 4 * n * sv G x v
      · have hc2 := claim2_v (x := x) hS7 hK ha v L (hLu v) hL1 (fun s t h1 h2 h3 h4 =>
          hreg s t h1 h2 h3 (by nlinarith))
        have hsq : 2 * lam * sv G x v ≤ sv G x v ^ 2 + lam ^ 2 := by
          nlinarith [sq_nonneg ((sv G x v : ℤ) - lam)]
        have e2 : 7 * x ^ 4 * (2 * lam * sv G x v) ≤ 7 * x ^ 4 * (sv G x v ^ 2 + lam ^ 2) :=
          Nat.mul_le_mul_left _ hsq
        calc 56 * n * x ^ 4 * lam * sv G x v = 4 * n * (7 * x ^ 4 * (2 * lam * sv G x v)) := by ring
          _ ≤ 4 * n * (7 * x ^ 4 * (sv G x v ^ 2 + lam ^ 2)) := Nat.mul_le_mul_left _ e2
          _ = 4 * n * (7 * sv G x v ^ 2 * x ^ 4) + 28 * n * x ^ 4 * lam ^ 2 := by ring
          _ ≤ 4 * n * (16 * 6561 * 128 * L ^ 2 * a ^ 3 * C2v G x v) + 28 * n * x ^ 4 * lam ^ 2 :=
              Nat.add_le_add_right (Nat.mul_le_mul_left _ hc2) _
          _ = 4 * n * C0 * L ^ 2 * a ^ 3 * C2v G x v + 28 * n * x ^ 4 * lam ^ 2 := by
              unfold C0; ring
          _ ≤ _ := by omega
      · push_neg at hgood
        calc 56 * n * x ^ 4 * lam * sv G x v = 14 * x ^ 4 * lam * (4 * n * sv G x v) := by ring
          _ ≤ 14 * x ^ 4 * lam * T := Nat.mul_le_mul_left _ hgood.le
          _ ≤ _ := by omega
    have hsum := sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) => hv v)
    rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_const, card_univ, smul_eq_mul] at hsum
    have hT : ∑ v, sv G x v = T := rfl
    rw [hT] at hsum
    have hC2 := C2_sum_le (x := x) hK ha
    have k1 : 4 * n * C0 * L ^ 2 * a ^ 3 * ∑ v, C2v G x v ≤ 4 * n * C0 * L ^ 2 * a ^ 3 * (a * T) :=
      Nat.mul_le_mul_left _ hC2
    have k2 : n * (28 * n * x ^ 4 * lam ^ 2) ≤ 28 * n * x ^ 4 * lam * T := by
      have := Nat.mul_le_mul_left (28 * n * x ^ 4 * lam) hlam
      nlinarith
    have hmain : (14 * x ^ 4 * lam) * (n * T) ≤ (4 * C0 * L ^ 2 * a ^ 4) * (n * T) := by
      nlinarith
    have hlam2 : 14 * x ^ 4 * lam ≤ 4 * C0 * L ^ 2 * a ^ 4 :=
      Nat.le_of_mul_le_mul_right hmain (Nat.mul_pos hnpos hTpos)
    have hTlt : T < lam * n + n := Nat.lt_div_mul_add hnpos
    have p1 := Nat.mul_le_mul_left n hlam2
    have p2 : 7 * x ^ 4 * T ≤ 7 * x ^ 4 * (lam * n + n) := Nat.mul_le_mul_left _ hTlt.le
    have p4 : 2 * (7 * x ^ 4 * (lam * n + n)) = n * (14 * x ^ 4 * lam) + 14 * x ^ 4 * n := by ring
    have p5 : 2 * (n * (2 * C0 * L ^ 2 * a ^ 4 + 7 * x ^ 4)) =
        n * (4 * C0 * L ^ 2 * a ^ 4) + 14 * x ^ 4 * n := by ring
    omega

end

end E813

end S_M1

-- ===== N1 =====
section S_N1

/-! Choice of the grid parameters (original). -/

namespace E813

lemma sq_lt_imp_lt {A B : ℕ} (h : A ^ 2 < B ^ 2) : A < B := by
  by_contra hc; push_neg at hc
  exact absurd h (not_lt.2 (Nat.pow_le_pow_left hc 2))

lemma sqrt_succ_bounds (M : ℕ) (hM : 1 ≤ M) :
    M ≤ (Nat.sqrt M + 1) * (Nat.sqrt M + 1) ∧ (Nat.sqrt M + 1) ^ 2 ≤ 4 * M := by
  have h1 := Nat.lt_succ_sqrt' M
  have h2 := Nat.sqrt_le' M
  have h3 : 1 ≤ Nat.sqrt M := Nat.sqrt_pos.2 hM
  refine ⟨?_, ?_⟩
  · have := h1.le; rw [Nat.succ_eq_add_one, sq] at this; exact this
  · have e1 : Nat.sqrt M + 1 ≤ 2 * Nat.sqrt M := by omega
    calc (Nat.sqrt M + 1) ^ 2 ≤ (2 * Nat.sqrt M) ^ 2 := Nat.pow_le_pow_left e1 2
      _ = 4 * Nat.sqrt M ^ 2 := by ring
      _ ≤ 4 * M := Nat.mul_le_mul_left _ h2

lemma grid_ok (a s t k : ℕ) (ha : 1 ≤ a) (hs : 256 ≤ s) (hts : 1024 * s ≤ t) (hta : t ≤ a)
    (hk : 1 ≤ k) (c1 : 2 ^ 20 * a ≤ s * t * k) (c2 : 2 ^ 28 * a ^ 2 ≤ s ^ 2 * t * k)
    (c3 : 2 ^ 73 * a ^ 4 ≤ s ^ 2 * t ^ 3 * k) (c4 : 2 ^ 92 * a ^ 5 ≤ s ^ 3 * t ^ 3 * k ^ 2) :
    GridOK a s t k := by
  intro r hr1 hr2
  have ha0 : 0 < a := by omega
  have hs0 : 0 < s := by omega
  have ht0 : 0 < t := by omega
  have hk0 : 0 < k := by omega
  have hr4 : 4 ≤ r := by omega
  set j₀ := r / 2 with hj₀
  have hj1 : 2 * j₀ ≤ r := Nat.mul_div_le r 2
  have hj2 : r ≤ 2 * j₀ + 1 := by omega
  have hj0 : 1 ≤ j₀ := by omega
  set s₁ := r - j₀ with hs₁
  set β := a / j₀ + 1 with hβ
  have hβ1 : a ≤ β * j₀ := by
    have := Nat.lt_div_mul_add (a := a) (show 0 < j₀ by omega)
    have e : (a / j₀ + 1) * j₀ = a / j₀ * j₀ + j₀ := by ring
    rw [hβ, e]; omega
  have hβ2 : (a / j₀) * j₀ ≤ a := Nat.div_mul_le_self a j₀
  set m := t * k / 64 with hm
  have hm1 : 64 * m ≤ t * k := Nat.mul_div_le _ _
  have hm2 : t * k < m * 64 + 64 := Nat.lt_div_mul_add (by norm_num)
  have htk : 2 ^ 18 ≤ t * k := by
    have : 2 ^ 18 ≤ t := by omega
    exact this.trans (Nat.le_mul_of_pos_right t hk)
  have hm3 : t * k ≤ 128 * m := by omega
  set q := m / (2 * k * j₀) with hq
  have hq1 : q * (2 * k * j₀) ≤ m := Nat.div_mul_le_self _ _
  have hq2 : m < q * (2 * k * j₀) + 2 * k * j₀ := Nat.lt_div_mul_add (Nat.mul_pos (Nat.mul_pos (by norm_num) hk0) (by omega))
  -- `t < 256 s q`
  have hq3 : t < 256 * s * q ∧ 1 ≤ q := by
    have e1 : t * k < 128 * (q * (2 * k * j₀) + 2 * k * j₀) := by omega
    have e2 : 2 * j₀ ≤ s := by omega
    have e3 : 128 * (q * (2 * k * j₀) + 2 * k * j₀) ≤ 128 * (k * s * (q + 1)) := by
      have : q * (2 * k * j₀) + 2 * k * j₀ = k * (2 * j₀) * (q + 1) := by ring
      rw [this]; gcongr
    have e4 : t * k < k * (128 * s * (q + 1)) := by
      calc t * k < 128 * (q * (2 * k * j₀) + 2 * k * j₀) := e1
        _ ≤ 128 * (k * s * (q + 1)) := e3
        _ = k * (128 * s * (q + 1)) := by ring
    have e5 : t < 128 * s * (q + 1) := by
      rw [mul_comm k] at e4
      exact Nat.lt_of_mul_lt_mul_right e4
    have e6 : 1 ≤ q := by
      by_contra h; push_neg at h
      have : q = 0 := Nat.lt_one_iff.mp h
      rw [this] at e5
      have : t < 128 * s := by simpa using e5
      omega
    have e7 : s ≤ s * q := Nat.le_mul_of_pos_right s e6
    have e8 : 128 * s * (q + 1) = 128 * (s * q) + 128 * s := by ring
    have e9 : 256 * s * q = 256 * (s * q) := by ring
    exact ⟨by omega, e6⟩
  obtain ⟨hq4, hq5⟩ := hq3
  set m₁ := m - k * (q * j₀) with hm₁
  have hm₁a : m₁ + k * (q * j₀) ≤ m := by
    have : 2 * (k * (q * j₀)) ≤ m := by
      calc 2 * (k * (q * j₀)) = q * (2 * k * j₀) := by ring
        _ ≤ m := hq1
    omega
  have hm₁b : m ≤ 2 * m₁ := by
    have : 2 * (k * (q * j₀)) ≤ m := by
      calc 2 * (k * (q * j₀)) = q * (2 * k * j₀) := by ring
        _ ≤ m := hq1
    omega
  have hs₁b : s ≤ 128 * s₁ := by omega
  have hsm : s * (t * k) ≤ 32768 * (s₁ * m₁) := by
    have e1 : t * k ≤ 256 * m₁ := by omega
    calc s * (t * k) ≤ (128 * s₁) * (256 * m₁) := Nat.mul_le_mul hs₁b e1
      _ = 32768 * (s₁ * m₁) := by ring
  set δ := s₁ * m₁ / (4 * a) with hδ
  have hδ1 : δ * (4 * a) ≤ s₁ * m₁ := Nat.div_mul_le_self _ _
  have hδ2 : s₁ * m₁ < δ * (4 * a) + 4 * a := Nat.lt_div_mul_add (by omega)
  set h := s₁ * m₁ - 2 * a * δ with hh
  have hh1 : h + 2 * a * δ ≤ s₁ * m₁ := by
    have e1 : 2 * a * δ = 2 * (a * δ) := by ring
    have e2 : δ * (4 * a) = 4 * (a * δ) := by ring
    omega
  have hh2 : s * t * k ≤ 65536 * h := by
    have e1 : 2 * a * δ = 2 * (a * δ) := by ring
    have e2 : δ * (4 * a) = 4 * (a * δ) := by ring
    have e : s * t * k = s * (t * k) := by ring
    omega
  have hδ3 : s * t * k < 262144 * (a * δ) := by
    have e1 : s * t * k < 131072 * (a * (δ + 1)) := by
      have e : s * t * k = s * (t * k) := by ring
      have : 32768 * (s₁ * m₁) < 32768 * (δ * (4 * a) + 4 * a) := by omega
      have e2 : 32768 * (δ * (4 * a) + 4 * a) = 131072 * (a * (δ + 1)) := by ring
      omega
    have e2 : 8 ≤ δ := by
      by_contra hc; push_neg at hc
      have : a * (δ + 1) ≤ a * 8 := Nat.mul_le_mul_left _ (by omega)
      omega
    have e3 : a * (δ + 1) ≤ 2 * (a * δ) := by
      have : a * (δ + 1) = a * δ + a := by ring
      have : a ≤ a * δ := Nat.le_mul_of_pos_right a (by omega)
      omega
    omega
  -- `hδ` lower bound: 2^34 a (h δ) ≥ (s t k)^2
  have hhd : (s * t * k) ^ 2 ≤ 2 ^ 34 * a * (h * δ) := by
    have := Nat.mul_le_mul hh2 hδ3.le
    calc (s * t * k) ^ 2 = (s * t * k) * (s * t * k) := by ring
      _ ≤ 65536 * h * (262144 * (a * δ)) := this
      _ = 2 ^ 34 * a * (h * δ) := by ring
  set e := Nat.sqrt (t * k) + 1 with he
  obtain ⟨he1, he2⟩ := sqrt_succ_bounds (t * k) (by omega)
  set φ := β / q + 1 with hφ
  have hφ1 : β ≤ q * φ := by
    have := Nat.lt_div_mul_add (a := β) (show 0 < q from hq5)
    have e : q * (β / q + 1) = β / q * q + q := by ring
    rw [hφ, e]; omega
  set e' := Nat.sqrt (s * φ) + 1 with he'
  obtain ⟨he'1, he'2⟩ := sqrt_succ_bounds (s * φ) (by
    have : 1 ≤ φ := by rw [hφ]; exact Nat.le_add_left 1 _
    exact Nat.mul_le_mul (by omega : 1 ≤ s) this)
  refine ⟨j₀, q, β, s₁, m₁, δ, h, e, φ, e', hβ1, by omega, ?_, hh1, he1, ?_, hφ1, he'1, ?_, ?_⟩
  · -- m₁ + k (q j₀) ≤ t k / 64
    exact hm₁a
  · -- hcol
    apply sq_lt_imp_lt
    have hpos : 0 < a ^ 2 * s ^ 2 * t * k ^ 3 := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos ha0 2) (pow_pos hs0 2)) ht0) (pow_pos hk0 3)
    have e1 : (2 * e * a * s * k) ^ 2 ≤ 16 * (a ^ 2 * s ^ 2 * t * k ^ 3) := by
      calc (2 * e * a * s * k) ^ 2 = 4 * (e ^ 2) * (a ^ 2 * s ^ 2 * k ^ 2) := by ring
        _ ≤ 4 * (4 * (t * k)) * (a ^ 2 * s ^ 2 * k ^ 2) := by gcongr
        _ = 16 * (a ^ 2 * s ^ 2 * t * k ^ 3) := by ring
    have e2 : (s * t * k) ^ 4 ≤ 2 ^ 68 * a ^ 2 * (h * δ) ^ 2 := by
      have := Nat.pow_le_pow_left hhd 2
      calc (s * t * k) ^ 4 = ((s * t * k) ^ 2) ^ 2 := by ring
        _ ≤ (2 ^ 34 * a * (h * δ)) ^ 2 := this
        _ = 2 ^ 68 * a ^ 2 * (h * δ) ^ 2 := by ring
    have e3 : 2 ^ 73 * a ^ 4 * (s ^ 2 * t * k ^ 3) ≤ (s * t * k) ^ 4 := by
      calc 2 ^ 73 * a ^ 4 * (s ^ 2 * t * k ^ 3) ≤ (s ^ 2 * t ^ 3 * k) * (s ^ 2 * t * k ^ 3) :=
            Nat.mul_le_mul_right _ c3
        _ = (s * t * k) ^ 4 := by ring
    -- 2^73 a^4 X ≤ 2^68 a^2 (hδ)^2, so 32 a^2 X ≤ (hδ)^2
    have e4 : 32 * (a ^ 2 * (s ^ 2 * t * k ^ 3)) ≤ (h * δ) ^ 2 := by
      have e5 : 2 ^ 68 * a ^ 2 * (32 * (a ^ 2 * (s ^ 2 * t * k ^ 3))) ≤
          2 ^ 68 * a ^ 2 * (h * δ) ^ 2 := by
        calc 2 ^ 68 * a ^ 2 * (32 * (a ^ 2 * (s ^ 2 * t * k ^ 3)))
            = 2 ^ 73 * a ^ 4 * (s ^ 2 * t * k ^ 3) := by ring
          _ ≤ _ := e3.trans e2
      exact Nat.le_of_mul_le_mul_left e5 (Nat.mul_pos (by norm_num) (pow_pos ha0 2))
    have e6 : 16 * (a ^ 2 * s ^ 2 * t * k ^ 3) < 32 * (a ^ 2 * (s ^ 2 * t * k ^ 3)) := by
      have : a ^ 2 * s ^ 2 * t * k ^ 3 = a ^ 2 * (s ^ 2 * t * k ^ 3) := by ring
      omega
    omega
  · -- 2 β ≤ δ
    have e1 : β * s ≤ 256 * a + 128 * s := by
      have : s ≤ 256 * j₀ := by omega
      calc β * s ≤ β * (256 * j₀) := Nat.mul_le_mul_left _ this
        _ = 256 * ((a / j₀) * j₀) + 256 * j₀ := by rw [hβ]; ring
        _ ≤ 256 * a + 128 * s := by omega
    -- s^2 t k < 2^18 s a δ   and   s t k < 2^18 a δ
    have e2 : s * (s * t * k) < s * (262144 * (a * δ)) := Nat.mul_lt_mul_of_pos_left hδ3 (by omega)
    have e3 : 2 ^ 28 * a ^ 2 < 262144 * (a * (s * δ)) := by
      calc 2 ^ 28 * a ^ 2 ≤ s ^ 2 * t * k := c2
        _ = s * (s * t * k) := by ring
        _ < s * (262144 * (a * δ)) := e2
        _ = 262144 * (a * (s * δ)) := by ring
    have e4 : 1024 * a < s * δ := by
      have : 262144 * (a * (1024 * a)) < 262144 * (a * (s * δ)) := by
        calc 262144 * (a * (1024 * a)) = 2 ^ 28 * a ^ 2 := by ring
          _ < _ := e3
      have := Nat.lt_of_mul_lt_mul_left this
      exact Nat.lt_of_mul_lt_mul_left this
    have e5 : 4 ≤ δ := by
      by_contra hc; push_neg at hc
      have : a * δ ≤ a * 3 := Nat.mul_le_mul_left _ (by omega)
      omega
    -- 2 β s ≤ 512 a + 256 s ≤ s δ
    have e6 : 2 * β * s ≤ s * δ := by
      have : 256 * s ≤ s * δ / 2 + s * δ / 2 := by
        have : s * 4 ≤ s * δ := Nat.mul_le_mul_left _ e5
        omega
      have : 2 * β * s = 2 * (β * s) := by ring
      omega
    have : s * (2 * β) ≤ s * δ := by
      calc s * (2 * β) = 2 * β * s := by ring
        _ ≤ s * δ := e6
    exact Nat.le_of_mul_le_mul_left this (by omega)
  · -- hrow
    apply sq_lt_imp_lt
    -- φ t ≤ 2^17 a
    have hφt : φ * t ≤ 131072 * a := by
      have e1 : (β / q) * q ≤ β := Nat.div_mul_le_self β q
      have e2 : β * s ≤ 256 * a + 128 * s := by
        have : s ≤ 256 * j₀ := by omega
        calc β * s ≤ β * (256 * j₀) := Nat.mul_le_mul_left _ this
          _ = 256 * ((a / j₀) * j₀) + 256 * j₀ := by rw [hβ]; ring
          _ ≤ 256 * a + 128 * s := by omega
      -- (β/q) t < (β/q) 256 s q ≤ 256 s β
      have e3 : (β / q) * t ≤ 256 * (β * s) := by
        calc (β / q) * t ≤ (β / q) * (256 * s * q) := Nat.mul_le_mul_left _ hq4.le
          _ = 256 * s * ((β / q) * q) := by ring
          _ ≤ 256 * s * β := Nat.mul_le_mul_left _ e1
          _ = 256 * (β * s) := by ring
      have e4 : 32768 * s ≤ 32 * t := by omega
      have e5 : φ * t = (β / q) * t + t := by rw [hφ]; ring
      omega
    have e1 : (4 * (t * k) * e' * a) ^ 2 ≤ 64 * 131072 * (a ^ 3 * s * t * k ^ 2) := by
      calc (4 * (t * k) * e' * a) ^ 2 = 16 * (t * k) ^ 2 * a ^ 2 * e' ^ 2 := by ring
        _ ≤ 16 * (t * k) ^ 2 * a ^ 2 * (4 * (s * φ)) := by gcongr
        _ = 64 * (a ^ 2 * s * t * k ^ 2) * (φ * t) := by ring
        _ ≤ 64 * (a ^ 2 * s * t * k ^ 2) * (131072 * a) := Nat.mul_le_mul_left _ hφt
        _ = 64 * 131072 * (a ^ 3 * s * t * k ^ 2) := by ring
    have e2 : (s * t * k) ^ 4 ≤ 2 ^ 68 * a ^ 2 * (h * δ) ^ 2 := by
      have := Nat.pow_le_pow_left hhd 2
      calc (s * t * k) ^ 4 = ((s * t * k) ^ 2) ^ 2 := by ring
        _ ≤ (2 ^ 34 * a * (h * δ)) ^ 2 := this
        _ = 2 ^ 68 * a ^ 2 * (h * δ) ^ 2 := by ring
    have e3 : 2 ^ 92 * a ^ 5 * (a ^ 0 * s * t * k ^ 2) ≤ (s * t * k) ^ 4 := by
      calc 2 ^ 92 * a ^ 5 * (a ^ 0 * s * t * k ^ 2) ≤ (s ^ 3 * t ^ 3 * k ^ 2) * (s * t * k ^ 2) := by
            rw [pow_zero, one_mul]; exact Nat.mul_le_mul_right _ c4
        _ = (s * t * k) ^ 4 := by ring
    have e4 : 2 ^ 24 * (a ^ 3 * s * t * k ^ 2) ≤ (h * δ) ^ 2 := by
      have e5 : 2 ^ 68 * a ^ 2 * (2 ^ 24 * (a ^ 3 * s * t * k ^ 2)) ≤
          2 ^ 68 * a ^ 2 * (h * δ) ^ 2 := by
        calc 2 ^ 68 * a ^ 2 * (2 ^ 24 * (a ^ 3 * s * t * k ^ 2))
            = 2 ^ 92 * a ^ 5 * (a ^ 0 * s * t * k ^ 2) := by ring
          _ ≤ _ := e3.trans e2
      exact Nat.le_of_mul_le_mul_left e5 (Nat.mul_pos (by norm_num) (pow_pos ha0 2))
    have hpos : 0 < a ^ 3 * s * t * k ^ 2 := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos ha0 3) hs0) ht0) (pow_pos hk0 2)
    have : 64 * 131072 * (a ^ 3 * s * t * k ^ 2) < 2 ^ 24 * (a ^ 3 * s * t * k ^ 2) := by
      have : (64 * 131072 : ℕ) < 2 ^ 24 := by norm_num
      exact Nat.mul_lt_mul_of_pos_right this hpos
    omega

end E813

end S_N1

-- ===== N2 =====
section S_N2

/-! Regime selection for Claim 2 (original). -/

namespace E813

/-- If `P ≤ s t²` with `P` large, then the star at hand is in one of the two regimes. -/
lemma regime_ok (a s t x : ℕ) (P : ℝ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hta : t < a) (hx : 1 ≤ x)
    (hP : P ≤ (s : ℝ) * t ^ 2)
    (H1 : 2000 * (a : ℝ) ^ 3 ≤ P * x ^ 2) (H2 : 2 ^ 34 * (a : ℝ) ^ 6 ≤ P ^ 2 * x ^ 3)
    (H3 : 2 ^ 73 * (a : ℝ) ^ 5 ≤ P ^ 2 * x) (H4 : 2 ^ 92 * (a : ℝ) ^ 8 ≤ P ^ 3 * x ^ 2)
    (H5 : 256 * (a : ℝ) ^ 2 ≤ P) (H6 : 2 ^ 20 * (a : ℝ) ^ 2 ≤ P * x) :
    648 * a ^ 3 ≤ s * t ^ 2 * x ^ 2 ∧
      (210 * a * a ≤ s * t * x ∨ (12 * s ≤ t ∧ 8 * a ≤ t * x ∧ GridOK a s t x)) := by
  have hA : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hT : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hS : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hX : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hX0 : (0 : ℝ) < x := by linarith
  have hTA : (t : ℝ) ≤ a := by exact_mod_cast hta.le
  have hP0 : 0 ≤ P := le_trans (by positivity) H5
  set Q : ℝ := (s : ℝ) * t ^ 2 with hQ
  have hQ2 : P ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ hP0 hP 2
  have hQ3 : P ^ 3 ≤ Q ^ 3 := pow_le_pow_left₀ hP0 hP 3
  refine ⟨?_, ?_⟩
  · have : (648 : ℝ) * a ^ 3 ≤ s * t ^ 2 * x ^ 2 := by
      have : P * x ^ 2 ≤ Q * x ^ 2 := by gcongr
      nlinarith
    exact_mod_cast this
  by_cases hreg : 210 * a * a ≤ s * t * x
  · exact Or.inl hreg
  right
  push_neg at hreg
  have hreg' : (s : ℝ) * t * x < 210 * a ^ 2 := by
    have : ((s * t * x : ℕ) : ℝ) < ((210 * a * a : ℕ) : ℝ) := by exact_mod_cast hreg
    push_cast at this; nlinarith
  -- t > P x / (210 a²)
  have ht1 : P * x < t * (210 * a ^ 2) := by
    calc P * x ≤ Q * x := by gcongr
      _ = t * (s * t * x) := by rw [hQ]; ring
      _ < t * (210 * a ^ 2) := by gcongr
  have ht2 : (P * x) ^ 2 * x < (t * (210 * a ^ 2)) ^ 2 * x := by
    have : 0 ≤ P * x := by positivity
    gcongr
  have hB1r : 1024 * (s : ℝ) ≤ t := by
    have e1 : 2 ^ 34 * (a : ℝ) ^ 6 < (a : ℝ) ^ 4 * (210 ^ 2 * (t ^ 2 * x)) := by
      calc 2 ^ 34 * (a : ℝ) ^ 6 ≤ P ^ 2 * x ^ 3 := H2
        _ = (P * x) ^ 2 * x := by ring
        _ < (t * (210 * a ^ 2)) ^ 2 * x := ht2
        _ = (a : ℝ) ^ 4 * (210 ^ 2 * (t ^ 2 * x)) := by ring
    have e2 : (a : ℝ) ^ 4 * (210 ^ 2 * (1024 * 210 * a ^ 2)) ≤ 2 ^ 34 * (a : ℝ) ^ 6 := by
      have : (a : ℝ) ^ 4 * (210 ^ 2 * (1024 * 210 * a ^ 2)) = (210 ^ 3 * 1024) * a ^ 6 := by ring
      rw [this]; gcongr; norm_num
    have e3 : 210 ^ 2 * (1024 * 210 * (a : ℝ) ^ 2) < 210 ^ 2 * (t ^ 2 * x) :=
      lt_of_mul_lt_mul_left (e2.trans_lt e1) (by positivity)
    have e4 : 1024 * 210 * (a : ℝ) ^ 2 < t ^ 2 * x := lt_of_mul_lt_mul_left e3 (by norm_num)
    have e5 : 1024 * (s : ℝ) * (t * x) ≤ t * (t * x) := by
      have : 1024 * (s : ℝ) * (t * x) = 1024 * (s * t * x) := by ring
      rw [this]
      nlinarith
    exact le_of_mul_le_mul_right e5 (by positivity)
  have hB1 : 1024 * s ≤ t := by exact_mod_cast hB1r
  -- 8 a ≤ t x
  have hB2r : 8 * (a : ℝ) ≤ t * x := by
    have e1 : P * x ^ 2 < (t * x) * (210 * a ^ 2) := by
      calc P * x ^ 2 = (P * x) * x := by ring
        _ < (t * (210 * a ^ 2)) * x := by gcongr
        _ = (t * x) * (210 * a ^ 2) := by ring
    have e2 : 8 * (a : ℝ) * (210 * a ^ 2) ≤ P * x ^ 2 := by
      have : 8 * (a : ℝ) * (210 * a ^ 2) = 1680 * a ^ 3 := by ring
      rw [this]; nlinarith [pow_pos hA 3]
    exact le_of_lt (lt_of_mul_lt_mul_right (e2.trans_lt e1) (by positivity))
  have hB2 : 8 * a ≤ t * x := by exact_mod_cast hB2r
  refine ⟨by omega, hB2, ?_⟩
  -- grid parameters
  have hs256 : 256 ≤ s := by
    have e1 : 256 * (a : ℝ) ^ 2 ≤ s * t ^ 2 := H5.trans hP
    have e2 : (s : ℝ) * t ^ 2 ≤ s * a ^ 2 := by gcongr
    have e3 : 256 * (a : ℝ) ^ 2 ≤ s * a ^ 2 := e1.trans e2
    have : (256 : ℝ) ≤ s := le_of_mul_le_mul_right e3 (pow_pos hA 2)
    exact_mod_cast this
  have hstx : (0 : ℝ) ≤ s * t * x := by positivity
  have c1 : 2 ^ 20 * a ≤ s * t * x := by
    have e : 2 ^ 20 * (a : ℝ) ^ 2 ≤ a * (s * t * x) := by
      calc 2 ^ 20 * (a : ℝ) ^ 2 ≤ P * x := H6
        _ ≤ Q * x := by gcongr
        _ = t * (s * t * x) := by rw [hQ]; ring
        _ ≤ a * (s * t * x) := by gcongr
    have e' : (a : ℝ) * (2 ^ 20 * a) ≤ a * (s * t * x) := by
      have : (a : ℝ) * (2 ^ 20 * a) = 2 ^ 20 * a ^ 2 := by ring
      linarith
    have : 2 ^ 20 * (a : ℝ) ≤ s * t * x := le_of_mul_le_mul_left e' hA
    exact_mod_cast this
  have c2 : 2 ^ 28 * a ^ 2 ≤ s ^ 2 * t * x := by
    have e : (a : ℝ) ^ 3 * (2 ^ 28 * a ^ 2) ≤ a ^ 3 * (s ^ 2 * t * x) := by
      calc (a : ℝ) ^ 3 * (2 ^ 28 * a ^ 2) = 2 ^ 28 * (a : ℝ) ^ 5 := by ring
        _ ≤ 2 ^ 73 * (a : ℝ) ^ 5 := by gcongr <;> norm_num
        _ ≤ P ^ 2 * x := H3
        _ ≤ Q ^ 2 * x := by gcongr
        _ = t ^ 3 * (s ^ 2 * t * x) := by rw [hQ]; ring
        _ ≤ a ^ 3 * (s ^ 2 * t * x) := by gcongr
    have : 2 ^ 28 * (a : ℝ) ^ 2 ≤ s ^ 2 * t * x := le_of_mul_le_mul_left e (pow_pos hA 3)
    exact_mod_cast this
  have c3 : 2 ^ 73 * a ^ 4 ≤ s ^ 2 * t ^ 3 * x := by
    have e : (a : ℝ) * (2 ^ 73 * a ^ 4) ≤ a * (s ^ 2 * t ^ 3 * x) := by
      calc (a : ℝ) * (2 ^ 73 * a ^ 4) = 2 ^ 73 * (a : ℝ) ^ 5 := by ring
        _ ≤ P ^ 2 * x := H3
        _ ≤ Q ^ 2 * x := by gcongr
        _ = t * (s ^ 2 * t ^ 3 * x) := by rw [hQ]; ring
        _ ≤ a * (s ^ 2 * t ^ 3 * x) := by gcongr
    have : 2 ^ 73 * (a : ℝ) ^ 4 ≤ s ^ 2 * t ^ 3 * x := le_of_mul_le_mul_left e hA
    exact_mod_cast this
  have c4 : 2 ^ 92 * a ^ 5 ≤ s ^ 3 * t ^ 3 * x ^ 2 := by
    have e : (a : ℝ) ^ 3 * (2 ^ 92 * a ^ 5) ≤ a ^ 3 * (s ^ 3 * t ^ 3 * x ^ 2) := by
      calc (a : ℝ) ^ 3 * (2 ^ 92 * a ^ 5) = 2 ^ 92 * (a : ℝ) ^ 8 := by ring
        _ ≤ P ^ 3 * x ^ 2 := H4
        _ ≤ Q ^ 3 * x ^ 2 := by gcongr
        _ = t ^ 3 * (s ^ 3 * t ^ 3 * x ^ 2) := by rw [hQ]; ring
        _ ≤ a ^ 3 * (s ^ 3 * t ^ 3 * x ^ 2) := by gcongr
    have : 2 ^ 92 * (a : ℝ) ^ 5 ≤ s ^ 3 * t ^ 3 * x ^ 2 := le_of_mul_le_mul_left e (pow_pos hA 3)
    exact_mod_cast this
  exact grid_ok a s t x (by omega) hs256 hB1 hta.le hx c1 c2 c3 c4

end E813

end S_N2

-- ===== N3 =====
section S_N3

/-! The final numerical contradiction (original). -/

namespace E813

/-- constant in the bound for `P` -/
def cP : ℝ := 64 ^ 4 * 5529600

set_option maxHeartbeats 2000000 in
lemma final_contra (n a x L T Dsum E m₁ m₂ : ℕ)
    (Fa : m₁ * n ≤ E + a * m₁ ^ 2) (Fb : E ≤ Dsum + n * (a * (x + 1)))
    (Fc : m₂ * (x * x) * Dsum ≤ 9 * T + n * (9 * (a * a * m₂ ^ 2) + 210 * a * a * m₂))
    (Fd : (∀ s t : ℕ, 1 ≤ s → 1 ≤ t → t < a → T ≤ 16 * n * L * (s * t ^ 2) →
      648 * a ^ 3 ≤ s * t ^ 2 * x ^ 2 ∧
      (210 * a * a ≤ s * t * x ∨ (12 * s ≤ t ∧ 8 * a ≤ t * x ∧ GridOK a s t x))) →
      7 * x ^ 4 * T ≤ n * (2 * C0 * L ^ 2 * a ^ 4 + 7 * x ^ 4))
    (ha : 1 ≤ a) (hL : 1 ≤ L) (hx : 1 ≤ x)
    (hm1a : 2 * a * m₁ ≤ n) (hm1b : n ≤ 4 * a * m₁)
    (hx1 : 16 * a ^ 2 * (x + 1) ≤ n) (hx2 : n ≤ 64 * a ^ 2 * x)
    (hm2a : 600 * a ^ 3 * m₂ ≤ x ^ 2 * n) (hm2b : x ^ 2 * n ≤ 1200 * a ^ 3 * m₂)
    (hc : 13440 * a ^ 3 ≤ x ^ 2 * n)
    (H1 : 2000 * cP * 64 ^ 2 * L * (a : ℝ) ^ 19 ≤ (n : ℝ) ^ 8)
    (H2 : 2 ^ 34 * cP ^ 2 * 64 ^ 3 * L ^ 2 * (a : ℝ) ^ 36 ≤ (n : ℝ) ^ 15)
    (H3 : 2 ^ 73 * cP ^ 2 * 64 * L ^ 2 * (a : ℝ) ^ 31 ≤ (n : ℝ) ^ 13)
    (H4 : 2 ^ 92 * cP ^ 3 * 64 ^ 2 * L ^ 3 * (a : ℝ) ^ 48 ≤ (n : ℝ) ^ 20)
    (H5 : 256 * cP * L * (a : ℝ) ^ 14 ≤ (n : ℝ) ^ 6)
    (H6 : 2 ^ 20 * cP * 64 * L * (a : ℝ) ^ 16 ≤ (n : ℝ) ^ 7)
    (F1 : 4 * (C0 : ℝ) * 345600 * 64 ^ 8 * L ^ 2 * (a : ℝ) ^ 24 < 7 * (n : ℝ) ^ 10)
    (F2 : 2 * 345600 * 64 ^ 4 * (a : ℝ) ^ 12 < (n : ℝ) ^ 6) : False := by
  -- real versions
  have hA : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hXr : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hX0 : (0 : ℝ) < x := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (by omega) 2)) (Nat.succ_pos x)) hx1
  have hN : (0 : ℝ) < n := by exact_mod_cast hn0
  have rFa : (m₁ : ℝ) * n ≤ E + a * m₁ ^ 2 := by exact_mod_cast Fa
  have rFb : (E : ℝ) ≤ Dsum + n * (a * (x + 1)) := by exact_mod_cast Fb
  have rFc : (m₂ : ℝ) * (x * x) * Dsum ≤ 9 * T + n * (9 * (a * a * m₂ ^ 2) + 210 * a * a * m₂) := by
    exact_mod_cast Fc
  have r1a : 2 * (a : ℝ) * m₁ ≤ n := by exact_mod_cast hm1a
  have r1b : (n : ℝ) ≤ 4 * a * m₁ := by exact_mod_cast hm1b
  have rx1 : 16 * (a : ℝ) ^ 2 * (x + 1) ≤ n := by exact_mod_cast hx1
  have rx2 : (n : ℝ) ≤ 64 * a ^ 2 * x := by exact_mod_cast hx2
  have r2a : 600 * (a : ℝ) ^ 3 * m₂ ≤ x ^ 2 * n := by exact_mod_cast hm2a
  have r2b : (x : ℝ) ^ 2 * n ≤ 1200 * a ^ 3 * m₂ := by exact_mod_cast hm2b
  have rc : 13440 * (a : ℝ) ^ 3 ≤ x ^ 2 * n := by exact_mod_cast hc
  have hM1 : (0 : ℝ) ≤ m₁ := by positivity
  have hM2 : (0 : ℝ) ≤ m₂ := by positivity
  have hDs : (0 : ℝ) ≤ Dsum := by positivity
  have hn' : (0 : ℝ) ≤ n := hN.le
  have s1 : (m₁ : ℝ) * n ≤ 2 * E := by
    have := mul_le_mul_of_nonneg_left r1a hM1
    nlinarith [this]
  have s2 : (n : ℝ) ^ 2 ≤ 8 * a * E := by
    have h1 := mul_le_mul_of_nonneg_left r1b hn'
    have h2 := mul_le_mul_of_nonneg_left s1 (show (0 : ℝ) ≤ 4 * a by positivity)
    linarith
  have s3 : (n : ℝ) ^ 2 ≤ 16 * a * Dsum := by
    have h1 := mul_le_mul_of_nonneg_left rx1 hn'
    have h2 := mul_le_mul_of_nonneg_left rFb (show (0 : ℝ) ≤ 16 * a by positivity)
    linarith
  have s4 : 100 * (9 * n * a ^ 2 * m₂ : ℝ) ≤ 24 * (x ^ 2 * Dsum) := by
    have e1 := mul_le_mul_of_nonneg_left r2a (show (0 : ℝ) ≤ 9 * n by positivity)
    have e2 : 9 * (x : ℝ) ^ 2 * n ^ 2 ≤ 9 * x ^ 2 * (16 * a * Dsum) := by gcongr
    have e3 : (a : ℝ) * (600 * (9 * n * a ^ 2 * m₂)) ≤ a * (144 * (x ^ 2 * Dsum)) := by linarith
    have := le_of_mul_le_mul_left e3 hA
    linarith
  have s5 : 4 * (210 * n * (a : ℝ) ^ 2) ≤ x ^ 2 * Dsum := by
    have e1 : 13440 * (a : ℝ) ^ 3 * n ≤ x ^ 2 * n * n := by gcongr
    have e2 : (x : ℝ) ^ 2 * n ^ 2 ≤ x ^ 2 * (16 * a * Dsum) := by gcongr
    have e3 : (16 * (a : ℝ)) * (4 * (210 * n * a ^ 2)) ≤ (16 * a) * (x ^ 2 * Dsum) := by linarith
    exact le_of_mul_le_mul_left e3 (by positivity)
  have s6 : (m₂ : ℝ) * (x ^ 2 * Dsum) ≤ 18 * T := by
    have e3 : (m₂ : ℝ) * (9 * n * a ^ 2 * m₂) ≤ m₂ * (24 / 100 * (x ^ 2 * Dsum)) :=
      mul_le_mul_of_nonneg_left (by linarith) hM2
    have e4 : (m₂ : ℝ) * (210 * n * a ^ 2) ≤ m₂ * (1 / 4 * (x ^ 2 * Dsum)) :=
      mul_le_mul_of_nonneg_left (by linarith) hM2
    linarith
  have s7 : (x : ℝ) ^ 4 * n ^ 3 ≤ 345600 * a ^ 4 * T := by
    have e1 : (x : ℝ) ^ 2 * n * (x ^ 2 * n ^ 2) ≤ (1200 * a ^ 3 * m₂) * (x ^ 2 * (16 * a * Dsum)) := by
      apply mul_le_mul r2b _ (by positivity) (by positivity)
      gcongr
    have e3 : 19200 * (a : ℝ) ^ 4 * (m₂ * (x ^ 2 * Dsum)) ≤ 19200 * a ^ 4 * (18 * T) := by gcongr
    linarith
  -- the oracle
  set P : ℝ := (x : ℝ) ^ 4 * n ^ 2 / (5529600 * L * a ^ 4) with hP
  have hy : (n : ℝ) / (64 * a ^ 2) ≤ x := by
    rw [div_le_iff₀ (by positivity)]; linarith
  set y : ℝ := (n : ℝ) / (64 * a ^ 2) with hydef
  have hy0 : 0 < y := by positivity
  set P0 : ℝ := n ^ 6 / (cP * L * a ^ 12) with hP0
  have hPP0 : P0 ≤ P := by
    have e1 : y ^ 4 ≤ (x : ℝ) ^ 4 := by gcongr
    have e2 : P0 = y ^ 4 * n ^ 2 / (5529600 * L * a ^ 4) := by
      rw [hP0, hydef, cP]; field_simp; try ring
    rw [e2, hP]; gcongr
  have hcP : (0 : ℝ) < cP := by unfold cP; norm_num
  have hP00 : 0 < P0 := by positivity
  -- helper: from a monomial bound to a bound with P0 and y
  have hreg : ∀ s t : ℕ, 1 ≤ s → 1 ≤ t → t < a → T ≤ 16 * n * L * (s * t ^ 2) →
      648 * a ^ 3 ≤ s * t ^ 2 * x ^ 2 ∧
      (210 * a * a ≤ s * t * x ∨ (12 * s ≤ t ∧ 8 * a ≤ t * x ∧ GridOK a s t x)) := by
    intro s t hs ht hta hT
    have hTr : (T : ℝ) ≤ 16 * n * L * (s * t ^ 2) := by exact_mod_cast hT
    have hPst : P ≤ (s : ℝ) * t ^ 2 := by
      rw [hP, div_le_iff₀ (by positivity)]
      have : (x : ℝ) ^ 4 * n ^ 3 ≤ 345600 * a ^ 4 * (16 * n * L * (s * t ^ 2)) := by
        have := mul_le_mul_of_nonneg_left hTr (show (0 : ℝ) ≤ 345600 * a ^ 4 by positivity)
        linarith
      have e : (345600 : ℝ) * a ^ 4 * (16 * n * L * (s * t ^ 2)) =
          n * ((s * t ^ 2) * (5529600 * L * a ^ 4)) := by ring
      rw [e] at this
      have : (n : ℝ) * (x ^ 4 * n ^ 2) ≤ n * ((s * t ^ 2) * (5529600 * L * a ^ 4)) := by
        have e2 : (x : ℝ) ^ 4 * n ^ 3 = n * (x ^ 4 * n ^ 2) := by ring
        linarith
      exact le_of_mul_le_mul_left this hN
    have hyx := hy
    refine regime_ok a s t x P hs ht hta hx hPst ?_ ?_ ?_ ?_ ?_ ?_
    · have k : P0 * y ^ 2 = n ^ 8 / (cP * 64 ^ 2 * L * a ^ 16) := by
        rw [hP0, hydef]; field_simp; try ring
      calc 2000 * (a : ℝ) ^ 3 ≤ P0 * y ^ 2 := by
            rw [k, le_div_iff₀ (by positivity)]
            have : 2000 * (a : ℝ) ^ 3 * (cP * 64 ^ 2 * L * a ^ 16) =
              2000 * cP * 64 ^ 2 * L * a ^ 19 := by ring
            linarith
        _ ≤ P * x ^ 2 := by gcongr
    · have k : P0 ^ 2 * y ^ 3 = n ^ 15 / (cP ^ 2 * 64 ^ 3 * L ^ 2 * a ^ 30) := by
        rw [hP0, hydef]; field_simp; try ring
      calc 2 ^ 34 * (a : ℝ) ^ 6 ≤ P0 ^ 2 * y ^ 3 := by
            rw [k, le_div_iff₀ (by positivity)]
            have : 2 ^ 34 * (a : ℝ) ^ 6 * (cP ^ 2 * 64 ^ 3 * L ^ 2 * a ^ 30) =
              2 ^ 34 * cP ^ 2 * 64 ^ 3 * L ^ 2 * a ^ 36 := by ring
            linarith
        _ ≤ P ^ 2 * x ^ 3 := by gcongr
    · have k : P0 ^ 2 * y = n ^ 13 / (cP ^ 2 * 64 * L ^ 2 * a ^ 26) := by
        rw [hP0, hydef]; field_simp; try ring
      calc 2 ^ 73 * (a : ℝ) ^ 5 ≤ P0 ^ 2 * y := by
            rw [k, le_div_iff₀ (by positivity)]
            have : 2 ^ 73 * (a : ℝ) ^ 5 * (cP ^ 2 * 64 * L ^ 2 * a ^ 26) =
              2 ^ 73 * cP ^ 2 * 64 * L ^ 2 * a ^ 31 := by ring
            linarith
        _ ≤ P ^ 2 * x := by gcongr
    · have k : P0 ^ 3 * y ^ 2 = n ^ 20 / (cP ^ 3 * 64 ^ 2 * L ^ 3 * a ^ 40) := by
        rw [hP0, hydef]; field_simp; try ring
      calc 2 ^ 92 * (a : ℝ) ^ 8 ≤ P0 ^ 3 * y ^ 2 := by
            rw [k, le_div_iff₀ (by positivity)]
            have : 2 ^ 92 * (a : ℝ) ^ 8 * (cP ^ 3 * 64 ^ 2 * L ^ 3 * a ^ 40) =
              2 ^ 92 * cP ^ 3 * 64 ^ 2 * L ^ 3 * a ^ 48 := by ring
            linarith
        _ ≤ P ^ 3 * x ^ 2 := by gcongr
    · calc 256 * (a : ℝ) ^ 2 ≤ P0 := by
            rw [hP0, le_div_iff₀ (by positivity)]
            have : 256 * (a : ℝ) ^ 2 * (cP * L * a ^ 12) = 256 * cP * L * a ^ 14 := by ring
            linarith
        _ ≤ P := hPP0
    · have k : P0 * y = n ^ 7 / (cP * 64 * L * a ^ 14) := by
        rw [hP0, hydef]; field_simp; try ring
      calc 2 ^ 20 * (a : ℝ) ^ 2 ≤ P0 * y := by
            rw [k, le_div_iff₀ (by positivity)]
            have : 2 ^ 20 * (a : ℝ) ^ 2 * (cP * 64 * L * a ^ 14) =
              2 ^ 20 * cP * 64 * L * a ^ 16 := by ring
            linarith
        _ ≤ P * x := by gcongr
  have hFd := Fd hreg
  have rFd : 7 * (x : ℝ) ^ 4 * T ≤ n * (2 * C0 * L ^ 2 * a ^ 4 + 7 * x ^ 4) := by
    exact_mod_cast hFd
  -- combine with s7
  have e1 : 7 * (x : ℝ) ^ 8 * n ^ 3 ≤ 345600 * a ^ 4 * (n * (2 * C0 * L ^ 2 * a ^ 4 + 7 * x ^ 4)) := by
    have := mul_le_mul_of_nonneg_left s7 (show (0 : ℝ) ≤ 7 * x ^ 4 by positivity)
    have h2 := mul_le_mul_of_nonneg_left rFd (show (0 : ℝ) ≤ 345600 * a ^ 4 by positivity)
    linarith
  -- but 7 x⁸ n² > 345600 a⁴ (2 C0 L² a⁴ + 7 x⁴)
  have hy8 : y ^ 4 ≤ (x : ℝ) ^ 4 := by gcongr
  have e2 : 345600 * (a : ℝ) ^ 4 * (2 * C0 * L ^ 2 * a ^ 4) * 2 < 7 * x ^ 8 * n ^ 2 := by
    have k : y ^ 8 * n ^ 2 = n ^ 10 / (64 ^ 8 * a ^ 16) := by rw [hydef]; field_simp; try ring
    have : 345600 * (a : ℝ) ^ 4 * (2 * C0 * L ^ 2 * a ^ 4) * 2 < 7 * (y ^ 8 * n ^ 2) := by
      rw [k, mul_div_assoc', lt_div_iff₀ (by positivity)]
      have : 345600 * (a : ℝ) ^ 4 * (2 * C0 * L ^ 2 * a ^ 4) * 2 * (64 ^ 8 * a ^ 16) =
        4 * (C0 : ℝ) * 345600 * 64 ^ 8 * L ^ 2 * a ^ 24 := by ring
      linarith
    have : y ^ 8 ≤ (x : ℝ) ^ 8 := by gcongr
    have := mul_le_mul_of_nonneg_right this (show (0 : ℝ) ≤ n ^ 2 by positivity)
    linarith
  have e3 : 345600 * (a : ℝ) ^ 4 * (7 * x ^ 4) * 2 < 7 * x ^ 8 * n ^ 2 := by
    have : 345600 * (a : ℝ) ^ 4 * 2 < x ^ 4 * n ^ 2 := by
      have k : y ^ 4 * n ^ 2 = n ^ 6 / (64 ^ 4 * a ^ 8) := by rw [hydef]; field_simp; try ring
      have : 345600 * (a : ℝ) ^ 4 * 2 < y ^ 4 * n ^ 2 := by
        rw [k, lt_div_iff₀ (by positivity)]
        have : 345600 * (a : ℝ) ^ 4 * 2 * (64 ^ 4 * a ^ 8) = 2 * 345600 * 64 ^ 4 * a ^ 12 := by ring
        linarith
      have : y ^ 4 * (n : ℝ) ^ 2 ≤ x ^ 4 * n ^ 2 := by gcongr
      linarith
    have h4 : 0 < (x : ℝ) ^ 4 := by positivity
    have := mul_lt_mul_of_pos_left this (show (0 : ℝ) < 7 * x ^ 4 by positivity)
    linarith
  have e4 : 7 * (x : ℝ) ^ 8 * n ^ 3 = n * (7 * x ^ 8 * n ^ 2) := by ring
  have e5 : 345600 * (a : ℝ) ^ 4 * (n * (2 * C0 * L ^ 2 * a ^ 4 + 7 * x ^ 4)) =
      n * (345600 * a ^ 4 * (2 * C0 * L ^ 2 * a ^ 4) + 345600 * a ^ 4 * (7 * x ^ 4)) := by ring
  rw [e4, e5] at e1
  have := le_of_mul_le_mul_left e1 hN
  linarith

end E813

end S_N3

-- ===== N4 =====
section S_N4

/-! Asymptotic bookkeeping (original). -/

open Filter Real

namespace E813

lemma ev_log (K : ℝ) (hK : 0 ≤ K) (q : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, K * ((Nat.log 2 n : ℝ) + 1) ^ q ≤ (n : ℝ) ^ η := by
  have hc : (0 : ℝ) < 1 / (K * 3 ^ q + 1) := by positivity
  have hO := (isLittleO_log_rpow_rpow_atTop (q : ℝ) hη).bound hc
  have hreal : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x ∧
      ‖Real.log x ^ (q : ℝ)‖ ≤ 1 / (K * 3 ^ q + 1) * ‖x ^ η‖ ∧ 0 < x :=
    (Real.tendsto_log_atTop.eventually_ge_atTop 1).and (hO.and (eventually_gt_atTop 0))
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat] with n hn
  obtain ⟨h1, h2, h3⟩ := hn
  have hlog0 : 0 ≤ Real.log n := by linarith
  rw [Real.rpow_natCast, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)] at h2
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hnl : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
    have e1 := Real.natLog_le_logb n 2
    have e2 : Real.logb 2 n ≤ 2 * Real.log n := by
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith
    exact_mod_cast e1.trans e2
  have hb : (Nat.log 2 n : ℝ) + 1 ≤ 3 * Real.log n := by linarith
  calc K * ((Nat.log 2 n : ℝ) + 1) ^ q ≤ K * (3 * Real.log n) ^ q := by
        gcongr
    _ = K * 3 ^ q * Real.log n ^ q := by ring
    _ ≤ K * 3 ^ q * (1 / (K * 3 ^ q + 1) * (n : ℝ) ^ η) := by gcongr
    _ ≤ (n : ℝ) ^ η := by
        have hp : 0 ≤ (n : ℝ) ^ η := by positivity
        have : K * 3 ^ q * (1 / (K * 3 ^ q + 1)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith
        nlinarith

/-- monomial bounds hold eventually for `a = ⌈n^θ⌉`, `θ = 5/12 - ε` -/
lemma asym (ε : ℝ) (hε : 0 < ε) (hε' : ε < 5 / 12) (K : ℝ) (hK : 0 ≤ K) (q r p : ℕ)
    (hpr : 5 * r ≤ 12 * p) (hrpos : 1 ≤ r) :
    ∀ᶠ n : ℕ in atTop, K * (((Nat.log 2 ⌈(n : ℝ) ^ (5 / 12 - ε)⌉₊ + 1 : ℕ) : ℝ)) ^ q *
      ((⌈(n : ℝ) ^ (5 / 12 - ε)⌉₊ : ℕ) : ℝ) ^ r ≤ (n : ℝ) ^ p := by
  set θ := 5 / 12 - ε with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast hrpos
  filter_upwards [ev_log (K * 2 ^ r) (by positivity) q (ε * r) (by positivity),
    eventually_ge_atTop 1] with n hlog hn1
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow1 : 1 ≤ (n : ℝ) ^ θ := Real.one_le_rpow hn hθ0.le
  have hpow_le : (n : ℝ) ^ θ ≤ n := by
    calc (n : ℝ) ^ θ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
      _ = n := Real.rpow_one _
  set a := ⌈(n : ℝ) ^ θ⌉₊
  have ha1 : ((a : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ θ := by
    have := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ θ by positivity)
    linarith
  have han : a ≤ n := Nat.ceil_le.2 (by exact_mod_cast hpow_le)
  have hL : ((Nat.log 2 a + 1 : ℕ) : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by
    push_cast
    have := Nat.log_mono_right (b := 2) han
    exact_mod_cast (Nat.add_le_add_right this 1)
  have hL0 : (0 : ℝ) ≤ ((Nat.log 2 a + 1 : ℕ) : ℝ) := by positivity
  calc K * ((Nat.log 2 a + 1 : ℕ) : ℝ) ^ q * ((a : ℕ) : ℝ) ^ r
      ≤ K * ((Nat.log 2 n : ℝ) + 1) ^ q * (2 * (n : ℝ) ^ θ) ^ r := by gcongr
    _ = K * 2 ^ r * ((Nat.log 2 n : ℝ) + 1) ^ q * ((n : ℝ) ^ θ) ^ r := by ring
    _ ≤ (n : ℝ) ^ (ε * r) * ((n : ℝ) ^ θ) ^ r := by gcongr
    _ = (n : ℝ) ^ ((5 / 12 : ℝ) * r) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ θ) r, ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
        congr 1; rw [hθ]; ring
    _ ≤ (n : ℝ) ^ (p : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hn
        have : (5 : ℝ) * r ≤ 12 * p := by exact_mod_cast hpr
        linarith
    _ = (n : ℝ) ^ p := Real.rpow_natCast _ _

end E813

end S_N4

-- ===== W1 =====
section S_W1

/-! Main bound and the asymptotic statement (original). -/

open Finset

namespace E813

noncomputable section
open Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma k4free_of (hS7 : Seven3 G) {a : ℕ} (ha : IndLt G a) (hn : a * a + 4 ≤ Fintype.card V) :
    K4free G := by
  intro p q r s hpq hpr hps hqr hqs hrs
  set W := univ \ ({p, q, r, s} : Finset V)
  have hW : TriFree G W := by
    intro x hx y hy z hz hxy hxz hyz
    refine no_k4_tri hS7 hpq hpr hps hqr hqs hrs hxy hxz hyz ?_
    intro w hw
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
    · exact (mem_sdiff.1 hx).2 hw
    · exact (mem_sdiff.1 hy).2 hw
    · exact (mem_sdiff.1 hz).2 hw
  have h1 := trifree_card ha W hW
  have h2 : Fintype.card V ≤ W.card + 4 := by
    have : W.card + ({p, q, r, s} : Finset V).card = (univ : Finset V).card :=
      card_sdiff_add_card_eq_card (subset_univ ({p, q, r, s} : Finset V))
    have h4 : ({p, q, r, s} : Finset V).card ≤ 4 := by
      refine (card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
      exact Nat.succ_le_succ (card_le_two)
    rw [card_univ] at this
    omega
  omega

/-- the main bound in polynomial form -/
theorem main_bound (hS7 : Seven3 G) (a : ℕ) (ha : IndLt G a) (ha1 : 1 ≤ a)
    (hn1 : 128 * a ^ 2 ≤ Fintype.card V)
    (hc' : 13440 * 4096 * (a : ℝ) ^ 7 ≤ (Fintype.card V : ℝ) ^ 3)
    (H1 : 2000 * cP * 64 ^ 2 * (Nat.log 2 a + 1 : ℕ) * (a : ℝ) ^ 19 ≤ (Fintype.card V : ℝ) ^ 8)
    (H2 : 2 ^ 34 * cP ^ 2 * 64 ^ 3 * ((Nat.log 2 a + 1 : ℕ) : ℝ) ^ 2 * (a : ℝ) ^ 36 ≤
      (Fintype.card V : ℝ) ^ 15)
    (H3 : 2 ^ 73 * cP ^ 2 * 64 * ((Nat.log 2 a + 1 : ℕ) : ℝ) ^ 2 * (a : ℝ) ^ 31 ≤
      (Fintype.card V : ℝ) ^ 13)
    (H4 : 2 ^ 92 * cP ^ 3 * 64 ^ 2 * ((Nat.log 2 a + 1 : ℕ) : ℝ) ^ 3 * (a : ℝ) ^ 48 ≤
      (Fintype.card V : ℝ) ^ 20)
    (H5 : 256 * cP * (Nat.log 2 a + 1 : ℕ) * (a : ℝ) ^ 14 ≤ (Fintype.card V : ℝ) ^ 6)
    (H6 : 2 ^ 20 * cP * 64 * (Nat.log 2 a + 1 : ℕ) * (a : ℝ) ^ 16 ≤ (Fintype.card V : ℝ) ^ 7)
    (F1 : 4 * (C0 : ℝ) * 345600 * 64 ^ 8 * ((Nat.log 2 a + 1 : ℕ) : ℝ) ^ 2 * (a : ℝ) ^ 24 <
      7 * (Fintype.card V : ℝ) ^ 10)
    (F2 : 2 * 345600 * 64 ^ 4 * (a : ℝ) ^ 12 < (Fintype.card V : ℝ) ^ 6) : False := by
  set n := Fintype.card V with hn
  have ha0 : 0 < a := by omega
  have hsq : a ≤ a ^ 2 := Nat.le_self_pow (by norm_num) a
  have hK : K4free G := k4free_of hS7 ha (by
    have : a * a = a ^ 2 := by ring
    omega)
  set L := Nat.log 2 a + 1 with hLdef
  have hL : a ≤ 2 ^ L := (Nat.lt_pow_succ_log_self (by norm_num) a).le
  set x := n / (32 * a ^ 2) with hx
  obtain ⟨Fa, Fb, Fc, Fd⟩ := core hS7 hK ha x L hL (by omega)
  have ha2 : 0 < 32 * a ^ 2 := Nat.mul_pos (by norm_num) (pow_pos ha0 2)
  have hx1 : 32 * a ^ 2 * x ≤ n := Nat.mul_div_le n _
  have hx2 : n < x * (32 * a ^ 2) + 32 * a ^ 2 := Nat.lt_div_mul_add ha2
  have hx4 : 4 ≤ x := (Nat.le_div_iff_mul_le ha2).2 (by
    have : 4 * (32 * a ^ 2) = 128 * a ^ 2 := by ring
    omega)
  set m₁ := n / (2 * a) with hm₁
  have h2a : 0 < 2 * a := by omega
  have hm1a : 2 * a * m₁ ≤ n := Nat.mul_div_le n _
  have hm1c : n < m₁ * (2 * a) + 2 * a := Nat.lt_div_mul_add h2a
  have hm1d : 1 ≤ m₁ := (Nat.le_div_iff_mul_le h2a).2 (by omega)
  have hm1b : n ≤ 4 * a * m₁ := by
    have e1 : m₁ * (2 * a) = 2 * (a * m₁) := by ring
    have e2 : 4 * a * m₁ = 4 * (a * m₁) := by ring
    have e3 : a ≤ a * m₁ := Nat.le_mul_of_pos_right a hm1d
    omega
  have hxl : n ≤ 64 * a ^ 2 * x := by
    have e1 : x * (32 * a ^ 2) = 32 * (a ^ 2 * x) := by ring
    have e2 : 64 * a ^ 2 * x = 64 * (a ^ 2 * x) := by ring
    have e3 : a ^ 2 ≤ a ^ 2 * x := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hc : 13440 * a ^ 3 ≤ x ^ 2 * n := by
    have e1 : (n : ℝ) ≤ 64 * a ^ 2 * x := by exact_mod_cast hxl
    have hA : (0 : ℝ) < a := by exact_mod_cast ha0
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have e2 : (n : ℝ) ^ 2 ≤ (64 * a ^ 2 * x) ^ 2 := pow_le_pow_left₀ hn0 e1 2
    have e3 : (n : ℝ) ^ 3 ≤ (64 * a ^ 2 * x) ^ 2 * n := by
      have := mul_le_mul_of_nonneg_right e2 hn0
      calc (n : ℝ) ^ 3 = n ^ 2 * n := by ring
        _ ≤ _ := this
    have e4 : (4096 * (a : ℝ) ^ 4) * (13440 * a ^ 3) ≤ (4096 * a ^ 4) * (x ^ 2 * n) := by
      have : (4096 * (a : ℝ) ^ 4) * (13440 * a ^ 3) = 13440 * 4096 * (a : ℝ) ^ 7 := by ring
      have : (64 * (a : ℝ) ^ 2 * x) ^ 2 * n = (4096 * a ^ 4) * (x ^ 2 * n) := by ring
      linarith
    have := le_of_mul_le_mul_left e4 (by positivity)
    exact_mod_cast this
  set m₂ := x ^ 2 * n / (600 * a ^ 3) with hm₂
  have h6 : 0 < 600 * a ^ 3 := Nat.mul_pos (by norm_num) (pow_pos ha0 3)
  have hm2a : 600 * a ^ 3 * m₂ ≤ x ^ 2 * n := Nat.mul_div_le _ _
  have hm2c : x ^ 2 * n < m₂ * (600 * a ^ 3) + 600 * a ^ 3 := Nat.lt_div_mul_add h6
  have hm2d : 1 ≤ m₂ := (Nat.le_div_iff_mul_le h6).2 (by omega)
  have hm2b : x ^ 2 * n ≤ 1200 * a ^ 3 * m₂ := by
    have e1 : m₂ * (600 * a ^ 3) = 600 * (a ^ 3 * m₂) := by ring
    have e2 : 1200 * a ^ 3 * m₂ = 1200 * (a ^ 3 * m₂) := by ring
    have e3 : a ^ 3 ≤ a ^ 3 * m₂ := Nat.le_mul_of_pos_right _ hm2d
    omega
  have hxx : 16 * a ^ 2 * (x + 1) ≤ n := by
    have e1 : 16 * a ^ 2 * (x + 1) = 16 * (a ^ 2 * x) + 16 * a ^ 2 := by ring
    have e2 : 32 * a ^ 2 * x = 32 * (a ^ 2 * x) := by ring
    omega
  exact final_contra n a x L (Tsum G x) (∑ u, (out G x u).card) (∑ u, (Nb G u).card) m₁ m₂
    (Fa m₁) Fb (Fc m₂) Fd ha1 (by omega) (by omega) hm1a hm1b hxx hxl hm2a hm2b hc
    H1 H2 H3 H4 H5 H6 F1 F2

end

end E813

end S_W1

namespace E813

open Filter Classical

-- BEGIN-SOLUTION
lemma seven3_compl {n : ℕ} {G : SimpleGraph (Fin n)} (hG : Erdos813.EverySevenHasTriangle G) :
    Seven3 Gᶜ := by
  intro S hS
  obtain ⟨t, htS, ht⟩ := hG S hS
  refine ⟨t, htS, ht.card_eq, ?_⟩
  intro x hx y hy hxy
  rw [SimpleGraph.compl_adj] at hxy
  exact hxy.2 (ht.isClique hx hy hxy.1)

lemma indlt_compl {n : ℕ} {G : SimpleGraph (Fin n)} {a : ℕ} (h : G.cliqueNum < a) :
    IndLt Gᶜ a := by
  intro A hA
  have hcl : G.IsClique (A : Set (Fin n)) := by
    intro x hx y hy hxy
    by_contra hn
    exact hA x hx y hy ((SimpleGraph.compl_adj G x y).2 ⟨hxy, hn⟩)
  exact lt_of_le_of_lt hcl.card_le_cliqueNum h

theorem solution813 : ∀ ε : ℝ, 0 < ε → ε < 5 / 12 →
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (5 / 12 - ε : ℝ) ≤ (Erdos813.h n : ℝ) := by
  intro ε hε hε'
  have hcP : (0 : ℝ) ≤ cP := by unfold cP; norm_num
  have hC0 : (0 : ℝ) ≤ (C0 : ℝ) := by positivity
  filter_upwards [asym ε hε hε' 128 (by norm_num) 0 2 1 (by norm_num) (by norm_num),
    asym ε hε hε' (13440 * 4096) (by norm_num) 0 7 3 (by norm_num) (by norm_num),
    asym ε hε hε' (2000 * cP * 64 ^ 2) (by positivity) 1 19 8 (by norm_num) (by norm_num),
    asym ε hε hε' (2 ^ 34 * cP ^ 2 * 64 ^ 3) (by positivity) 2 36 15 (by norm_num) (by norm_num),
    asym ε hε hε' (2 ^ 73 * cP ^ 2 * 64) (by positivity) 2 31 13 (by norm_num) (by norm_num),
    asym ε hε hε' (2 ^ 92 * cP ^ 3 * 64 ^ 2) (by positivity) 3 48 20 (by norm_num) (by norm_num),
    asym ε hε hε' (256 * cP) (by positivity) 1 14 6 (by norm_num) (by norm_num),
    asym ε hε hε' (2 ^ 20 * cP * 64) (by positivity) 1 16 7 (by norm_num) (by norm_num),
    asym ε hε hε' (4 * (C0 : ℝ) * 345600 * 64 ^ 8) (by positivity) 2 24 10 (by norm_num)
      (by norm_num),
    asym ε hε hε' (2 * (2 * 345600 * 64 ^ 4)) (by norm_num) 0 12 6 (by norm_num) (by norm_num),
    eventually_ge_atTop 1] with n e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 hn1
  set θ : ℝ := 5 / 12 - ε with hθ
  set a := ⌈(n : ℝ) ^ θ⌉₊ with ha
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpos : 0 < (n : ℝ) ^ θ := Real.rpow_pos_of_pos (by linarith) _
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (by
    intro h0; rw [ha, Nat.ceil_eq_zero] at h0; linarith)
  have hA : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  simp only [pow_zero, mul_one, pow_one] at e1 e2 e3 e7 e8 e10
  have key : ∀ G : SimpleGraph (Fin n), Erdos813.EverySevenHasTriangle G → a ≤ G.cliqueNum := by
    intro G hG
    by_contra hlt
    push_neg at hlt
    have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
    refine main_bound (G := Gᶜ) (seven3_compl hG) a (indlt_compl hlt) ha1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ <;> rw [hcard]
    · exact_mod_cast e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
    · exact e6
    · exact e7
    · exact e8
    · have : (0 : ℝ) < (n : ℝ) ^ 10 := by positivity
      linarith
    · have : (0 : ℝ) < (a : ℝ) ^ 12 := by positivity
      nlinarith
  have hne : {k : ℕ | ∃ G : SimpleGraph (Fin n), Erdos813.EverySevenHasTriangle G ∧
      G.cliqueNum = k}.Nonempty := ⟨_, ⊤, Erdos813.everySevenHasTriangle_top n, rfl⟩
  have hh : a ≤ Erdos813.h n := by
    unfold Erdos813.h
    refine le_csInf hne ?_
    rintro k ⟨G, hG, rfl⟩
    exact key G hG
  calc (n : ℝ) ^ θ ≤ a := Nat.le_ceil _
    _ ≤ (Erdos813.h n : ℝ) := by exact_mod_cast hh

end E813

theorem OMA.solution : OMA.R_Erdos813_erdos_813_variants_bucic_sudakov_R1.H2 := by
  unfold OMA.R_Erdos813_erdos_813_variants_bucic_sudakov_R1.H2
  exact E813.solution813
