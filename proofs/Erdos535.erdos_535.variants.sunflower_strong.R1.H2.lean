import OMAReductions.R_Erdos535_erdos_535_variants_sunflower_strong_R1
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Multiset.Fintype

/-! Select compatible prime exponents by prescribing one bit for each occurrence of a prime. -/

open Finset

namespace OMA.PrimeLayers

def layers (a : ℕ) : Finset ℕ :=
  (a.primeFactorsList : Multiset ℕ).toEnumFinset.map Nat.pairEquiv.toEmbedding

lemma mem_layers (a p j : ℕ) :
    Nat.pair p j ∈ layers a ↔ j < a.factorization p := by
  change Nat.pairEquiv.toEmbedding (p,j) ∈ _ ↔ _
  rw [layers, Finset.mem_map', Multiset.mem_toEnumFinset]
  simp [Multiset.coe_count, Nat.primeFactorsList_count_eq]

lemma layers_inj {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : layers a = layers b) : a = b := by
  apply Nat.eq_of_factorization_eq ha.ne' hb.ne'
  intro p
  have H (j : ℕ) : j < a.factorization p ↔ j < b.factorization p := by
    rw [← mem_layers, ← mem_layers, h]
  have := H (a.factorization p)
  have := H (b.factorization p)
  omega

lemma layers_gcd {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    layers (a.gcd b) = layers a ∩ layers b := by
  ext t
  obtain ⟨⟨p,j⟩,rfl⟩ := Nat.pairEquiv.surjective t
  change Nat.pair p j ∈ layers (a.gcd b) ↔ Nat.pair p j ∈ layers a ∩ layers b
  simp only [Finset.mem_inter, mem_layers, Nat.factorization_gcd ha.ne' hb.ne', Finsupp.inf_apply,
    lt_inf_iff]

lemma choose_bits (A : Finset ℕ) (E : ℕ → Finset ℕ) (bit : ℕ → ℕ → Bool)
    (k : ℕ) (hk : ∀ a ∈ A, (E a).card = k) :
    ∃ (B : Finset ℕ) (color : ℕ → Bool), B ⊆ A ∧ A.card ≤ 2^k * B.card ∧
      ∀ a ∈ B, ∀ x ∈ E a, color x = bit a x := by
  classical
  by_cases hne : A.Nonempty
  · let S := A.biUnion E
    let C := S → Bool
    let color (c : C) (x : ℕ) := if hx : x ∈ S then c ⟨x,hx⟩ else false
    let good (a : ℕ) (c : C) := ∀ x ∈ E a, color c x = bit a x
    let cols := (univ : Finset C)
    have sub {a : ℕ} (ha : a ∈ A) : E a ⊆ S := fun x hx => mem_biUnion.mpr ⟨a,ha,hx⟩
    have count (a : ℕ) (ha : a ∈ A) : 2^(S.card-k) ≤ (cols.bipartiteAbove good a).card := by
      let D := S \ E a
      let extend (u : D → Bool) (x : S) :=
        if hx : x.val ∈ E a then bit a x else u ⟨x,mem_sdiff.mpr ⟨x.property,hx⟩⟩
      let embed (u : D → Bool) : ↥(cols.bipartiteAbove good a) :=
        ⟨extend u, mem_filter.mpr ⟨mem_univ _, fun x hx => by simp [color,extend,sub ha hx,hx]⟩⟩
      have inj : Function.Injective embed := by
        intro u v h
        have he : extend u = extend v := congrArg Subtype.val h
        funext x
        have hx := mem_sdiff.mp x.property
        simpa [extend,hx.2] using congrFun he ⟨x,hx.1⟩
      have hcard := Fintype.card_le_of_injective _ inj
      rw [Fintype.card_coe] at hcard
      simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_coe,D,
        card_sdiff_of_subset (sub ha),hk a ha] using hcard
    obtain ⟨c,_,hmax⟩ := cols.exists_max_image (fun c => (A.bipartiteBelow good c).card)
      ⟨fun _ => false, mem_univ _⟩
    refine ⟨A.bipartiteBelow good c, color c, filter_subset _ _, ?_, fun a ha => (mem_filter.mp ha).2⟩
    obtain ⟨a,ha⟩ := hne
    have hle : k ≤ S.card := hk a ha ▸ card_le_card (sub ha)
    have hp : 2^S.card = 2^(S.card-k) * 2^k := by rw [← pow_add,Nat.sub_add_cancel hle]
    have h := card_nsmul_le_card_nsmul (r := good) count hmax
    simp only [smul_eq_mul,cols,card_univ,C,Fintype.card_fun,Fintype.card_bool,Fintype.card_coe,hp] at h
    exact Nat.le_of_mul_le_mul_right (by simpa only [mul_assoc,mul_comm,mul_left_comm] using h)
      (pow_pos (by decide : 0 < 2) (S.card-k))
  · exact ⟨∅, fun _ => false, empty_subset _, by simp [not_nonempty_iff_eq_empty.mp hne], by simp⟩

lemma div_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (agree : ∀ p, 0 < a.factorization p → 0 < b.factorization p →
      a.factorization p = b.factorization p) : (a / a.gcd b).Coprime (a.gcd b) := by
  by_contra h
  obtain ⟨p,hp,h1,h2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hg := Nat.gcd_dvd_left a b
  have hd := Nat.gcd_pos_of_pos_left b ha
  have hq := Nat.div_pos (Nat.le_of_dvd ha hg) hd
  have h1' := (hp.dvd_iff_one_le_factorization hq.ne').mp h1
  have h2' := (hp.dvd_iff_one_le_factorization hd.ne').mp h2
  rw [Nat.factorization_div hg, Finsupp.tsub_apply] at h1'
  rw [Nat.factorization_gcd ha.ne' hb.ne', Finsupp.inf_apply] at h1' h2'
  change 1 ≤ a.factorization p - min (a.factorization p) (b.factorization p) at h1'
  change 1 ≤ min (a.factorization p) (b.factorization p) at h2'
  have := agree p (by omega) (by omega)
  omega

end OMA.PrimeLayers

open OMA.PrimeLayers

theorem OMA.solution : OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1.H2 := by
  classical
  intro r k A hA
  let lastBit (a t : ℕ) := decide (t.unpair.2 + 1 = a.factorization t.unpair.1)
  have hk (a : ℕ) (ha : a ∈ A) : (layers a).card = k := by
    rw [layers, card_map, Multiset.card_toEnumFinset]
    exact (hA a ha).2
  obtain ⟨B,col,hBA,hsize,hcol⟩ := choose_bits A layers lastBit k hk
  have pos {a} (ha : a ∈ B) : 0 < a := (hA _ (hBA ha)).1
  have no_lt {a b} (ha : a ∈ B) (hb : b ∈ B) (p : ℕ) (hpos : 0 < a.factorization p)
      (hlt : a.factorization p < b.factorization p) : False := by
    let j := a.factorization p - 1
    have hj : j + 1 = a.factorization p := by dsimp [j]; omega
    have ha' := hcol a ha _ ((mem_layers a p j).mpr (by omega))
    have hb' := hcol b hb _ ((mem_layers b p j).mpr (by omega))
    simpa [lastBit, Nat.unpair_pair, hj, hlt.ne] using ha'.symm.trans hb'
  refine ⟨B,hBA,hsize,layers,fun a ha b hb h => layers_inj (pos ha) (pos hb) h,
    fun a ha => hk a (hBA ha), ?_⟩
  intro S hSB _ hK
  obtain ⟨K,hK⟩ := hK
  by_cases hs : ∃ x ∈ S, ∃ y ∈ S, x ≠ y
  · obtain ⟨x,hx,y,hy,hxy⟩ := hs
    let d := x.gcd y
    have gcd_eq {a b} (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) : a.gcd b = d := by
      apply layers_inj (Nat.gcd_pos_of_pos_left _ (pos (hSB ha)))
        (Nat.gcd_pos_of_pos_left _ (pos (hSB hx)))
      exact (layers_gcd (pos (hSB ha)) (pos (hSB hb))).trans
        ((hK ha hb hne).trans ((hK hx hy hxy).symm.trans
          (layers_gcd (pos (hSB hx)) (pos (hSB hy))).symm))
    refine ⟨d, Nat.gcd_pos_of_pos_left _ (pos (hSB hx)), fun a ha b hb h => gcd_eq ha hb h, ?_⟩
    intro a ha
    obtain ⟨b,hb,hne⟩ : ∃ b ∈ S, a ≠ b := by
      by_cases h : a = x
      · exact ⟨y,hy,h ▸ hxy⟩
      · exact ⟨x,hx,h⟩
    rw [← gcd_eq ha hb hne]
    refine ⟨a / a.gcd b,(Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm, ?_⟩
    apply div_coprime (pos (hSB ha)) (pos (hSB hb))
    intro p h1 h2
    exact le_antisymm (le_of_not_gt (no_lt (hSB hb) (hSB ha) p h2))
      (le_of_not_gt (no_lt (hSB ha) (hSB hb) p h1))
  · refine ⟨1,by decide, ?_,fun a _ => ⟨a, by simp, by simp⟩⟩
    intro a ha b hb hne
    exact (hs ⟨a,ha,b,hb,hne⟩).elim
