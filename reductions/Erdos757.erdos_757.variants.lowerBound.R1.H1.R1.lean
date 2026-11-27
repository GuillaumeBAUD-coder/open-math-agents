import OMAReductions.R_Erdos757_erdos_757_variants_lowerBound_R1

/-! Ma and Tang, arXiv:2602.23282, Theorem 1.6: use the hypergraph of three-term
progressions. Its edges have distinct midpoints. A small transversal gives a
progression-free complement of size at least nine seventeenths of the set. -/

namespace OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1
open Finset
open scoped Pointwise Classical

def H1 : Prop :=
  ∀ A : Finset ℝ, (∀ B : Set ℝ, B ⊆ (A : Set ℝ) → B.ncard = 4 → 11 ≤ (B-B).ncard) →
    let E := A.powerset.filter fun e => ∃ a b c : ℝ,
      a < b ∧ b < c ∧ a+c = 2*b ∧ e = {a,b,c}
    (∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1) ∧
    ∀ a b c d t : ℝ, a < b → b < c → d < b → b < t →
      a+c = 2*b → d+t = 2*b → {a,b,c} ∈ E → {d,b,t} ∈ E → a = d

def H2 : Prop :=
  ∀ A : Finset ℝ, (∀ B : Set ℝ, B ⊆ (A : Set ℝ) → B.ncard = 4 → 11 ≤ (B-B).ncard) →
    let E := A.powerset.filter fun e => ∃ a b c : ℝ,
      a < b ∧ b < c ∧ a+c = 2*b ∧ e = {a,b,c}
    ¬ ∃ f : Fin 7 ↪ ℝ, {f 0,f 1,f 2} ∈ E ∧ {f 0,f 3,f 4} ∈ E ∧
        {f 0,f 5,f 6} ∈ E ∧ {f 1,f 3,f 5} ∈ E ∧ {f 2,f 4,f 6} ∈ E

def H3 : Prop :=
  ∀ (A : Finset ℝ) (E : Finset (Finset ℝ)), (∀ e ∈ E, e ⊆ A ∧ e.card = 3) →
    (∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1) →
    (¬ ∃ f : Fin 7 ↪ ℝ, {f 0,f 1,f 2} ∈ E ∧ {f 0,f 3,f 4} ∈ E ∧
        {f 0,f 5,f 6} ∈ E ∧ {f 1,f 3,f 5} ∈ E ∧ {f 2,f 4,f 6} ∈ E) →
    ∃ T ⊆ A, (∀ e ∈ E, (e ∩ T).Nonempty) ∧ 17*T.card ≤ 5*A.card+3*E.card

theorem main : H1 → H2 → H3 → OMA.R_Erdos757_erdos_757_variants_lowerBound_R1.H1 := by
  classical
  intro config forbid cover
  refine ⟨9/17,by norm_num,?_⟩
  intro X hX _ condition
  let A := hX.toFinset
  have coeA : (A : Set ℝ) = X := hX.coe_toFinset
  let E := A.powerset.filter fun e => ∃ a b c : ℝ,
      a < b ∧ b < c ∧ a+c = 2*b ∧ e = {a,b,c}
  have localCond : ∀ B : Set ℝ, B ⊆ (A : Set ℝ) → B.ncard = 4 → 11 ≤ (B-B).ncard := by
    rwa [coeA]
  obtain ⟨lin,mid⟩ := config A localCond
  have sub {e} (he : e ∈ E) : e ⊆ A := mem_powerset.mp (mem_filter.mp he).1
  have dataE (e : E) := (mem_filter.mp e.property).2
  choose a b c ab bc avg form using dataE
  have midMem (e : E) : b e ∈ e.val := by rw [form e]; simp
  have inj : Function.Injective b := by
    intro e f eq
    have ha := mid (a e) (b e) (c e) (a f) (c f) (ab e) (bc e) (eq.symm ▸ ab f)
      (eq.symm ▸ bc f) (avg e) (eq.symm ▸ avg f) ((form e) ▸ e.property)
      (eq.symm ▸ (form f) ▸ f.property)
    have hc : c e = c f := by linarith [avg e,avg f]
    apply Subtype.ext
    rw [form e,form f,ha,eq,hc]
  have count : E.card ≤ A.card := by
    let f (e : E) : A := ⟨b e,sub e.property (midMem e)⟩
    simpa using Fintype.card_le_of_injective f (fun x y h => inj (congrArg Subtype.val h))
  have three (e) (h : e ∈ E) : e.card = 3 := by
    let z : E := ⟨e,h⟩
    change z.val.card = 3
    rw [form z]
    simp [(ab z).ne,(bc z).ne,((ab z).trans (bc z)).ne]
  obtain ⟨T,hT,hit,bound⟩ := cover A E (fun e h => ⟨sub h,three _ h⟩) lin (forbid A localCond)
  let S := A \ T
  refine ⟨(S : Set ℝ),coeA ▸ (show (S : Set ℝ) ⊆ A from fun _ h => (mem_sdiff.mp h).1),?_,?_⟩
  · have noAP (a b c : ℝ) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
        (ab : a < b) (bc : b < c) (avg : a+c=2*b) : False := by
      have he : {a,b,c} ∈ E := mem_filter.mpr ⟨mem_powerset.mpr (by
        intro z hz
        simp only [mem_insert,mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        exacts [(mem_sdiff.mp ha).1,(mem_sdiff.mp hb).1,(mem_sdiff.mp hc).1]),
        a,b,c,ab,bc,avg,rfl⟩
      obtain ⟨z,hz⟩ := hit _ he
      obtain ⟨hz,hzt⟩ := mem_inter.mp hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact (mem_sdiff.mp ha).2 hzt
      · exact (mem_sdiff.mp hb).2 hzt
      · exact (mem_sdiff.mp hc).2 hzt
    intro x hx y hy z hz eq
    rcases lt_trichotomy x z with h | h | h
    · exact False.elim (noAP _ _ _ hx hy hz (by linarith) (by linarith) eq)
    · exact h
    · exact False.elim (noAP _ _ _ hz hy hx (by linarith) (by linarith) (by linarith))
  · rw [← coeA,Set.ncard_coe_finset,Set.ncard_coe_finset]
    have size : S.card + T.card = A.card := card_sdiff_add_card_eq_card hT
    have h : 9*A.card ≤ 17*S.card := by omega
    have hr : (9:ℝ)*A.card ≤ 17*S.card := by exact_mod_cast h
    linarith

end OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1
