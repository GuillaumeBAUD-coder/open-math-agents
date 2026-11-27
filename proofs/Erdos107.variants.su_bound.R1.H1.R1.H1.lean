import OMAReductions.R_Erdos107_variants_su_bound_R1_H1_R1
import Mathlib

open Finset

namespace FiniteUniformRamsey

universe u

/-- A bound for the size of a monochromatic set in a two-color uniform hypergraph. -/
def Bound (r m N : ℕ) : Prop :=
  ∀ {α : Type u} [LinearOrder α] (S : Finset α), N ≤ S.card →
    ∀ c : Finset α → Bool, ∃ (b : Bool) (T : Finset α), T ⊆ S ∧
      T.card = m ∧ ∀ e ⊆ T, e.card = r → c e = b

/-- Make the color of each edge depend only on its least vertex. -/
private theorem stabilize (r : ℕ) (lower : ∀ m, ∃ N, m ≤ N ∧ Bound.{u} r m N)
    (L : ℕ) : ∃ N, L ≤ N ∧ ∀ {α : Type u} [LinearOrder α] (S : Finset α),
      N ≤ S.card → ∀ c : Finset α → Bool, ∃ (T : Finset α) (d : α → Bool),
        T ⊆ S ∧ T.card = L ∧ ∀ e ⊆ T, e.card = r + 1 →
          ∀ v ∈ e, (∀ w ∈ e, v ≤ w) → c e = d v := by
  classical
  induction L with
  | zero =>
    refine ⟨0, le_rfl, fun S _ c => ⟨∅, fun _ => false, empty_subset _, card_empty, ?_⟩⟩
    intro e he hcard
    have hz : e.card ≤ 0 := by simpa using card_le_card he
    omega
  | succ L ih =>
    obtain ⟨M, hLM, hM⟩ := ih
    obtain ⟨N, hMN, hN⟩ := lower M
    refine ⟨N + 1, by omega, ?_⟩
    intro α _ S hS c
    have hnS : S.Nonempty := card_pos.mp (by omega)
    let a := S.min' hnS
    have ha : a ∈ S := min'_mem _ _
    have hS' : N ≤ (S.erase a).card := by rw [card_erase_of_mem ha]; omega
    obtain ⟨b, P, hPS, hPcard, hPc⟩ := hN (S.erase a) hS' (fun f => c (insert a f))
    obtain ⟨T, d, hTP, hTcard, hTd⟩ := hM P hPcard.ge c
    have haT : a ∉ T := fun haT => (mem_erase.mp (hPS (hTP haT))).1 rfl
    refine ⟨insert a T, Function.update d a b, ?_, ?_, ?_⟩
    · exact insert_subset ha (hTP.trans (hPS.trans (erase_subset _ _)))
    · rw [card_insert_of_notMem haT, hTcard]
    intro e he hcard v hv hleast
    by_cases hae : a ∈ e
    · have hva : v = a := le_antisymm (hleast a hae)
        (min'_le _ _ (by
          have h := he hv
          exact (mem_insert.mp h).elim (fun h => h ▸ ha)
            (fun h => (mem_erase.mp (hPS (hTP h))).2)))
      have hep : e.erase a ⊆ P := by
        intro w hw
        obtain ⟨hwa, hwe⟩ := mem_erase.mp hw
        exact hTP ((mem_insert.mp (he hwe)).resolve_left hwa)
      have hecard : (e.erase a).card = r := by rw [card_erase_of_mem hae, hcard]; omega
      have hb := hPc _ hep hecard
      change c (insert a (e.erase a)) = b at hb
      rw [insert_erase hae] at hb
      simpa [hva] using hb
    · have heT : e ⊆ T := by
        intro w hwe
        exact (mem_insert.mp (he hwe)).resolve_left (fun h => hae (h ▸ hwe))
      have hva : v ≠ a := fun h => hae (h ▸ hv)
      rw [Function.update_of_ne hva]
      exact hTd _ heT hcard _ hv hleast

theorem exists_bound (r m : ℕ) : ∃ N, m ≤ N ∧ Bound.{u} r m N := by
  classical
  induction r generalizing m with
  | zero =>
    refine ⟨m, le_rfl, ?_⟩
    intro α _ S hS c
    obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq hS
    refine ⟨c ∅, T, hTS, hT, ?_⟩
    intro e _ he
    rw [card_eq_zero.mp he]
  | succ r ih =>
    obtain ⟨N, hN, h⟩ := stabilize r ih (2 * m)
    refine ⟨N, by omega, ?_⟩
    intro α _ S hS c
    obtain ⟨T, d, hTS, hT, hTd⟩ := h S hS c
    have hsplit := card_filter_add_card_filter_not (s := T) (p := fun a => d a = true)
    have hcolor : ∃ b : Bool, m ≤ (T.filter (fun a => d a = b)).card := by
      by_cases hlarge : m ≤ (T.filter (fun a => d a = true)).card
      · exact ⟨true, hlarge⟩
      · refine ⟨false, ?_⟩
        have heq : T.filter (fun a => ¬ d a = true) = T.filter (fun a => d a = false) := by
          ext a
          cases h : d a <;> simp [h]
        rw [heq, hT] at hsplit
        omega
    obtain ⟨b, hb⟩ := hcolor
    obtain ⟨U, hU, hcard⟩ := exists_subset_card_eq hb
    refine ⟨b, U, hU.trans ((filter_subset _ _).trans hTS), hcard, ?_⟩
    intro e he hecard
    have hne : e.Nonempty := card_pos.mp (by omega)
    let v := e.min' hne
    have hv : v ∈ e := min'_mem _ _
    exact (hTd e (he.trans (hU.trans (filter_subset _ _))) hecard v hv
      (fun w hw => min'_le _ _ hw)).trans (mem_filter.mp (hU (he hv))).2

theorem finite (r m : ℕ) : ∃ N : ℕ, m ≤ N ∧ ∀ c : Finset (Fin N) → Bool,
    ∃ (b : Bool) (T : Finset (Fin N)), T.card = m ∧ ∀ e ⊆ T, e.card = r → c e = b := by
  obtain ⟨N, hN, h⟩ := exists_bound.{0} r m
  refine ⟨N, hN, ?_⟩
  intro c
  obtain ⟨b, T, _, hcard, hmono⟩ := h univ (by simp) c
  exact ⟨b, T, hcard, hmono⟩

end FiniteUniformRamsey

namespace CupCapRamsey

open Finset

private def turn (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1)

theorem main :
    ∀ k : ℕ, 0 < k → ∃ m : ℕ, 2 * k + 1 ≤ m ∧
      ∀ U : Finset (ℝ × ℝ), U.card = m → Set.InjOn Prod.fst (U : Set (ℝ × ℝ)) →
        (∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, a.1 < b.1 → b.1 < c.1 →
          (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0) →
        ∃ (up : Bool) (e : Fin (2 * k + 1) → ℝ × ℝ), (∀ i, e i ∈ U) ∧
          StrictMono (fun i => (e i).1) ∧ ∀ i j l, i < j → j < l →
            0 < (if up then (1 : ℝ) else -1) * (((e j).1 - (e i).1) * ((e l).2 - (e j).2) -
              ((e j).2 - (e i).2) * ((e l).1 - (e j).1)) := by
  classical
  intro k _
  obtain ⟨m, hsize, hRam⟩ := FiniteUniformRamsey.exists_bound.{0} 3 (2 * k + 1)
  refine ⟨m, hsize, ?_⟩
  intro U hU hInj hGeneral
  let S := U.image Prod.fst
  have hS : S.card = m := (card_image_of_injOn hInj).trans hU
  have hpre (x : ℝ) (hx : x ∈ S) : ∃ p ∈ U, p.1 = x := mem_image.mp hx
  let pt (x : ℝ) : ℝ × ℝ := if hx : x ∈ S then (hpre x hx).choose else (x, 0)
  have hpt (x : ℝ) (hx : x ∈ S) : pt x ∈ U ∧ (pt x).1 = x := by
    simpa only [pt, dif_pos hx] using (hpre x hx).choose_spec
  let color (F : Finset ℝ) : Bool := if h : F.card = 3 then
    decide (0 < turn (pt (F.orderEmbOfFin h 0)) (pt (F.orderEmbOfFin h 1))
      (pt (F.orderEmbOfFin h 2))) else false
  obtain ⟨b, T, hTS, hT, hcolor⟩ := hRam S hS.ge color
  let g := T.orderEmbOfFin hT
  have hg (i : Fin (2 * k + 1)) : g i ∈ T := orderEmbOfFin_mem _ _ _
  let e := pt ∘ g
  have he (i : Fin (2 * k + 1)) : e i ∈ U ∧ (e i).1 = g i := hpt _ (hTS (hg i))
  have hem : StrictMono (fun i => (e i).1) := fun i j hij => by
    change (e i).1 < (e j).1
    rw [(he i).2, (he j).2]
    exact g.strictMono hij
  refine ⟨b, e, fun i => (he i).1, hem, ?_⟩
  intro i j l hij hjl
  have hij' := g.strictMono hij
  have hjl' := g.strictMono hjl
  have hil' := hij'.trans hjl'
  let F : Finset ℝ := {g i, g j, g l}
  have hF : F.card = 3 := by
    dsimp only [F]
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp [ne_of_lt hjl']
    · simp [ne_of_lt hij', ne_of_lt hil']
  have hFT : F ⊆ T := by
    intro x hx
    simp only [F, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    all_goals exact hg _
  let f : Fin 3 → ℝ := ![g i, g j, g l]
  have hfm : StrictMono f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  have hfF (a : Fin 3) : f a ∈ F := by fin_cases a <;> simp [f, F]
  have hsort : f = F.orderEmbOfFin hF := orderEmbOfFin_unique hF hfF hfm
  have hc := hcolor F hFT hF
  simp only [color, dif_pos hF, ← hsort] at hc
  change decide (0 < turn (e i) (e j) (e l)) = b at hc
  have hne : turn (e i) (e j) (e l) ≠ 0 :=
    hGeneral _ (he i).1 _ (he j).1 _ (he l).1 (hem hij) (hem hjl)
  change 0 < (if b then (1 : ℝ) else -1) * turn (e i) (e j) (e l)
  cases b with
  | false =>
    have hn : ¬ 0 < turn (e i) (e j) (e l) := of_decide_eq_false hc
    simpa using lt_of_le_of_ne (le_of_not_gt hn) hne
  | true =>
    simpa using of_decide_eq_true hc

end CupCapRamsey

theorem OMA.solution : OMA.R_Erdos107_variants_su_bound_R1_H1_R1.H1 :=
  CupCapRamsey.main