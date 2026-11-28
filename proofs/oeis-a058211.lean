import OMAStatements.S_oeis_a058211
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a058211

/-- Integer points as real points. -/
def a058211Emb : ℤ × ℤ ↪ ℝ × ℝ :=
  ⟨fun z => ((z.1 : ℝ), (z.2 : ℝ)), fun a b h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by exact_mod_cast h.1) (by exact_mod_cast h.2)⟩

/-- Integer collinearity test. -/
def a058211ColZ (p q r : ℤ × ℤ) : Bool :=
  decide ((q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1))

theorem a058211Emb_apply (z : ℤ × ℤ) : a058211Emb z = ((z.1 : ℝ), (z.2 : ℝ)) := rfl

theorem a058211_col_iff (p q r : ℤ × ℤ) :
    collinear3 (a058211Emb p) (a058211Emb q) (a058211Emb r) ↔ a058211ColZ p q r = true := by
  simp only [collinear3, a058211ColZ, decide_eq_true_eq, a058211Emb_apply]
  constructor <;> intro h
  · exact_mod_cast h
  · exact_mod_cast h

/-- Nine integer points, each on exactly four connecting lines. -/
def a058211T : Finset (ℤ × ℤ) :=
  {(30, 10), (30, 15), (30, 18), (30, 30), (20, 30), (25, 20), (15, 30), (45, 0), (0, 30)}

theorem a058211_lines_eq (T : Finset (ℤ × ℤ)) (p : ℤ × ℤ) :
    numLinesThrough (T.map a058211Emb) (a058211Emb p) =
      ((T.erase p).image (fun q => T.filter (fun r => a058211ColZ p q r = true))).card := by
  classical
  unfold numLinesThrough
  have hmap : (T.erase p).map a058211Emb = (T.erase p).image a058211Emb := Finset.map_eq_image _ _
  rw [← Finset.map_erase, hmap, Finset.image_image]
  have hf : ((fun q => (T.map a058211Emb).filter (fun r => collinear3 (a058211Emb p) q r)) ∘
      a058211Emb) = fun q => (T.filter (fun r => a058211ColZ p q r = true)).map a058211Emb := by
    funext q
    simp only [Function.comp]
    rw [Finset.filter_map]
    congr 1
    apply Finset.filter_congr
    intro r _
    simp only [Function.comp, a058211_col_iff]
  rw [hf]
  rw [show (T.erase p).image (fun q => (T.filter (fun r => a058211ColZ p q r = true)).map a058211Emb)
      = ((T.erase p).image (fun q => T.filter (fun r => a058211ColZ p q r = true))).image
          (Finset.map a058211Emb) by rw [Finset.image_image]; rfl]
  exact Finset.card_image_of_injective _ (Finset.map_injective _)

theorem a058211_key : ∀ p ∈ a058211T,
    ((a058211T.erase p).image (fun q => a058211T.filter (fun r => a058211ColZ p q r = true))).card ≤ 4 := by
  decide +kernel

end OMA.Helpers

open OMA.Helpers OMA.S_oeis_a058211 in
/-- A nine-point counterexample: every point lies on exactly four connecting lines, and
`9 > 2 * 4`. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a058211.main) := by
  intro h
  have m1 : ((30, 10) : ℤ × ℤ) ∈ a058211T := by decide
  have m2 : ((30, 15) : ℤ × ℤ) ∈ a058211T := by decide
  have m3 : ((20, 30) : ℤ × ℤ) ∈ a058211T := by decide
  have hnc : ¬ collinear3 (a058211Emb (30, 10)) (a058211Emb (30, 15)) (a058211Emb (20, 30)) := by
    rw [a058211_col_iff]; decide
  obtain ⟨p, hp, hle⟩ := h (a058211T.map a058211Emb)
    ⟨_, Finset.mem_map_of_mem _ m1, _, Finset.mem_map_of_mem _ m2, _, Finset.mem_map_of_mem _ m3, hnc⟩
  rw [Finset.mem_map] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  rw [a058211_lines_eq, Finset.card_map] at hle
  have hc : a058211T.card = 9 := by decide
  have h4 := a058211_key z hz
  omega
