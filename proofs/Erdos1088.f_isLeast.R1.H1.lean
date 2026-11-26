import OMAReductions.R_Erdos1088_f_isLeast_R1

/-! # Coordinatewise monotone chains of Euclidean points -/
-- Credit: @steveDOTdigital

open Finset
open scoped EuclideanGeometry
namespace OMA.E1088
private theorem monoSub (k : ℕ) : ∃ m ≥ k, ∀ f : Fin m → ℝ,
    ∃ e : Fin k ↪o Fin m, Monotone (f ∘ e) ∨ Antitone (f ∘ e) := by
  classical
  let m := max k ((k+k).choose k)
  refine ⟨m,le_max_left _ _,?_⟩
  intro f
  let c (E : Finset (Fin m)) : Bool :=
    decide (∀ i ∈ E, ∀ j ∈ E, i < j → f i ≤ f j)
  have pair {i j : Fin m} (h : i < j) : c {i,j} = decide (f i ≤ f j) := by
    simp [c,h,not_lt_of_ge h.le]
  have big : (k+k).choose k ≤ (univ : Finset (Fin m)).card := by
    simpa [m] using le_max_right k ((k+k).choose k)
  have hR := Combinatorics.Diagonal.hasRamseyProperty_choose k k c univ big
  rcases hR with ⟨S,_,hS,hc⟩ | ⟨S,_,hS,hc⟩
  · let e := S.orderEmbOfFin hS
    refine ⟨e,Or.inr (antitone_iff_forall_lt.mpr ?_)⟩
    intro i j hij
    have he := e.strictMono hij
    have hh := hc {e i,e j} (by
      intro v hv; rcases Finset.mem_insert.mp hv with rfl | hv
      · exact S.orderEmbOfFin_mem hS i
      · rw [Finset.mem_singleton.mp hv]; exact S.orderEmbOfFin_mem hS j) (by simp [he.ne])
    rw [pair he] at hh
    exact le_of_lt (lt_of_not_ge (of_decide_eq_false hh))
  · let e := S.orderEmbOfFin hS
    refine ⟨e,Or.inl (monotone_iff_forall_lt.mpr ?_)⟩
    intro i j hij
    have he := e.strictMono hij
    have hh := hc {e i,e j} (by
      intro v hv; rcases Finset.mem_insert.mp hv with rfl | hv
      · exact S.orderEmbOfFin_mem hS i
      · rw [Finset.mem_singleton.mp hv]; exact S.orderEmbOfFin_mem hS j) (by simp [he.ne])
    rw [pair he] at hh
    exact of_decide_eq_true hh

private theorem selectCoords {d : ℕ} (J : Finset (Fin d)) (k : ℕ) :
    ∃ m ≥ k, ∀ f : Fin m → (ℝ^d), ∃ e : Fin k ↪o Fin m,
    ∀ t ∈ J, Monotone (fun i => f (e i) t) ∨ Antitone (fun i => f (e i) t) := by
  classical
  induction J using Finset.induction generalizing k with
  | empty => exact ⟨k,le_rfl,fun f => ⟨OrderEmbedding.ofStrictMono id strictMono_id,by simp⟩⟩
  | @insert t J ht ih =>
    obtain ⟨u,hku,hu⟩ := monoSub k
    obtain ⟨m,hum,hm⟩ := ih u
    refine ⟨m,hku.trans hum,?_⟩
    intro f
    obtain ⟨a,ha⟩ := hm f
    obtain ⟨b,hb⟩ := hu (fun i => f (a i) t)
    refine ⟨b.trans a,?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hb
    · rcases ha v hv with h | h
      · exact Or.inl (h.comp b.monotone)
      · exact Or.inr (h.comp_monotone b.monotone)
private theorem chain_dist {k d : ℕ} (p : Fin k ↪ (ℝ^d))
    (h : ∀ t, Monotone (fun i => p i t) ∨ Antitone (fun i => p i t))
    {i j l : Fin k} (hij : i < j) (hjl : j < l) :
    dist (p i) (p j) < dist (p i) (p l) ∧ dist (p j) (p l) < dist (p i) (p l) := by
  have hs : dist (p i) (p j)^2 + dist (p j) (p l)^2 ≤ dist (p i) (p l)^2 := by
    simp only [EuclideanSpace.dist_sq_eq, Real.dist_eq, sq_abs, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro t _
    rcases h t with ht | ht
    · have A := ht hij.le; have B := ht hjl.le
      dsimp at A B
      nlinarith [mul_nonneg (sub_nonneg.mpr A) (sub_nonneg.mpr B)]
    · have A := ht hij.le; have B := ht hjl.le
      dsimp at A B
      nlinarith [mul_nonneg (sub_nonneg.mpr A) (sub_nonneg.mpr B)]
  have hi := sq_pos_of_pos (dist_pos.mpr (p.injective.ne hij.ne))
  have hj := sq_pos_of_pos (dist_pos.mpr (p.injective.ne hjl.ne))
  constructor <;> apply (sq_lt_sq₀ dist_nonneg dist_nonneg).mp <;> linarith

theorem chains : OMA.R_Erdos1088_f_isLeast_R1.H1 := by
  classical
  intro d k
  obtain ⟨m,hkm,hm⟩ := selectCoords (univ : Finset (Fin d)) k
  refine ⟨m,hkm,?_⟩
  intro S hS
  let f : Fin m ↪ (ℝ^d) := (S.equivFinOfCardEq hS).symm.toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨e,he⟩ := hm f
  let p := e.toEmbedding.trans f
  refine ⟨p,fun i => ((S.equivFinOfCardEq hS).symm (e i)).property,?_⟩
  intro i j l hij hjl
  exact chain_dist p (fun t => he t (mem_univ _)) hij hjl
end OMA.E1088

theorem OMA.solution : OMA.R_Erdos1088_f_isLeast_R1.H1 := OMA.E1088.chains
