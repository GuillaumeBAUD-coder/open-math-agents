import OMAStatements.S_oeis_a223240
import Mathlib

-- Problem: oeis-a223240, n X 1 arrays on the 3-loop graph
-- Upstream: formal-conjectures statements/oeis-a223240.lean:0 (declaration OMA.S_oeis_a223240.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A223240aux
open OMA.S_oeis_a223240

instance edgeDec : DecidableRel edge := fun u v => by
  unfold edge
  infer_instance

def Walk (n : ℕ) (f : Fin (n + 1) → Fin 7) : Prop :=
  ∀ i : Fin n, edge (f i.castSucc) (f i.succ)

instance walkDec (n : ℕ) : DecidablePred (Walk n) := fun f => by
  unfold Walk
  infer_instance

def W (n : ℕ) (v : Fin 7) : Finset (Fin (n + 1) → Fin 7) :=
  (Finset.univ.filter (Walk n)).filter (fun f => f 0 = v)

theorem mem_W (n : ℕ) (v : Fin 7) (f : Fin (n + 1) → Fin 7) :
    f ∈ W n v ↔ Walk n f ∧ f 0 = v := by
  simp [W]

theorem card_W_succ (n : ℕ) (v : Fin 7) :
    (W (n + 1) v).card = ∑ u : Fin 7, if edge v u then (W n u).card else 0 := by
  have h1 : (W (n + 1) v).card
      = ((Finset.univ.filter (fun u => edge v u)).sigma (fun u => W n u)).card := by
    refine Finset.card_nbij' (fun f => ⟨f 1, Fin.tail f⟩)
      (fun p => Fin.cons (α := fun _ => Fin 7) v p.2) ?_ ?_ ?_ ?_
    · intro f hf
      have hf' := (mem_W _ _ _).1 (Finset.mem_coe.1 hf)
      obtain ⟨hw, h0⟩ := hf'
      simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_filter, Finset.mem_univ,
        true_and, Set.mem_ofPred_eq, Finset.mem_coe]
      refine ⟨?_, (mem_W _ _ _).2 ⟨?_, rfl⟩⟩
      · have := hw 0
        rw [← h0]
        simpa using this
      · intro i
        have := hw i.succ
        simpa [Fin.tail] using this
    · intro p hp
      simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_filter, Finset.mem_univ,
        true_and, Set.mem_ofPred_eq, Finset.mem_coe] at hp
      obtain ⟨he, hp2⟩ := hp
      obtain ⟨hw, h0⟩ := (mem_W _ _ _).1 hp2
      refine Finset.mem_coe.2 ((mem_W _ _ _).2 ⟨?_, by simp⟩)
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [h0] using he
      · have := hw j
        simpa using this
    · intro f hf
      obtain ⟨hw, h0⟩ := (mem_W _ _ _).1 (Finset.mem_coe.1 hf)
      rw [← h0]
      exact Fin.cons_self_tail f
    · intro p hp
      simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_filter, Finset.mem_univ,
        true_and, Set.mem_ofPred_eq, Finset.mem_coe] at hp
      obtain ⟨he, hp2⟩ := hp
      obtain ⟨hw, h0⟩ := (mem_W _ _ _).1 hp2
      obtain ⟨u, g⟩ := p
      simp only at h0
      subst h0
      simp
  rw [h1, Finset.card_sigma, Finset.sum_filter]

def cd : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => (6 * (cd n).2, (cd n).1 + (cd n).2)

theorem card_W_zero (v : Fin 7) : (W 0 v).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨fun _ => v, ?_⟩
  ext f
  rw [mem_W, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h0⟩
    funext i
    rw [Fin.eq_zero i]
    exact h0
  · rintro rfl
    exact ⟨fun i => i.elim0, rfl⟩

theorem card_W (n : ℕ) :
    (W n 0).card = (cd n).1 ∧ ∀ v : Fin 7, v ≠ 0 → (W n v).card = (cd n).2 := by
  induction n with
  | zero => exact ⟨card_W_zero 0, fun v _ => card_W_zero v⟩
  | succ n ih =>
    obtain ⟨ih0, ih1⟩ := ih
    have h1 := ih1 1 (by decide)
    have h2 := ih1 2 (by decide)
    have h3 := ih1 3 (by decide)
    have h4 := ih1 4 (by decide)
    have h5 := ih1 5 (by decide)
    have h6 := ih1 6 (by decide)
    refine ⟨?_, ?_⟩
    · rw [card_W_succ, Fin.sum_univ_seven]
      simp [edge, edges, ih0, h1, h2, h3, h4, h5, h6, cd]
      omega
    · intro v hv
      rw [card_W_succ, Fin.sum_univ_seven]
      fin_cases v <;> simp [edge, edges, ih0, h1, h2, h3, h4, h5, h6, cd] at hv ⊢ <;> omega

theorem edge_symm {u v : Fin 7} (h : edge u v) : edge v u := by
  unfold edge at *
  exact h.symm

theorem good_iff (m : ℕ) (x : Fin (m + 1) → Fin 1 → Fin 7) :
    Good x ↔ Walk m (fun i => x i 0) := by
  constructor
  · intro h i
    exact h (i.castSucc, 0) (i.succ, 0) (Or.inr ⟨rfl, Or.inr (by simp)⟩)
  · intro h p q hpq
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    have hp2 : p2 = 0 := Fin.eq_zero p2
    have hq2 : q2 = 0 := Fin.eq_zero q2
    subst hp2 hq2
    rcases hpq with ⟨_, h1 | h1⟩ | ⟨_, h1 | h1⟩
    · simp at h1
    · simp at h1
    · have h1' : (p1 : ℕ) = q1 + 1 := h1
      have hlt : (q1 : ℕ) < m := by
        have := p1.isLt
        omega
      have := h ⟨q1, hlt⟩
      have e1 : (⟨q1, hlt⟩ : Fin m).castSucc = q1 := Fin.ext rfl
      have e2 : (⟨q1, hlt⟩ : Fin m).succ = p1 := Fin.ext (by simp; omega)
      rw [e1, e2] at this
      exact edge_symm this
    · have h1' : (q1 : ℕ) = p1 + 1 := h1
      have hlt : (p1 : ℕ) < m := by
        have := q1.isLt
        omega
      have := h ⟨p1, hlt⟩
      have e1 : (⟨p1, hlt⟩ : Fin m).castSucc = p1 := Fin.ext rfl
      have e2 : (⟨p1, hlt⟩ : Fin m).succ = q1 := Fin.ext (by simp; omega)
      rw [e1, e2] at this
      exact this

theorem a_succ (m : ℕ) : a (m + 1) = (cd m).1 + 6 * (cd m).2 := by
  have e : {x : Fin (m + 1) → Fin 1 → Fin 7 // Good x} ≃ {f : Fin (m + 1) → Fin 7 // Walk m f} :=
    (Equiv.piCongrRight (fun _ => Equiv.funUnique (Fin 1) (Fin 7))).subtypeEquiv
      (fun x => (good_iff m x).trans Iff.rfl)
  unfold a
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  have hc := card_W m
  rw [Fin.sum_univ_seven]
  change (W m 0).card + (W m 1).card + (W m 2).card + (W m 3).card + (W m 4).card
    + (W m 5).card + (W m 6).card = _
  rw [hc.1, hc.2 1 (by decide), hc.2 2 (by decide), hc.2 3 (by decide), hc.2 4 (by decide),
    hc.2 5 (by decide), hc.2 6 (by decide)]
  ring

theorem cd_closed (m : ℕ) :
    ((cd m).1 : ℚ) = (8 * 3 ^ m - 3 * (-2) ^ m) / 5 ∧
    ((cd m).2 : ℚ) = (4 * 3 ^ m + (-2) ^ m) / 5 := by
  induction m with
  | zero => norm_num [cd]
  | succ m ih =>
    obtain ⟨i1, i2⟩ := ih
    simp only [cd]
    push_cast
    rw [i1, i2]
    constructor <;> ring

theorem gf_aux (f : ℕ → ℚ) (h0 : f 0 = 0) (h1 : f 1 = 7) (h2 : f 2 = 18)
    (hr : ∀ n, f (n + 3) = f (n + 2) + 6 * f (n + 1)) :
    PowerSeries.mk f * ((1 + 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X))
      = PowerSeries.X * (7 + 11 * PowerSeries.X) := by
  have h6 : (PowerSeries.C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat _ 6
  have h7 : (PowerSeries.C (7 : ℚ) : PowerSeries ℚ) = 7 := map_ofNat _ 7
  have h11 : (PowerSeries.C (11 : ℚ) : PowerSeries ℚ) = 11 := map_ofNat _ 11
  have e1 : PowerSeries.mk f * ((1 + 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X))
      = PowerSeries.mk f - PowerSeries.X ^ 1 * PowerSeries.mk f
        - PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 2 * PowerSeries.mk f) := by
    rw [h6]
    ring
  have e2 : (PowerSeries.X : PowerSeries ℚ) * (7 + 11 * PowerSeries.X)
      = PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 1
        + PowerSeries.C (11 : ℚ) * PowerSeries.X ^ 2 := by
    rw [h7, h11]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | n
  · simp [h0]
  · simp [h0, h1]
  · simp [h0, h1, h2]
    norm_num
  · have := hr n
    simp
    linarith

end OMA.A223240aux

open OMA.S_oeis_a223240 OMA.A223240aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a223240.main := by
  have hrec : ∀ m, a (m + 3) = a (m + 2) + 6 * a (m + 1) := by
    intro m
    rw [a_succ, a_succ, a_succ]
    simp only [cd]
    ring
  have ha1 : a 1 = 7 := by
    rw [a_succ]
    simp [cd]
  have ha2 : a 2 = 18 := by
    rw [a_succ]
    simp [cd]
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    exact hrec m
  · unfold G
    rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    apply gf_aux
    · simp
    · simp [ha1]
    · simp [ha2]
    · intro n
      simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, if_false, one_ne_zero]
      exact_mod_cast hrec n
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [a_succ]
    obtain ⟨c1, c2⟩ := cd_closed m
    push_cast
    rw [c1, c2]
    ring

