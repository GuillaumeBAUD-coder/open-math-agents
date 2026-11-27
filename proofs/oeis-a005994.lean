import OMAStatements.S_oeis_a005994
import Mathlib

namespace A005994

open Finset OMA.S_oeis_a005994

/-- Parameters `((r, d), (δ, ⟨x, y⟩))` with `r < 2`, `|δ| ≤ d` and `x + y + 2 d + r ≤ N`. -/
noncomputable def S (N : ℕ) : Finset (Σ _ : ℕ × ℕ, ℤ × (Σ _ : ℕ, ℕ)) :=
  (range 2 ×ˢ range (N + 1)).sigma (fun rd =>
    Icc (-(rd.2 : ℤ)) (rd.2 : ℤ) ×ˢ
      (range (N + 1 - (2 * rd.2 + rd.1))).sigma
        (fun x => range (N + 1 - (2 * rd.2 + rd.1) - x)))

lemma mem_S (N : ℕ) (q : Σ _ : ℕ × ℕ, ℤ × (Σ _ : ℕ, ℕ)) :
    q ∈ S N ↔ (q.1.1 < 2 ∧ q.1.2 < N + 1) ∧ (-(q.1.2 : ℤ) ≤ q.2.1 ∧ q.2.1 ≤ q.1.2) ∧
      (q.2.2.1 < N + 1 - (2 * q.1.2 + q.1.1) ∧
        q.2.2.2 < N + 1 - (2 * q.1.2 + q.1.1) - q.2.2.1) := by
  simp only [S, mem_sigma, mem_product, mem_range, mem_Icc]

/-- The pair of multiplicity triples attached to a parameter tuple. -/
def phi (N : ℕ) (q : Σ _ : ℕ × ℕ, ℤ × (Σ _ : ℕ, ℕ)) : Counts × Counts :=
  (⟨q.2.2.1 + q.2.1.toNat, q.2.2.2 + 2 * (-q.2.1).toNat,
      N - (2 * q.1.2 + q.1.1) - q.2.2.1 - q.2.2.2 + q.2.1.toNat⟩,
    ⟨q.2.2.1 + (-q.2.1).toNat, q.2.2.2 + 2 * q.2.1.toNat,
      N - (2 * q.1.2 + q.1.1) - q.2.2.1 - q.2.2.2 + (-q.2.1).toNat⟩)

lemma phi_mem (N : ℕ) (q : Σ _ : ℕ × ℕ, ℤ × (Σ _ : ℕ, ℕ)) (hq : q ∈ S N) :
    total (phi N q).1 = total (phi N q).2 ∧ weight (phi N q).1 = weight (phi N q).2 ∧
      total (phi N q).1 ≤ N := by
  rw [mem_S] at hq
  obtain ⟨⟨r, d⟩, δ, ⟨x, y⟩⟩ := q
  dsimp only at hq
  simp only [phi, total, weight]
  refine ⟨by omega, by omega, by omega⟩

lemma phi_injOn (N : ℕ) : Set.InjOn (phi N) (↑(S N) : Set (Σ _ : ℕ × ℕ, ℤ × (Σ _ : ℕ, ℕ))) := by
  intro q hq q' hq' h
  rw [Finset.mem_coe, mem_S] at hq hq'
  obtain ⟨⟨r, d⟩, δ, ⟨x, y⟩⟩ := q
  obtain ⟨⟨r', d'⟩, δ', ⟨x', y'⟩⟩ := q'
  simp only [phi, Prod.mk.injEq, Counts.mk.injEq] at h
  dsimp only at hq hq'
  obtain ⟨⟨e1, e2, e3⟩, e4, e5, e6⟩ := h
  have hδ : δ = δ' := by omega
  subst hδ
  have hx : x = x' := by omega
  subst hx
  have hy : y = y' := by omega
  subst hy
  have hd : d = d' := by omega
  subst hd
  have hr : r = r' := by omega
  subst hr
  rfl

lemma exists_par (N : ℕ) (p : Counts × Counts)
    (h1 : total p.1 = total p.2) (h2 : weight p.1 = weight p.2) (h3 : total p.1 ≤ N) :
    ∃ q ∈ S N, phi N q = p := by
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := p
  simp only [total, weight] at h1 h2 h3
  refine ⟨⟨((N - (a1 + a2 + a3)) % 2, ((a3 : ℤ) - b3).natAbs + (N - (a1 + a2 + a3)) / 2),
    ((a3 : ℤ) - b3, ⟨a1 - ((a3 : ℤ) - b3).toNat, a2 - 2 * (-((a3 : ℤ) - b3)).toNat⟩)⟩, ?_, ?_⟩
  · rw [mem_S]
    dsimp only
    refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega⟩
  · simp only [phi, Prod.mk.injEq, Counts.mk.injEq]
    refine ⟨⟨by omega, by omega, by omega⟩, by omega, by omega, by omega⟩

lemma arrayCount_eq (N : ℕ) : arrayCount N = (S N).card := by
  have h1 : arrayCount N = Set.ncard {p : Counts × Counts |
      total p.1 = total p.2 ∧ weight p.1 = weight p.2 ∧ total p.1 ≤ N} :=
    Nat.card_coe_set_eq {p : Counts × Counts |
      total p.1 = total p.2 ∧ weight p.1 = weight p.2 ∧ total p.1 ≤ N}
  have h2 : {p : Counts × Counts |
      total p.1 = total p.2 ∧ weight p.1 = weight p.2 ∧ total p.1 ≤ N}
      = phi N '' (↑(S N) : Set (Σ _ : ℕ × ℕ, ℤ × (Σ _ : ℕ, ℕ))) := by
    ext p
    constructor
    · rintro ⟨g1, g2, g3⟩
      obtain ⟨q, hq, hqp⟩ := exists_par N p g1 g2 g3
      exact ⟨q, hq, hqp⟩
    · rintro ⟨q, hq, rfl⟩
      exact phi_mem N q hq
  rw [h1, h2, (phi_injOn N).ncard_image, Set.ncard_coe_finset]

lemma sum_desc (M : ℕ) : ∑ x ∈ range M, (M - x) = (M + 1).choose 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ']
    have h : ∀ x, M + 1 - (x + 1) = M - x := fun x => by omega
    have e : (M + 1 + 1).choose 2 = (M + 1).choose 1 + (M + 1).choose 2 :=
      Nat.choose_succ_succ' (M + 1) 1
    simp only [h, ih]
    rw [e, Nat.choose_one_right]
    omega

lemma card_S (N : ℕ) : (S N).card =
    ∑ rd ∈ range 2 ×ˢ range (N + 1),
      (2 * rd.2 + 1) * (N + 1 - (2 * rd.2 + rd.1) + 1).choose 2 := by
  unfold S
  rw [card_sigma]
  refine sum_congr rfl (fun rd _ => ?_)
  rw [card_product, card_sigma, Int.card_Icc]
  simp only [card_range]
  rw [sum_desc]
  congr 1
  omega

lemma choose_trunc (u v : ℕ) (h : u = v ∨ (u ≤ 1 ∧ v ≤ 1)) : u.choose 2 = v.choose 2 := by
  rcases h with h | ⟨hu, hv⟩
  · rw [h]
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]

lemma sum_eq (n : ℕ) :
    ∑ rd ∈ range 2 ×ˢ range (n + 1 + 1),
      (2 * rd.2 + 1) * (n + 1 + 1 - (2 * rd.2 + rd.1) + 1).choose 2
      = alkaneCount n + alkaneCount (n + 1) := by
  have hA : ∑ d ∈ range (n + 1 + 1), (2 * d + 1) * (n + 1 + 1 - (2 * d + 0) + 1).choose 2
      = alkaneCount (n + 1) := by
    unfold alkaneCount triangle
    exact sum_congr rfl (fun d _ => by
      rw [choose_trunc (n + 1 + 1 - (2 * d + 0) + 1) (n + 1 + 2 - 2 * d) (by omega)])
  have hB : ∑ d ∈ range (n + 1 + 1), (2 * d + 1) * (n + 1 + 1 - (2 * d + 1) + 1).choose 2
      = alkaneCount n := by
    unfold alkaneCount triangle
    rw [sum_range_succ]
    have h0 : (n + 1 + 1 - (2 * (n + 1) + 1) + 1).choose 2 = 0 := by
      apply Nat.choose_eq_zero_of_lt
      omega
    rw [h0, mul_zero, add_zero]
    exact sum_congr rfl (fun d _ => by
      rw [choose_trunc (n + 1 + 1 - (2 * d + 1) + 1) (n + 2 - 2 * d) (by omega)])
  have h2 : range 2 = {0, 1} := by
    ext x
    simp only [mem_range, mem_insert, mem_singleton]
    omega
  rw [sum_product, h2, sum_pair (by norm_num)]
  dsimp only
  rw [hA, hB, add_comm]

end A005994

theorem OMA.solution : type_of% @OMA.S_oeis_a005994.main := by
  intro n
  rw [A005994.arrayCount_eq (n + 1), A005994.card_S (n + 1), A005994.sum_eq n]
