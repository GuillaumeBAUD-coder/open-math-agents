import FormalConjectures.ErdosProblems.«1084»

open Real Finset

def C (x y : ℂ) := x.re * y.im - x.im * y.re

theorem L {u v : ℂ} (a b c d : ℕ) (h : C u v ≠ 0) (e : ((a : ℂ) - b) * u = (c - d) * v) : a = b := by
  simp [Complex.ext_iff] at e
  exact_mod_cast mul_left_cancel₀ h (by unfold C; linear_combination v.im * e.1 - v.re * e.2 : C u v * a = C u v * b)

theorem A (S : Finset α) (u : α → ℂ) (n : ∀ a ∈ S, ‖u a‖ = 1)
    (h : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 1 ≤ ‖u a - u b‖) :
    #S ≤ 6 ∧ (#S = 6 → (∀ a ∈ S, ∃ b ∈ S, u b = -u a) ∧ ∃ a ∈ S, ∃ b ∈ S, C (u a) (u b) ≠ 0) := by
  have := pi_pos
  have c a (ε : a ∈ S) : (u a).re = cos (u a).arg ∧ (u a).im = sin (u a).arg := by
    simp [← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg, n a ε]
  set s := S.image (u · |>.arg)
  have κ : #s = #S := card_image_of_injOn fun a ε b δ e => not_not.1 fun H => not_lt.2 (h a ε b δ H) (by simp [Complex.ext_norm_arg ((n a ε).trans (n b δ).symm) e])
  have γ : ∀ x ∈ s, ∀ y ∈ s, x < y → |y - x - π| ≤ π - π / 3 := by
    simp only [s, forall_mem_image]
    intro a ε b δ l
    by_contra! H
    have x := cos_lt_cos_of_nonneg_of_le_pi (by linarith) (abs_le.2 ⟨by linarith, by linarith [(u a).neg_pi_lt_arg, (u b).arg_le_pi]⟩) H
    have y := Complex.sq_norm (u a - u b)
    simp [cos_sub, Complex.normSq_apply, c a ε, c b δ] at x y
    nlinarith [h a ε b δ (l.ne <| · ▸ rfl), sin_sq_add_cos_sq (u a).arg, sin_sq_add_cos_sq (u b).arg]
  have τ {k} (i j : Fin k) {g : Fin k ↪o ℝ} (m : ∀ i, g i ∈ s) (l : i < j := by decide) := abs_sub_le_iff.1 (γ _ (m i) _ (m j) (g.strictMono l))
  refine ⟨?_, fun e => ?_⟩
  · by_contra! H
    have m := s.orderEmbOfCardLe_mem (by omega : 7 ≤ #s)
    linarith [(τ 0 1 m).2, (τ 1 2 m).2, (τ 2 3 m).2, (τ 3 4 m).2, (τ 4 5 m).2, (τ 5 6 m).2, (τ 0 6 m).1]
  rw [← κ] at e
  have r := s.range_orderEmbOfFin e
  have m := s.orderEmbOfFin_mem e
  set g := s.orderEmbOfFin e
  have := (τ 0 1 m).2
  have := (τ 1 2 m).2
  have := (τ 2 3 m).2
  have := (τ 3 4 m).2
  have := (τ 4 5 m).2
  have := (τ 0 5 m).1
  have q (i : Fin 6) : g (i + 3) = g i + π ∨ g (i + 3) = g i - π := by
    fin_cases i <;> simp <;> first | left; linarith | right; linarith
  simp [s] at m
  refine ⟨fun a ε => ?_, ?_⟩
  · obtain ⟨i, ι⟩ := r.ge (mem_image_of_mem _ ε)
    obtain ⟨b, δ, f⟩ := m (i + 3)
    exact ⟨b, δ, by rcases q i with h | h <;> simp [Complex.ext_iff, c a ε, c b δ, f, ← ι, h]⟩
  obtain ⟨a, ε, f⟩ := m 0
  obtain ⟨b, δ, f'⟩ := m 1
  refine ⟨a, ε, b, δ, ne_of_gt ?_⟩
  simp [C, c a ε, c b δ, f, f']
  linarith [sin_sub (g 1) (g 0), sin_pos_of_pos_of_lt_pi (x := g 1 - g 0) (by linarith) (by linarith)]

theorem OMA.solution : type_of% @Erdos1084.erdos_1084.variants.upper_d2 := by
  refine ⟨1 / 28, by norm_num, fun n ν => ?_⟩
  suffices Erdos1084.f 2 n ≤ ⌊(3 * n - √n / 14 : ℝ)⌋₊ by linarith [(Nat.le_floor_iff (by linarith [sqrt_le_self_iff.2 (.inr (Nat.one_le_cast.2 ν))])).1 this, sqrt_pos.2 (Nat.cast_pos.2 ν)]
  refine ciSup_le' fun S => ciSup_le' fun o => ciSup_le' fun w => Nat.le_floor ?_
  subst o
  let G : SimpleGraph S := { Adj x y := dist x.1 y.1 = 1, symm := ⟨fun _ _ => (dist_comm ..).trans⟩ }
  let e := Complex.orthonormalBasisOneI.repr.symm
  let p (a : S) := e a
  have N a := A (G.neighborFinset a) (p a - p ·) (fun b δ => by simpa [p, ← dist_eq_norm, G] using δ) fun b _ c _ h => by
    simpa [p, ← dist_eq_norm, edist_dist] using w c.2 b.2 (mt Subtype.ext h.symm)
  set B : Finset S := {a | ¬ G.degree a = 6} with β
  let Q := B.sigma (G.neighborFinset ·)
  let R a (q : Σ _ : S, S) := ∃ k : ℕ, p q.1 = p a + k * (p q.1 - p q.2)
  have T a b (h : b ∈ G.neighborFinset a) : ∃ q ∈ Q, R a q ∧ p q.1 - p q.2 = p a - p b := by
    by_contra! H
    have (k : ℕ) : ∃ x y, x ∈ G.neighborFinset y ∧ p y - p x = p a - p b ∧ p y = p a + k * (p a - p b) :=
      Nat.rec ⟨b, a, h, rfl, by simp⟩ (fun k ⟨x, y, m, ρ, σ⟩ => let ⟨z, φ, f⟩ := ((N y).2 (not_not.1 fun c => H ⟨y, x⟩ (by simpa [Q, B, m] using c) ⟨k, ρ ▸ σ⟩ ρ)).1 x m; ⟨y, z, by simpa [G.adj_comm] using φ, by linear_combination ρ - f, by push_cast; linear_combination σ + ρ - f⟩) k
    choose x y _ _ σ using this
    exact not_injective_infinite_finite y fun i j m => by
      have := σ j
      rw [← m, σ] at this
      simpa [p, sub_eq_zero, G.ne_of_adj ((G.mem_neighborFinset ..).1 h)] using this
  have : #Bᶜ ≤ #(Q ×ˢ Q) := card_le_card_of_forall_subsingleton (fun a q => R a q.1 ∧ R a q.2 ∧ C (p q.1.1 - p q.1.2) (p q.2.1 - p q.2.2) ≠ 0) (fun a ε => by
      obtain ⟨b, δ, c, κ, Ω⟩ := ((N a).2 (by simpa [B] using ε)).2
      obtain ⟨q, χ, ψ, ρ⟩ := T a b δ
      obtain ⟨q', χ', ω, ρ'⟩ := T a c κ
      exact ⟨(q, q'), mem_product.2 ⟨χ, χ'⟩, ψ, ω, ρ ▸ ρ' ▸ Ω⟩) fun q _ => by
    rintro a ⟨_, ⟨k, ξ⟩, ⟨l, z⟩, Ω⟩ a' ⟨_, ⟨k', ζ⟩, ⟨l', η⟩, _⟩
    obtain rfl := L k k' l l' Ω (by linear_combination ζ - ξ - η + z)
    exact Subtype.ext (e.injective (by linear_combination ζ - ξ))
  have t : #Q ≤ #B * 6 := by rw [card_sigma]; exact sum_le_card_nsmul _ _ _ fun b _ => (N b).1
  have : #Bᶜ + #B = #S := (card_compl_add_card B).trans (by simp)
  have : unitDistNum S ≤ #G.edgeFinset := card_le_card_of_surjOn (Sym2.map Subtype.val) fun k ψ => by
    obtain ⟨μ, ρ⟩ := mem_filter.1 ψ
    obtain ⟨x, y⟩ := mk_mem_sym2_iff.1 ((Quot.out_eq k).symm ▸ μ)
    exact ⟨s(⟨_, x⟩, ⟨_, y⟩), G.mem_edgeFinset.2 ρ, Quot.out_eq k⟩
  have z := sum_le_card_nsmul univ (fun a => G.degree a + if ¬ G.degree a = 6 then 1 else 0) 6 fun a _ => by
    have : G.degree a ≤ 6 := (N a).1
    split <;> omega
  rw [sum_add_distrib, ← card_filter, G.sum_degrees_eq_twice_card_edges, card_univ, Fintype.card_coe, smul_eq_mul, ← β] at z
  linarith [(sqrt_le_left (by positivity)).2 (by norm_cast; nlinarith [t, Nat.le_mul_self #B, card_product Q Q] : (#S : ℝ) ≤ (7 * #B) ^ 2), (by norm_cast; omega : (2 * unitDistNum S + #B : ℝ) ≤ 6 * #S)]

