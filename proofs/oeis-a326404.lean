import OMAStatements.S_oeis_a326404

-- Problem: A326404: Triangle T(n,k) read by rows: T(n,k) = number of ways of seating n people around a table for the second time so that k pairs are maintained. Rotated sequences are counted as one.
-- Upstream: statements/oeis-a326404.lean (declaration OMA.S_oeis_a326404.main), Lean statement by @KoaOkano
-- Credit: @timlantin (the owner of the agent is credited as the solver)
-- Written with Claude Code (AI-assisted).

/-
OEIS A326404, conjecture of Witold Tatkiewicz (2019): among the circular seatings of n >= 3
people, counted up to rotation, the average number of originally adjacent pairs that are kept
is 2/(n-1) + 2, and it tends to 2.

Proof (linearity of expectation; no outside source or earlier proof was used). A seating is a
conjugate c of the rotation r. Conjugating by the transposition (v v') shows that, for a fixed
seat u, the number of seatings with c u = v is the same for every v other than u, so it is
K/(n-1), where K is the number of seatings (c u = u never happens). The seat x keeps its
clockwise neighbour r x exactly when c x = r x or c (r x) = x, and these two events are
disjoint for n >= 3 because c has no 2-cycle. Summing over the n seats, the kept pairs total
2*n*K/(n-1), so the average is 2*n/(n-1) = 2/(n-1) + 2.
-/

open Finset Filter Topology OMA.S_oeis_a326404

set_option maxHeartbeats 1600000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a326404.main := by
  classical
  have key : ∀ n : ℕ, 3 ≤ n → mean n = 2/((n:ℝ)-1)+2 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have r1 : ∀ z : Fin (m+3), finRotate (m+3) z ≠ z := by
      intro z h
      rw [finRotate_apply] at h
      exact one_ne_zero (add_eq_left.mp h)
    have r2 : ∀ z : Fin (m+3), finRotate (m+3) (finRotate (m+3) z) ≠ z := by
      intro z h
      rw [finRotate_apply, finRotate_apply, add_assoc] at h
      have h' : (1 + 1 : Fin (m+3)) = 0 := add_eq_left.mp h
      have h'' := congrArg Fin.val h'
      simp [Fin.val_add] at h''
      rw [Nat.mod_eq_of_lt (by omega)] at h''
      omega
    have hC : ∀ c : Equiv.Perm (Fin (m+3)), c ∈ circles (m+3) ↔
        ∃ σ : Equiv.Perm (Fin (m+3)), relabel σ (finRotate (m+3)) = c := by
      intro c
      simp [circles]
    have hconj : ∀ (τ c : Equiv.Perm (Fin (m+3))), c ∈ circles (m+3) →
        relabel τ c ∈ circles (m+3) := by
      intro τ c hc
      obtain ⟨σ, rfl⟩ := (hC c).1 hc
      exact (hC _).2 ⟨σ.trans τ, by ext x; simp [relabel]⟩
    have c1 : ∀ c ∈ circles (m+3), ∀ x, c x ≠ x := by
      intro c hc x h
      obtain ⟨σ, rfl⟩ := (hC c).1 hc
      have h1 : σ (finRotate (m+3) (σ.symm x)) = x := h
      exact r1 (σ.symm x) ((Equiv.eq_symm_apply σ).2 h1)
    have c2 : ∀ c ∈ circles (m+3), ∀ x, c (c x) ≠ x := by
      intro c hc x h
      obtain ⟨σ, rfl⟩ := (hC c).1 hc
      have h1 : σ (finRotate (m+3) (σ.symm (σ (finRotate (m+3) (σ.symm x))))) = x := h
      rw [Equiv.symm_apply_apply] at h1
      exact r2 (σ.symm x) ((Equiv.eq_symm_apply σ).2 h1)
    have sym : ∀ u v v' : Fin (m+3), v ≠ u → v' ≠ u →
        ((circles (m+3)).filter (fun c => c u = v)).card =
          ((circles (m+3)).filter (fun c => c u = v')).card := by
      intro u v v' hv hv'
      refine Finset.card_nbij' (fun c => relabel (Equiv.swap v v') c)
        (fun c => relabel (Equiv.swap v v') c) ?_ ?_ ?_ ?_
      · intro c hc
        rw [Finset.mem_coe, Finset.mem_filter] at hc ⊢
        refine ⟨hconj _ _ hc.1, ?_⟩
        show Equiv.swap v v' (c ((Equiv.swap v v').symm u)) = v'
        rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hv.symm hv'.symm, hc.2,
          Equiv.swap_apply_left]
      · intro c hc
        rw [Finset.mem_coe, Finset.mem_filter] at hc ⊢
        refine ⟨hconj _ _ hc.1, ?_⟩
        show Equiv.swap v v' (c ((Equiv.swap v v').symm u)) = v
        rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hv.symm hv'.symm, hc.2,
          Equiv.swap_apply_right]
      · intro c _
        ext x
        simp [relabel]
      · intro c _
        ext x
        simp [relabel]
    have cnt : ∀ u v : Fin (m+3), v ≠ u →
        (m+2) * ((circles (m+3)).filter (fun c => c u = v)).card = (circles (m+3)).card := by
      intro u v hv
      have h0 : ((circles (m+3)).filter (fun c => c u = u)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro c hc
        exact c1 c hc u
      have hs := Finset.card_eq_sum_card_fiberwise (s := circles (m+3))
        (t := (Finset.univ : Finset (Fin (m+3)))) (f := fun c => c u)
        (fun c _ => Finset.mem_univ _)
      beta_reduce at hs
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u), h0, zero_add,
        Finset.sum_congr rfl (fun w hw => sym u w v (Finset.ne_of_mem_erase hw) hv),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ,
        Fintype.card_fin, smul_eq_mul] at hs
      rw [hs]
      rfl
    have per : ∀ x : Fin (m+3),
        (m+2) * ((circles (m+3)).filter (fun c => adjacent c x (finRotate (m+3) x))).card =
          2 * (circles (m+3)).card := by
      intro x
      have e : (circles (m+3)).filter (fun c => adjacent c x (finRotate (m+3) x)) =
          (circles (m+3)).filter (fun c => c x = finRotate (m+3) x) ∪
            (circles (m+3)).filter (fun c => c (finRotate (m+3) x) = x) := by
        ext c
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter,
          ← and_or_left]
        rfl
      have d : Disjoint ((circles (m+3)).filter (fun c => c x = finRotate (m+3) x))
          ((circles (m+3)).filter (fun c => c (finRotate (m+3) x) = x)) := by
        rw [Finset.disjoint_left]
        intro c h1 h2
        rw [Finset.mem_filter] at h1 h2
        apply c2 c h1.1 x
        rw [h1.2, h2.2]
      rw [e, Finset.card_union_of_disjoint d, mul_add, cnt x _ (r1 x), cnt _ x (r1 x).symm,
        two_mul]
    have total : ((m:ℝ)+2) * ∑ c ∈ circles (m+3), (kept c : ℝ) =
        2 * ((m:ℝ)+3) * ((circles (m+3)).card : ℝ) := by
      have hk : ∀ c : Equiv.Perm (Fin (m+3)), (kept c : ℝ) =
          ∑ x : Fin (m+3), if adjacent c x (finRotate (m+3) x) then (1:ℝ) else 0 := by
        intro c
        unfold kept
        rw [Finset.natCast_card_filter]
      have hx : ∀ x : Fin (m+3), ((m:ℝ)+2) * ∑ c ∈ circles (m+3),
          (if adjacent c x (finRotate (m+3) x) then (1:ℝ) else 0) =
            2 * ((circles (m+3)).card : ℝ) := by
        intro x
        rw [← Finset.natCast_card_filter]
        exact_mod_cast per x
      rw [Finset.sum_congr rfl (fun c _ => hk c), Finset.sum_comm, Finset.mul_sum,
        Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    have hK : 0 < (circles (m+3)).card :=
      Finset.card_pos.mpr ⟨_, (hC _).2 ⟨1, rfl⟩⟩
    have hle : ∀ c : Equiv.Perm (Fin (m+3)), kept c ∈ Finset.range (m+3+1) := by
      intro c
      rw [Finset.mem_range, Nat.lt_succ_iff]
      have h1 : kept c ≤ (Finset.univ : Finset (Fin (m+3))).card := by
        unfold kept
        exact Finset.card_filter_le _ _
      simpa using h1
    have den : ∑ k ∈ Finset.range (m+3+1), (entry (m+3) k : ℝ) =
        ((circles (m+3)).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise (s := circles (m+3))
        (t := Finset.range (m+3+1)) (f := fun c => kept c) (fun c _ => hle c)]
      push_cast
      rfl
    have num : ∑ k ∈ Finset.range (m+3+1), (k:ℝ) * (entry (m+3) k : ℝ) =
        ∑ c ∈ circles (m+3), (kept c : ℝ) := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := circles (m+3))
        (t := Finset.range (m+3+1)) (g := fun c => kept c) (fun c _ => hle c)
        (fun c => (kept c : ℝ))]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_congr rfl (fun c hc => by rw [(Finset.mem_filter.mp hc).2] :
        ∀ c ∈ (circles (m+3)).filter (fun c => kept c = k), (kept c : ℝ) = (k:ℝ)),
        Finset.sum_const, nsmul_eq_mul, mul_comm]
      rfl
    have hK' : (0:ℝ) < ((circles (m+3)).card : ℝ) := by exact_mod_cast hK
    have hm : (0:ℝ) < (m:ℝ) + 2 := by positivity
    unfold mean
    rw [num, den, div_eq_iff hK'.ne']
    have e3 : (((m+3 : ℕ) : ℝ)) - 1 = (m:ℝ) + 2 := by push_cast; ring
    rw [e3]
    field_simp
    linarith [total]
  refine ⟨key, ?_⟩
  have h0 : Tendsto (fun n : ℕ => 2/((n:ℝ)-1)) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_atTop_add_const_right _ (-1) tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => 2/((n:ℝ)-1)+2) atTop (𝓝 2) := by
    simpa using h0.add_const 2
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact (key n hn).symm
