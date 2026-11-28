import FormalConjectures.ErdosProblems.«12»

-- Problem: Erdős Problem 12 — erdos sarkozy
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/12.lean:106 (declaration Erdos12.erdos_12.variants.erdos_sarkozy)
-- Credit: @michielkosters (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Set

section Erdos12Sarkozy

private noncomputable def chooseM (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (P prevN : ℕ) : ℕ :=
  let C := Classical.choose (eventually_atTop.mp (tendsto_atTop.mp hf (4 * P + 1)))
  max 2 (max prevN C)

private noncomputable def state (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | k + 1 =>
    let (P, prevN) := state f hf k
    let m := chooseM f hf P prevN
    let blk := (Finset.Ico m (2 * m)).image (fun t => 1 + 2 * P * t)
    (P * ∏ a ∈ blk, a, 4 * P * m)

private noncomputable def P_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) : ℕ :=
  (state f hf k).1

private noncomputable def prevN_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) : ℕ :=
  (state f hf k).2

private noncomputable def m_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) : ℕ :=
  chooseM f hf (P_seq f hf k) (prevN_seq f hf k)

private noncomputable def M_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) : ℕ :=
  2 * P_seq f hf k * m_seq f hf k

private noncomputable def N_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) : ℕ :=
  4 * P_seq f hf k * m_seq f hf k

private noncomputable def blk_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) : Finset ℕ :=
  (Finset.Ico (m_seq f hf k) (2 * m_seq f hf k)).image (fun t => 1 + 2 * P_seq f hf k * t)

private lemma m_ge (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) :
    2 ≤ m_seq f hf k ∧ prevN_seq f hf k ≤ m_seq f hf k :=
  ⟨le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _)⟩

private lemma lt_f (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k n : ℕ)
    (hn : m_seq f hf k ≤ n) : 4 * P_seq f hf k < f n :=
  Classical.choose_spec (eventually_atTop.mp (tendsto_atTop.mp hf (4 * P_seq f hf k + 1))) n
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)

private lemma P_seq_pos (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) : ∀ k, 0 < P_seq f hf k
  | 0 => one_pos
  | k + 1 => by
    change 0 < P_seq f hf k * ∏ a ∈ blk_seq f hf k, a
    refine Nat.mul_pos (P_seq_pos f hf k) (Finset.prod_pos fun a ha => ?_)
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ha
    omega

private lemma mem_blk_dvd_P_seq (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) {i k a : ℕ}
    (hik : i < k) (ha : a ∈ blk_seq f hf i) : a ∣ P_seq f hf k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hik with h | rfl
    · exact dvd_trans (ih h) (dvd_mul_right _ _)
    · exact dvd_trans (Finset.dvd_prod_of_mem _ ha) (dvd_mul_left _ _)

private lemma MN (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) :
    prevN_seq f hf k < M_seq f hf k ∧ M_seq f hf k < N_seq f hf k := by
  have := P_seq_pos f hf k
  obtain ⟨h1, h2⟩ := m_ge f hf k
  unfold M_seq N_seq
  constructor <;> nlinarith

private lemma N_lt_M (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) {i j : ℕ}
    (hij : i < j) : N_seq f hf i < M_seq f hf j := by
  induction j with
  | zero => omega
  | succ j ih =>
    have h : N_seq f hf j < M_seq f hf (j + 1) := (MN f hf (j + 1)).1
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h' | rfl
    · exact (ih h').trans ((MN f hf j).2.trans h)
    · exact h

private lemma M_mono (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) : StrictMono (M_seq f hf) :=
  fun i _ h => (MN f hf i).2.trans (N_lt_M f hf h)

private lemma mem_blk (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) {k x : ℕ}
    (hx : x ∈ blk_seq f hf k) :
    M_seq f hf k < x ∧ x < N_seq f hf k ∧ x % 2 = 1 ∧ 5 ≤ x := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_Ico] at ht
  have := P_seq_pos f hf k
  have := (m_ge f hf k).1
  unfold M_seq N_seq
  exact ⟨by nlinarith, by nlinarith, by rw [mul_assoc]; omega, by nlinarith⟩

private lemma mem_blk_mod_P (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) {i k x a : ℕ}
    (hik : i < k) (ha : a ∈ blk_seq f hf i) (hx : x ∈ blk_seq f hf k) :
    ∃ q, x = 1 + a * q := by
  obtain ⟨r, hr⟩ := mem_blk_dvd_P_seq f hf hik ha
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨2 * r * t, by rw [hr]; ring⟩

private lemma blk_order (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) {i j x y : ℕ}
    (hx : x ∈ blk_seq f hf i) (hy : y ∈ blk_seq f hf j) (hxy : x < y) : i ≤ j := by
  by_contra h
  have := N_lt_M f hf (not_le.mp h)
  have := mem_blk f hf hx
  have := mem_blk f hf hy
  omega

private lemma blk_card (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (k : ℕ) :
    (blk_seq f hf k).card = m_seq f hf k := by
  rw [blk_seq, Finset.card_image_of_injective, Nat.card_Ico]
  · omega
  · intro t1 t2 ht
    have := P_seq_pos f hf k
    nlinarith

private noncomputable def A_set (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) : Set ℕ :=
  ⋃ k, (blk_seq f hf k : Set ℕ)

private lemma A_set_isGood (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) :
    Erdos12.IsGood (A_set f hf) := by
  refine ⟨infinite_of_forall_exists_gt fun B => ⟨1 + M_seq f hf B, mem_iUnion.mpr ⟨B,
    Finset.mem_image.mpr ⟨m_seq f hf B, Finset.mem_Ico.mpr ⟨le_rfl, by have := m_ge f hf B; omega⟩,
    rfl⟩⟩, by have : B ≤ M_seq f hf B := (M_mono f hf).id_le B; omega⟩, ?_⟩
  intro a ha b hb c hc hdvd hab hac
  rw [A_set, mem_iUnion] at ha hb hc
  obtain ⟨i, ha⟩ := ha
  obtain ⟨j, hb⟩ := hb
  obtain ⟨k, hc⟩ := hc
  wlog hjk : j ≤ k generalizing b c j k
  · exact (this c b (by rwa [add_comm]) hac hab k hc j hb (by omega)).symm
  obtain ⟨ha1, -, ha2, ha3⟩ := mem_blk f hf ha
  obtain ⟨-, hb1, hb2, -⟩ := mem_blk f hf hb
  obtain ⟨-, hc1, hc2, -⟩ := mem_blk f hf hc
  have hN : N_seq f hf i = 2 * M_seq f hf i := by unfold N_seq M_seq; ring
  rcases (blk_order f hf ha hb hab).lt_or_eq with hij | rfl
  · obtain ⟨q1, rfl⟩ := mem_blk_mod_P f hf hij ha hb
    obtain ⟨q2, rfl⟩ := mem_blk_mod_P f hf (hij.trans_le hjk) ha hc
    have := Nat.le_of_dvd two_pos ((Nat.dvd_add_right (dvd_mul_right a (q1 + q2))).mp
      (by convert hdvd using 1; ring))
    omega
  rcases hjk.lt_or_eq with hjk | rfl
  · obtain ⟨q, rfl⟩ := mem_blk_mod_P f hf hjk ha hc
    obtain ⟨s, hs⟩ := (Nat.dvd_add_right (dvd_mul_right a q)).mp
      (by convert hdvd using 1; ring : a ∣ a * q + (b + 1))
    have : 2 ≤ s := by nlinarith
    nlinarith
  obtain ⟨s, hs⟩ := hdvd
  have : s = 3 := by nlinarith
  subst this
  omega

end Erdos12Sarkozy

theorem OMA.solution : type_of% @Erdos12.erdos_12.variants.erdos_sarkozy := by
  intro f hf
  refine ⟨A_set f hf, A_set_isGood f hf, infinite_of_forall_exists_gt fun B =>
    ⟨N_seq f hf (B + 1), ?_, ?_⟩⟩
  · have := P_seq_pos f hf (B + 1)
    have := (m_ge f hf (B + 1)).1
    have hN : N_seq f hf (B + 1) = 4 * P_seq f hf (B + 1) * m_seq f hf (B + 1) := rfl
    have hf' := lt_f f hf (B + 1) (N_seq f hf (B + 1)) (by nlinarith)
    have hcard : m_seq f hf (B + 1) ≤ (A_set f hf ∩ Icc 1 (N_seq f hf (B + 1))).ncard := by
      rw [← blk_card, ← ncard_coe_finset]
      exact ncard_le_ncard (fun x hx => ⟨mem_iUnion.mpr ⟨_, hx⟩, by have := mem_blk f hf hx; omega,
        by have := mem_blk f hf hx; omega⟩) ((finite_Icc _ _).subset inter_subset_right)
    rw [mem_ofPred_eq, div_lt_iff₀ (by exact_mod_cast (by omega : 0 < f (N_seq f hf (B + 1))))]
    exact_mod_cast (by nlinarith : N_seq f hf (B + 1) < _ * f (N_seq f hf (B + 1)))
  · have : B + 1 ≤ M_seq f hf (B + 1) := (M_mono f hf).id_le _
    have := (MN f hf (B + 1)).2
    omega
