import OMAReductions.R_oeis_a048200_R1

namespace OeisA048200R1H2Proof

open OMA.S_oeis_a048200

private lemma run_nil (l : List ℕ) : run [] l = l := rfl

private lemma run_append (w₁ w₂ : List Bool) (l : List ℕ) :
    run (w₁ ++ w₂) l = run w₂ (run w₁ l) :=
  List.foldl_append

private lemma step_false_cons_cons (x y : ℕ) (t : List ℕ) :
    step (x :: y :: t) false = y :: x :: t := rfl

private lemma step_true_cons (x : ℕ) (t : List ℕ) :
    step (x :: t) true = t ++ [x] := by
  simp [step, List.rotate_cons_succ]

/-- Word `(S R)^k` of length `2 * k`. -/
private def sr : ℕ → List Bool
  | 0 => []
  | k + 1 => false :: true :: sr k

private lemma sr_length (k : ℕ) : (sr k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [sr, ih]; omega

private lemma run_sr (x : ℕ) (u v : List ℕ) :
    run (sr u.length) (x :: (u ++ v)) = x :: (v ++ u) := by
  induction u generalizing v with
  | nil => simp [sr, run]
  | cons y u' ih =>
    change run (sr u'.length) (step (step (x :: y :: (u' ++ v)) false) true) = x :: (v ++ y :: u')
    rw [step_false_cons_cons, step_true_cons]
    have hrew : (x :: (u' ++ v)) ++ [y] = x :: (u' ++ (v ++ [y])) := by simp [List.append_assoc]
    rw [hrew, ih (v ++ [y])]
    simp [List.append_assoc]

/-- Word `R^k` of length `k`. -/
private def rotW (k : ℕ) : List Bool := List.replicate k true

private lemma rotW_length (k : ℕ) : (rotW k).length = k :=
  List.length_replicate

private lemma run_rotW (u v : List ℕ) :
    run (rotW u.length) (u ++ v) = v ++ u := by
  induction u generalizing v with
  | nil => simp [rotW, run]
  | cons y u' ih =>
    change run (rotW u'.length) (step (y :: (u' ++ v)) true) = v ++ (y :: u')
    rw [step_true_cons]
    have hrew : (u' ++ v) ++ [y] = u' ++ (v ++ [y]) := by simp [List.append_assoc]
    rw [hrew, ih (v ++ [y])]
    simp [List.append_assoc]

/-- One pass bubbles `x` past `u`, then rotates `x :: s` to the back, swapping blocks. -/
private lemma run_pass (x : ℕ) (u s v : List ℕ) :
    run (sr u.length ++ rotW (s.length + 1)) (((x :: u) ++ s) ++ v) =
      v ++ (u ++ (x :: s)) := by
  rw [run_append]
  have h1 : ((x :: u) ++ s) ++ v = x :: (u ++ (s ++ v)) := by simp [List.append_assoc]
  rw [h1, run_sr x u (s ++ v)]
  have h2 : x :: ((s ++ v) ++ u) = (x :: s) ++ (v ++ u) := by simp [List.append_assoc]
  have hlen : s.length + 1 = (x :: s).length := by simp
  rw [h2, hlen, run_rotW (x :: s) (v ++ u)]
  simp [List.append_assoc]

/-- Even-case recursive word for `k ≥ 1` rounds, starting with reversed suffix length `r`. -/
private def evenWord : ℕ → ℕ → List Bool
  | 0, _ => []
  | 1, r => sr 1 ++ rotW (r + 1) ++ [false]
  | k + 2, r =>
      (sr (k + 2) ++ rotW (r + 1)) ++
      (sr (k + 2) ++ rotW (r + 1)) ++
      evenWord (k + 1) (r + 1)

private lemma evenWord_length (k r : ℕ) (hk : 1 ≤ k) :
    (evenWord k r).length = (2 * k - 1) * r + 3 * k ^ 2 + 2 * k - 1 := by
  induction k generalizing r with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      simp only [evenWord, List.length_append, sr_length, rotW_length, List.length_singleton]
      omega
    | succ m =>
      simp only [evenWord, List.length_append, sr_length, rotW_length]
      have hih := ih (r + 1) (by omega)
      rw [hih]
      have h1 : 1 ≤ (2 * (m + 1) - 1) * (r + 1) + 3 * (m + 1) ^ 2 + 2 * (m + 1) := by nlinarith
      have h2 : 1 ≤ (2 * (m + 2) - 1) * r + 3 * (m + 2) ^ 2 + 2 * (m + 2) := by nlinarith
      zify [h1, h2]
      have h3 : ((2 * (m + 1) - 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 1 := by omega
      have h4 : ((2 * (m + 2) - 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 3 := by omega
      rw [h3, h4]
      ring

private lemma run_evenWord : ∀ (k : ℕ), 1 ≤ k →
    ∀ (uA sA uB sB : List ℕ),
      uA.length = k + 1 → uB.length = k + 1 → sA.length = sB.length →
      run (evenWord k sA.length) ((uA ++ sA) ++ (uB ++ sB)) =
        (uB.reverse ++ sB) ++ (uA.reverse ++ sA) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      intro uA sA uB sB huA huB hs
      rcases uA with _ | ⟨a₀, _ | ⟨a₁, _ | _⟩⟩ <;> simp at huA
      rcases uB with _ | ⟨b₀, _ | ⟨b₁, _ | _⟩⟩ <;> simp at huB
      unfold evenWord
      rw [run_append]
      have hpass := run_pass a₀ [a₁] sA ([b₀, b₁] ++ sB)
      simp only [List.length_singleton] at hpass
      rw [show ([a₀, a₁] ++ sA) ++ ([b₀, b₁] ++ sB) = ((a₀ :: [a₁]) ++ sA) ++ ([b₀, b₁] ++ sB) by rfl]
      rw [hpass]
      change step (([b₀, b₁] ++ sB) ++ ([a₁] ++ (a₀ :: sA))) false = _
      simp [step_false_cons_cons, List.append_assoc]
    | succ m =>
      intro uA sA uB sB huA huB hs
      rcases uA with _ | ⟨x, uA'⟩
      · simp at huA
      rcases uB with _ | ⟨y, uB'⟩
      · simp at huB
      have huA' : uA'.length = m + 2 := by simp at huA; omega
      have huB' : uB'.length = m + 2 := by simp at huB; omega
      unfold evenWord
      rw [run_append, run_append]
      have hpass1 := run_pass x uA' sA (((y :: uB') ++ sB))
      rw [huA'] at hpass1
      rw [hpass1]
      have hpass2 := run_pass y uB' sB (uA' ++ (x :: sA))
      rw [huB', ← hs] at hpass2
      rw [hpass2]
      have hih := ih (by omega) uA' (x :: sA) uB' (y :: sB) huA' huB' (by simp [hs])
      simp only [List.length_cons] at hih
      rw [hih]
      simp [List.reverse_cons, List.append_assoc]

/-- Odd-case recursive word for `k ≥ 1` rounds, starting with reversed suffix length `r`. -/
private def oddWord : ℕ → ℕ → List Bool
  | 0, _ => []
  | 1, r => (sr 1 ++ rotW (r + 1)) ++ sr 2
  | k + 2, r =>
      (sr (k + 2) ++ rotW (r + 1)) ++
      (sr (k + 3) ++ rotW (r + 1)) ++
      oddWord (k + 1) (r + 1)

private lemma oddWord_length (k r : ℕ) (hk : 1 ≤ k) :
    (oddWord k r).length = (2 * k - 1) * r + 3 * k ^ 2 + 4 * k := by
  induction k generalizing r with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      simp only [oddWord, List.length_append, sr_length, rotW_length]
      omega
    | succ m =>
      simp only [oddWord, List.length_append, sr_length, rotW_length]
      have hih := ih (r + 1) (by omega)
      rw [hih]
      zify
      have h3 : ((2 * (m + 1) - 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 1 := by omega
      have h4 : ((2 * (m + 2) - 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 3 := by omega
      rw [h3, h4]
      ring

private lemma run_oddWord : ∀ (k : ℕ), 1 ≤ k →
    ∀ (uB sB uC sC t : List ℕ),
      uB.length = k + 1 → uC.length = k → sB.length = sC.length → t.length = 2 →
      run (oddWord k sB.length) ((uB ++ sB) ++ ((uC ++ t) ++ sC)) =
        ((uC.reverse ++ sC) ++ (uB.reverse ++ sB)) ++ t := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      intro uB sB uC sC t huB huC hs ht
      rcases uB with _ | ⟨b₀, _ | ⟨b₁, _ | _⟩⟩ <;> simp at huB
      rcases uC with _ | ⟨c₀, _ | _⟩ <;> simp at huC
      unfold oddWord
      rw [run_append]
      have hpass := run_pass b₀ [b₁] sB ((([c₀] ++ t) ++ sC))
      simp only [List.length_singleton] at hpass
      rw [show ([b₀, b₁] ++ sB) ++ (([c₀] ++ t) ++ sC) =
            ((b₀ :: [b₁]) ++ sB) ++ (([c₀] ++ t) ++ sC) by rfl]
      rw [hpass]
      have hrew : (([c₀] ++ t) ++ sC) ++ ([b₁] ++ (b₀ :: sB)) =
          c₀ :: (t ++ (sC ++ ([b₁, b₀] ++ sB))) := by simp [List.append_assoc]
      rw [hrew, ← ht, run_sr c₀ t (sC ++ ([b₁, b₀] ++ sB))]
      simp [List.append_assoc]
    | succ m =>
      intro uB sB uC sC t huB huC hs ht
      rcases uB with _ | ⟨x, uB'⟩
      · simp at huB
      rcases uC with _ | ⟨y, uC'⟩
      · simp at huC
      have huB' : uB'.length = m + 2 := by simp at huB; omega
      have huC' : uC'.length = m + 1 := by simp at huC; omega
      unfold oddWord
      rw [run_append, run_append]
      have hpass1 := run_pass x uB' sB ((((y :: uC') ++ t) ++ sC))
      rw [huB'] at hpass1
      rw [hpass1]
      have hrew : (((y :: uC') ++ t) ++ sC) ++ (uB' ++ (x :: sB)) =
          ((y :: (uC' ++ t)) ++ sC) ++ (uB' ++ (x :: sB)) := by simp [List.append_assoc]
      rw [hrew]
      have hlenD : (uC' ++ t).length = m + 3 := by simp [huC', ht]
      have hpass2 := run_pass y (uC' ++ t) sC (uB' ++ (x :: sB))
      rw [hlenD, ← hs] at hpass2
      rw [hpass2]
      have hih := ih (by omega) uB' (x :: sB) uC' (y :: sC) t huB' huC' (by simp [hs]) ht
      simp only [List.length_cons] at hih
      rw [hih]
      simp [List.reverse_cons, List.append_assoc]

private lemma range_split (a b : ℕ) :
    List.range (a + b) = List.range a ++ (List.range b).map (· + a) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, List.range_succ, List.range_succ, List.map_append, List.map_singleton,
        ← List.append_assoc, ih]
    simp [Nat.add_comm]

theorem main_proof : OMA.R_oeis_a048200_R1.H2 := by
  intro n hn
  constructor
  · rintro ⟨m, rfl⟩
    have hm : 2 ≤ m := by omega
    have hsplit : List.range (m + m) = List.range m ++ (List.range m).map (· + m) :=
      range_split m m
    set uA := List.range m
    set uB := (List.range m).map (· + m)
    set w := evenWord (m - 1) 0
    have hrun : run w (List.range (m + m)) = (List.range (m + m)).reverse := by
      have h1 := run_evenWord (m - 1) (by omega) uA [] uB [] (by simp [uA]; omega)
        (by simp [uB]; omega) rfl
      simp only [List.length_nil, List.append_nil] at h1
      rw [hsplit, List.reverse_append]
      exact h1
    have hlen : w.length = 3 * m ^ 2 - 4 * m := by
      have h1 := evenWord_length (m - 1) 0 (by omega)
      simp only [mul_zero, zero_add] at h1
      dsimp [w]
      rw [h1]
      have hm1 : 1 ≤ m - 1 := by omega
      have hge1 : 1 ≤ 3 * (m - 1) ^ 2 + 2 * (m - 1) := by nlinarith
      have hge2 : 4 * m ≤ 3 * m ^ 2 := by nlinarith
      zify [hge1, hge2, show 1 ≤ m by omega]
      ring
    have ha_le : a (m + m) ≤ w.length :=
      Nat.sInf_le ⟨w, rfl, hrun⟩
    have : a (m + m) ≤ 3 * m ^ 2 - 4 * m := hlen ▸ ha_le
    have hge2 : 4 * m ≤ 3 * m ^ 2 := by nlinarith
    zify [hge2] at this ⊢
    linarith
  · rintro ⟨m, rfl⟩
    have hm : 2 ≤ m := by omega
    have hsplit1 : List.range (2 * m + 1) = List.range 2 ++ (List.range (2 * m - 1)).map (· + 2) := by
      have heq : 2 * m + 1 = 2 + (2 * m - 1) := by omega
      rw [heq, range_split]
    have hsplit2 : List.range (2 * m - 1) = List.range m ++ (List.range (m - 1)).map (· + m) := by
      have heq : 2 * m - 1 = m + (m - 1) := by omega
      rw [heq, range_split]
    set uB := (List.range m).map (· + 2)
    set uC := ((List.range (m - 1)).map (· + m)).map (· + 2)
    have hrange : List.range (2 * m + 1) = 0 :: 1 :: (uB ++ uC) := by
      rw [hsplit1, hsplit2, List.map_append]
      simp [uB, uC, List.range_succ]
    set w0 : List Bool := sr 1 ++ rotW 1
    set w := w0 ++ oddWord (m - 1) 0
    have hrun : run w (List.range (2 * m + 1)) = (List.range (2 * m + 1)).reverse := by
      rw [hrange]
      dsimp [w]
      rw [run_append]
      have hstep0 : run w0 (0 :: 1 :: (uB ++ uC)) = (uB ++ uC) ++ [1, 0] := by
        have hpass := run_pass 0 [1] [] (uB ++ uC)
        simpa [w0] using hpass
      rw [hstep0]
      have hrew : (uB ++ uC) ++ [1, 0] = uB ++ (uC ++ [1, 0]) := by
        simp [List.append_assoc]
      rw [hrew]
      have h1 := run_oddWord (m - 1) (by omega) uB [] uC [] [1, 0]
        (by simp [uB]; omega) (by simp [uC]) rfl rfl
      simp only [List.length_nil, List.append_nil] at h1
      rw [h1]
      simp [List.reverse_append, List.append_assoc]
    have hlen : w.length = 3 * m ^ 2 - 2 * m + 2 := by
      dsimp [w, w0]
      rw [List.length_append, List.length_append, sr_length, rotW_length,
          oddWord_length (m - 1) 0 (by omega)]
      have hge : 2 * m ≤ 3 * m ^ 2 := by nlinarith
      zify [hge, show 1 ≤ m by omega]
      ring
    have ha_le : a (2 * m + 1) ≤ w.length :=
      Nat.sInf_le ⟨w, rfl, hrun⟩
    have : a (2 * m + 1) ≤ 3 * m ^ 2 - 2 * m + 2 := hlen ▸ ha_le
    have hge : 2 * m ≤ 3 * m ^ 2 := by nlinarith
    zify [hge] at this ⊢
    linarith

end OeisA048200R1H2Proof

theorem OMA.solution : OMA.R_oeis_a048200_R1.H2 :=
  OeisA048200R1H2Proof.main_proof
