import OMAReductions.R_Erdos409_erdos_409_variants_sigma_prime_termination_R1

/-! Kernel-checked divisor-sum orbits for all starting values from 2 to 300. -/

private def step (n : ℕ) : ℕ := (n.divisorsAntidiagonalList.map Prod.fst).sum - 1

private theorem step_eq (n : ℕ) : step n = ArithmeticFunction.sigma 1 n - 1 := by
  let divs := n.divisorsAntidiagonalList.map Prod.fst
  have same : divs.toFinset = n.divisors := by
    rw [← Nat.image_fst_divisorsAntidiagonal, ← Nat.toFinset_divisorsAntidiagonalList]
    ext d
    simp [divs]
    intro _
    exact exists_congr fun _ => eq_comm
  have unique : divs.Nodup := Nat.sortedLT_map_fst_divisorsAntidiagonalList.nodup
  have sums : (∑ d ∈ divs.toFinset, d) = divs.sum := by
    simpa using List.sum_toFinset (fun d : ℕ => d) unique
  simpa [step, divs, ArithmeticFunction.sigma_one_apply] using
    congrArg (fun s : Nat => s - 1) ((same ▸ sums).symm)

private def hitsPrime : ℕ → ℕ → Bool
  | 0, n => decide n.Prime
  | j + 1, n => decide n.Prime || hitsPrime j (step n)

private theorem hitsPrime_sound (j n : ℕ) (h : hitsPrime j n = true) :
    ∃ i, ((fun m => ArithmeticFunction.sigma 1 m - 1)^[i] n).Prime := by
  induction j generalizing n with
  | zero => exact ⟨0, of_decide_eq_true h⟩
  | succ j ih =>
    change (decide n.Prime || hitsPrime j (step n)) = true at h
    simp only [Bool.or_eq_true] at h
    rcases h with hp | hnext
    · exact ⟨0, of_decide_eq_true hp⟩
    · obtain ⟨i, hi⟩ := ih _ hnext
      exact ⟨i + 1, by simpa only [Function.iterate_succ_apply, step_eq] using hi⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked2 : (List.range' 2 20).all (hitsPrime 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked22 : (List.range' 22 20).all (hitsPrime 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked42 : (List.range' 42 20).all (hitsPrime 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked62 : (List.range' 62 20).all (hitsPrime 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked82 : (List.range' 82 20).all (hitsPrime 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked102 : (List.range' 102 20).all (hitsPrime 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked122 : (List.range' 122 20).all (hitsPrime 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked142 : (List.range' 142 20).all (hitsPrime 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked162 : (List.range' 162 20).all (hitsPrime 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked182 : (List.range' 182 20).all (hitsPrime 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked202 : (List.range' 202 20).all (hitsPrime 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked222 : (List.range' 222 20).all (hitsPrime 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked242 : (List.range' 242 20).all (hitsPrime 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked262 : (List.range' 262 20).all (hitsPrime 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked282 : (List.range' 282 19).all (hitsPrime 6) = true := by
  decide +kernel

private theorem tested : (List.range' 2 299).all (hitsPrime 6) = true := by
  rw [show List.range' 2 299 =
    (List.range' 2 20) ++
    (List.range' 22 20) ++
    (List.range' 42 20) ++
    (List.range' 62 20) ++
    (List.range' 82 20) ++
    (List.range' 102 20) ++
    (List.range' 122 20) ++
    (List.range' 142 20) ++
    (List.range' 162 20) ++
    (List.range' 182 20) ++
    (List.range' 202 20) ++
    (List.range' 222 20) ++
    (List.range' 242 20) ++
    (List.range' 262 20) ++
    (List.range' 282 19) by decide +kernel]
  simp only [List.all_append, checked2, checked22, checked42, checked62, checked82, checked102, checked122,
    checked142, checked162, checked182, checked202, checked222, checked242, checked262, checked282, Bool.and_self]

theorem OMA.solution : OMA.R_Erdos409_erdos_409_variants_sigma_prime_termination_R1.H1 := by
  intro n hn hu
  exact hitsPrime_sound 6 n (List.all_eq_true.mp tested _ (List.mem_range'_1.mpr ⟨by omega, by omega⟩))
