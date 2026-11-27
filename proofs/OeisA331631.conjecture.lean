import FormalConjectures.OEIS.«331631»

-- Problem: Tripling until the seed's digits reappear
-- Upstream: formal-conjectures FormalConjectures/OEIS/331631.lean:255 (declaration OeisA331631.conjecture)
-- Credit: @TaifengYi (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Tripling

open OeisA331631

/-- Euler's theorem gives a tripled value with the seed as its decimal suffix. -/
theorem successful (s : ℕ) : ∃ k : ℕ, 0 < k ∧ ContainsSeed s (s * 3 ^ k) := by
  let m := 10 ^ (Nat.digits 10 s).length
  have cop : Nat.Coprime 3 m := (show Nat.Coprime 3 10 by decide).pow_right _
  let k := Nat.totient m
  have hk : 0 < k := Nat.totient_pos.mpr (by dsimp [m]; positivity)
  have cong : s ≡ s * 3 ^ k [MOD m] := by
    simpa only [Nat.mul_one] using (Nat.ModEq.pow_totient cop).symm.mul_left s
  have bound : s ≤ s * 3 ^ k := Nat.le_mul_of_pos_right _ (by positivity)
  obtain ⟨q, hq⟩ := (Nat.modEq_iff_exists_eq_add bound).mp cong
  refine ⟨k, hk, [], Nat.digits 10 q, ?_⟩
  simpa only [List.nil_append, hq] using
    (Nat.digits_append_digits (b := 10) (n := s) (m := q) (by decide))

theorem stop_exists (s : ℕ) : ∃ k, StopsAt s k := by
  classical
  let h := successful s
  refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, ?_⟩
  intro j hj hlt hit
  exact Nat.find_min h hlt ⟨hj, hit⟩

noncomputable def stop (s : ℕ) : ℕ := Classical.choose (stop_exists s)

theorem stop_spec (s : ℕ) : StopsAt s (stop s) := Classical.choose_spec (stop_exists s)

theorem missing_exists (xs : List ℕ) : ∃ n : ℕ, 0 < n ∧ n ∉ xs := by
  obtain ⟨n, hn⟩ := (insert 0 xs.toFinset).exists_notMem
  simpa only [Finset.mem_insert, List.mem_toFinset, not_or, Nat.pos_iff_ne_zero] using
    (show ∃ n : ℕ, n ∉ insert 0 xs.toFinset from ⟨n, hn⟩)

def fresh (xs : List ℕ) : ℕ := Nat.find (missing_exists xs)

theorem fresh_spec (xs : List ℕ) : 0 < fresh xs ∧ fresh xs ∉ xs :=
  Nat.find_spec (missing_exists xs)

theorem fresh_le {xs : List ℕ} {n : ℕ} (hn : 0 < n) (hx : n ∉ xs) : fresh xs ≤ n :=
  Nat.find_min' (missing_exists xs) ⟨hn, hx⟩

noncomputable def history : ℕ → List ℕ
  | 0 => []
  | b + 1 =>
    let xs := history b
    xs ++ blockValues (fresh xs) (stop (fresh xs))

noncomputable def seed (b : ℕ) := fresh (history b)
noncomputable def boundary (b : ℕ) := (history b).length

theorem next_history (b : ℕ) :
    history (b + 1) = history b ++ blockValues (seed b) (stop (seed b)) := rfl

theorem next_boundary (b : ℕ) :
    boundary (b + 1) = boundary b + stop (seed b) + 1 := by
  simp only [boundary, next_history, List.length_append, block_values_length, Nat.add_assoc]

theorem boundary_mono : StrictMono boundary :=
  strictMono_nat_of_lt_succ fun b => by rw [next_boundary]; omega

theorem boundary_ge (b : ℕ) : b ≤ boundary b := boundary_mono.id_le b

theorem history_extends {b c : ℕ} (h : b ≤ c) : (history b).IsPrefix (history c) := by
  induction c, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ c _ ih => exact ih.trans ⟨_, (next_history c).symm⟩

noncomputable def term (n : ℕ) := (history (n+1))[n]'(Nat.lt_of_lt_of_le (by omega) (boundary_ge (n+1)))

theorem term_history {b n : ℕ} (hn : n < boundary b) :
    term n = (history b)[n]'hn := by
  rcases le_total (n+1) b with h | h
  · exact (history_extends h).getElem (Nat.lt_of_lt_of_le (by omega) (boundary_ge (n+1)))
  · exact ((history_extends h).getElem hn).symm

theorem mem_history {b v : ℕ} :
    v ∈ history b ↔ ∃ n < boundary b, term n = v := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨n, hn, hv⟩
    exact ⟨n, hn, (term_history hn).trans hv⟩
  · rintro ⟨n, hn, hv⟩
    exact ⟨n, hn, (term_history hn).symm.trans hv⟩

theorem block_term (b j : ℕ) (hj : j ≤ stop (seed b)) :
    term (boundary b + j) = seed b * 3 ^ j := by
  have hn : boundary b + j < boundary (b+1) := by rw [next_boundary]; omega
  rw [term_history hn]
  have idx : j < (blockValues (seed b) (stop (seed b))).length := by
    rw [block_values_length]; omega
  have entry := List.getElem_append_right' (history b) idx
  simpa only [next_history, boundary, Nat.add_comm (history b).length j,
    blockValues, List.getElem_map, List.getElem_range] using entry.symm

theorem start_term (b : ℕ) : term (boundary b) = seed b := by
  simpa using block_term b 0 (Nat.zero_le _)

theorem least_seed (b : ℕ) : LeastMissingBefore term (boundary b) (seed b) := by
  obtain ⟨pos, absent⟩ := fresh_spec (history b)
  refine ⟨⟨pos, fun n hn he => absent (mem_history.mpr ⟨n, hn, he⟩)⟩, ?_⟩
  rintro v ⟨hv, hmiss⟩
  apply fresh_le hv
  rintro h
  obtain ⟨n, hn, he⟩ := mem_history.mp h
  exact hmiss n hn he

theorem seed_mono : StrictMono seed := by
  apply strictMono_nat_of_lt_succ
  intro b
  obtain ⟨⟨hp, absent⟩, _⟩ := least_seed (b+1)
  have leq := (least_seed b).2 (seed (b+1))
    ⟨hp, fun i hi => absent i (hi.trans (boundary_mono (Nat.lt_succ_self b)))⟩
  exact lt_of_le_of_ne leq (fun he =>
    absent (boundary b) (boundary_mono (Nat.lt_succ_self b)) ((start_term b).trans he))

theorem all_positive_values (v : ℕ) (hv : 0 < v) : ∃ n, term n = v := by
  by_contra h
  have hm : MissingBefore term (boundary (v+1)) v :=
    ⟨hv, fun i _ hi => h ⟨i, hi⟩⟩
  have h₁ := (least_seed (v+1)).2 v hm
  exact (Nat.not_succ_le_self v) ((seed_mono.id_le (v+1)).trans h₁)

/-- Every index occurs in one of the successive finite intervals. -/
theorem locate (n : ℕ) : ∃ b j, j ≤ stop (seed b) ∧ n = boundary b + j := by
  have ex : ∃ k, n < boundary k := ⟨n+1, Nat.lt_of_lt_of_le (by omega) (boundary_ge (n+1))⟩
  have top : n < boundary (Nat.find ex) := Nat.find_spec ex
  cases hk : Nat.find ex with
  | zero => rw [hk] at top; exact (Nat.not_lt_zero n top).elim
  | succ b =>
    have bot : ¬ n < boundary b := Nat.find_min ex (by omega : b < Nat.find ex)
    rw [hk, next_boundary] at top
    exact ⟨b, n-boundary b, by omega, by omega⟩

/-- An intersection with a later block would put its seed inside the earlier block. -/
theorem different_blocks {b c i j : ℕ} (hbc : b < c) (hi : i ≤ stop (seed b)) :
    seed b * 3 ^ i ≠ seed c * 3 ^ j := by
  intro eqv
  have hs := seed_mono hbc
  have hji : j ≤ i := by
    by_contra! hij
    have h₁ : seed b * 3 ^ i < seed c * 3 ^ i := Nat.mul_lt_mul_of_pos_right hs (by positivity)
    have h₂ : (3:ℕ)^i ≤ 3^j := Nat.pow_le_pow_right (by decide) hij.le
    exact (h₁.trans_le (Nat.mul_le_mul_left _ h₂)).ne eqv
  have cancel : seed b * 3 ^ (i-j) = seed c := by
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (3:ℕ)^j)
    simpa only [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hji] using eqv
  have earlier : boundary b + (i-j) < boundary c := by
    have h₁ := boundary_mono.monotone (Nat.succ_le_of_lt hbc)
    rw [next_boundary] at h₁
    omega
  exact (least_seed c).1.2 _ earlier ((block_term b (i-j) (by omega)).trans cancel)

theorem distinct_terms : Function.Injective term := by
  intro n m he
  obtain ⟨b, i, hi, rfl⟩ := locate n
  obtain ⟨c, j, hj, rfl⟩ := locate m
  rw [block_term b i hi, block_term c j hj] at he
  rcases lt_trichotomy b c with h | rfl | h
  · exact (different_blocks h hi he).elim
  · have hp : 0 < seed b := (least_seed b).1.1
    have hpow := Nat.eq_of_mul_eq_mul_left hp he
    have e : i = j := (pow_right_strictMono₀ (by decide : 1 < (3:ℕ))).injective hpow
    rw [e]
  · exact (different_blocks h hj he.symm).elim

end Tripling

open Tripling in
theorem OMA.solution : type_of% @OeisA331631.conjecture := by
  refine ⟨term, ⟨boundary, fun b => stop (seed b), rfl, ?_⟩, distinct_terms, all_positive_values⟩
  intro b
  dsimp only
  rw [start_term]
  exact ⟨least_seed b, stop_spec (seed b), block_term b, next_boundary b⟩

