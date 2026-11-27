import OMAReductions.R_ScholzConjecture_scholz_conjecture_R1
import Mathlib.Tactic

-- Credit: @jagong-cmu

namespace ScholzH1

lemma chain_append {C : List ℕ} {L x a b : ℕ} (hC : IsAdditionChain C)
    (hle : ∀ y ∈ C, y ≤ L) (hLx : L < x) (ha : a ∈ C) (hb : b ∈ C) (hx : x = a + b) :
    IsAdditionChain (C ++ [x]) := by
  obtain ⟨hhead, hsorted, hsum⟩ := hC
  have hne : C ≠ [] := by rintro rfl; simp at hhead
  refine ⟨?_, ?_, ?_⟩
  · cases C with
    | nil => exact absurd rfl hne
    | cons cs t => simpa using hhead
  · rw [List.pairwise_append]
    refine ⟨hsorted, List.pairwise_singleton _ _, ?_⟩
    intro y hy z hz
    rw [List.mem_singleton] at hz
    subst hz
    exact lt_of_le_of_lt (hle y hy) hLx
  · intro y hy hy1
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨u, hu, v, hv, huv⟩ := hsum y hy hy1
      exact ⟨u, List.mem_append_left _ hu, v, List.mem_append_left _ hv, huv⟩
    · rw [List.mem_singleton] at hy
      subst hy
      exact ⟨a, List.mem_append_left _ ha, b, List.mem_append_left _ hb, hx⟩

/-- `k` doublings of the last entry `L`. -/
lemma chain_double {C : List ℕ} {L : ℕ} (hC : IsAdditionChain C) (hL : L ∈ C)
    (hle : ∀ y ∈ C, y ≤ L) (hL1 : 1 ≤ L) (k : ℕ) :
    ∃ D : List ℕ, IsAdditionChain D ∧ L * 2 ^ k ∈ D ∧ (∀ y ∈ D, y ≤ L * 2 ^ k) ∧
      D.length = C.length + k ∧ ∀ y ∈ C, y ∈ D := by
  induction k with
  | zero =>
    exact ⟨C, hC, by simpa using hL, by simpa using hle, by simp, fun y hy => hy⟩
  | succ k ih =>
    obtain ⟨D, hD, hmem, hDle, hlen, hsub⟩ := ih
    have hpos : 0 < L * 2 ^ k := Nat.mul_pos hL1 (Nat.two_pow_pos k)
    have h2 : L * 2 ^ (k + 1) = L * 2 ^ k + L * 2 ^ k := by ring
    refine ⟨D ++ [L * 2 ^ (k + 1)], chain_append hD hDle (by omega) hmem hmem
      h2, by simp, ?_, by simp [hlen]; omega,
      fun y hy => List.mem_append_left _ (hsub y hy)⟩
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · have := hDle y hy
      omega
    · simp at hy; omega

lemma pow_arith (a b : ℕ) : 2 ^ (a + b) - 1 = (2 ^ a - 1) * 2 ^ b + (2 ^ b - 1) := by
  obtain ⟨A, hA⟩ : ∃ A, 2 ^ a = A + 1 := ⟨2 ^ a - 1, by have := Nat.one_le_two_pow (n := a); omega⟩
  obtain ⟨B, hB⟩ : ∃ B, 2 ^ b = B + 1 := ⟨2 ^ b - 1, by have := Nat.one_le_two_pow (n := b); omega⟩
  rw [pow_add, hA, hB]
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

lemma brauer_prefix (cs : List ℕ) (hc : IsAdditionChain cs)
    (hstar : ∀ (i : ℕ) (hi : i + 1 < cs.length), ∃ j ∈ cs, cs[i + 1] = cs[i] + j)
    (k : ℕ) (hk : k < cs.length) :
    ∃ C : List ℕ, IsAdditionChain C ∧ (∀ y ∈ C, y ≤ 2 ^ cs[k] - 1) ∧
      C.getLast? = some (2 ^ cs[k] - 1) ∧ C.length = cs[k] - 1 + k + 1 ∧
      ∀ (i : ℕ) (hi : i ≤ k), 2 ^ (cs[i]'(by omega)) - 1 ∈ C := by
  have hpos : ∀ (i : ℕ) (hi : i < cs.length), 1 ≤ cs[i] :=
    fun i hi => hc.one_le_of_mem (List.getElem_mem hi)
  induction k with
  | zero =>
    have h0 : cs[0] = 1 := by
      obtain ⟨hhead, -, -⟩ := hc
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hk] at hhead
      exact Option.some.inj hhead
    refine ⟨[1], by decide, ?_, ?_, ?_, ?_⟩
    · intro y hy; simp at hy; simp [h0, hy]
    · simp [h0]
    · simp [h0]
    · intro i hi
      have : i = 0 := by omega
      subst this; simp [h0]
  | succ k ih =>
    obtain ⟨C, hC, hCle, hClast, hClen, hCmem⟩ := ih (by omega)
    obtain ⟨j, hj, hjk⟩ := hstar k hk
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hj
    have hik : i ≤ k := by
      by_contra hcon
      have hsorted := (List.pairwise_iff_getElem.mp hc.2.1)
      have h1 := hpos k (by omega)
      rcases Nat.lt_or_ge (k + 1) i with h | h
      · have := hsorted (k + 1) i hk hi h
        omega
      · have : i = k + 1 := by omega
        subst this
        omega
    set L := 2 ^ cs[k] - 1 with hLdef
    have hck := hpos k (by omega)
    have hci := hpos i hi
    have hL1 : 1 ≤ L := by
      have : 2 ≤ 2 ^ cs[k] := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ cs[k] := Nat.pow_le_pow_right (by norm_num) hck
      omega
    have hLC : L ∈ C := List.mem_of_getLast? hClast
    obtain ⟨D, hD, hDmem, hDle, hDlen, hDsub⟩ := chain_double hC hLC hCle hL1 cs[i]
    have hB : 2 ≤ 2 ^ cs[i] := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ cs[i] := Nat.pow_le_pow_right (by norm_num) hci
    have hx : 2 ^ cs[k + 1] - 1 = L * 2 ^ cs[i] + (2 ^ cs[i] - 1) := by
      rw [hjk, pow_arith]
    have hbD : 2 ^ cs[i] - 1 ∈ D := hDsub _ (hCmem i hik)
    refine ⟨D ++ [2 ^ cs[k + 1] - 1], chain_append hD hDle (by omega) hDmem hbD hx, ?_, by simp,
      ?_, ?_⟩
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · have := hDle y hy; omega
      · simp at hy; omega
    · simp [hDlen, hClen, hjk]; omega
    · intro i' hi'
      rcases Nat.lt_or_ge i' (k + 1) with h | h
      · exact List.mem_append_left _ (hDsub _ (hCmem i' (by omega)))
      · have : i' = k + 1 := by omega
        subst this
        simp

theorem brauer (n : ℕ) (hn : 0 < n)
    (h : ∃ cs : List ℕ, IsAdditionChain cs ∧ cs.getLast? = some n ∧
      cs.length = additionChainLength n + 1 ∧
      ∀ (i : ℕ) (hi : i + 1 < cs.length), ∃ j ∈ cs, cs[i + 1] = cs[i] + j) :
    additionChainLength (2 ^ n - 1) ≤ n - 1 + additionChainLength n := by
  obtain ⟨cs, hc, hlast, hlen, hstar⟩ := h
  have hk : cs.length - 1 < cs.length := by omega
  obtain ⟨C, hC, -, hClast, hClen, -⟩ := brauer_prefix cs hc hstar (cs.length - 1) hk
  have hcn : cs[cs.length - 1] = n := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hk] at hlast
    exact Option.some.inj hlast
  rw [hcn] at hClast hClen
  exact additionChainLength_le C hC hClast (by rw [hClen]; omega)

end ScholzH1


theorem OMA.solution : OMA.R_ScholzConjecture_scholz_conjecture_R1.H1 := fun n hn h => ScholzH1.brauer n hn h
