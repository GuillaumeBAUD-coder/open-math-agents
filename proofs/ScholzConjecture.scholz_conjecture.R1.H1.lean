import OMAReductions.R_ScholzConjecture_scholz_conjecture_R1
import Mathlib.Tactic

/-!
# Step Proof for Scholz Conjecture (`ScholzConjecture.scholz_conjecture.R1.H1`)
-/

namespace ScholzStep

lemma getLast_eq_of_getLast? {c : List ℕ} {v : ℕ} (hne : c ≠ []) (h : c.getLast? = some v) :
    c.getLast hne = v := by
  induction c with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    cases t with
    | nil => simpa using h
    | cons b u => exact ih (List.cons_ne_nil b u) (by simpa using h)

lemma append_add_last {c : List ℕ} {v w : ℕ} (hc : IsAdditionChain c)
    (hlast : c.getLast? = some v) (hw : w ∈ c) :
    IsAdditionChain (c ++ [v + w]) ∧
      (c ++ [v + w]).getLast? = some (v + w) ∧
      (c ++ [v + w]).length = c.length + 1 := by
  have hne : c ≠ [] := by
    rintro rfl
    simp at hlast
  have hv_last : c.getLast hne = v := getLast_eq_of_getLast? hne hlast
  have hv_mem : v ∈ c := hv_last ▸ List.getLast_mem hne
  refine ⟨⟨?_, ?_, ?_⟩, by simp, by simp⟩
  · cases c with
    | nil => exact absurd rfl hne
    | cons a t => simpa using hc.1
  · rw [List.pairwise_append]
    refine ⟨hc.2.1, List.pairwise_singleton _ _, ?_⟩
    intro x hx z hz
    rw [List.mem_singleton] at hz
    subst hz
    have hxv : x ≤ v := hv_last ▸ (hc.2.1.imp le_of_lt).rel_getLast hx
    have hw1 : 1 ≤ w := hc.one_le_of_mem hw
    omega
  · intro x hx hx1
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, z, hz, rfl⟩ := hc.2.2 x hx hx1
      exact ⟨y, List.mem_append_left _ hy, z, List.mem_append_left _ hz, rfl⟩
    · rw [List.mem_singleton] at hx
      subst hx
      exact ⟨v, List.mem_append_left _ hv_mem, w, List.mem_append_left _ hw, rfl⟩

lemma append_doubles (k : ℕ) {c : List ℕ} {v : ℕ} (hc : IsAdditionChain c)
    (hlast : c.getLast? = some v) :
    ∃ c' : List ℕ, IsAdditionChain c' ∧ (∀ x ∈ c, x ∈ c') ∧
      c'.getLast? = some (2 ^ k * v) ∧ c'.length = c.length + k := by
  induction k with
  | zero =>
    exact ⟨c, hc, fun _ hx => hx, by simpa using hlast, by simp⟩
  | succ k ih =>
    obtain ⟨c₁, hc₁, hsub₁, hlast₁, hlen₁⟩ := ih
    have hc₁_ne : c₁ ≠ [] := by
      rintro rfl
      simp at hlast₁
    have hmem_last : 2 ^ k * v ∈ c₁ :=
      getLast_eq_of_getLast? hc₁_ne hlast₁ ▸ List.getLast_mem hc₁_ne
    obtain ⟨hc₂, -, hlen₂⟩ := append_add_last hc₁ hlast₁ hmem_last
    have hmul : 2 ^ k * v + 2 ^ k * v = 2 ^ (k + 1) * v := by ring
    refine ⟨c₁ ++ [2 ^ k * v + 2 ^ k * v], hc₂,
      fun x hx => List.mem_append_left _ (hsub₁ x hx), ?_, ?_⟩
    · simp [hmul]
    · omega

lemma brauer_step {c : List ℕ} {a j : ℕ} (hc : IsAdditionChain c)
    (hlast : c.getLast? = some (2 ^ a - 1)) (ha : 1 ≤ a) (_hj : 1 ≤ j)
    (hmemj : 2 ^ j - 1 ∈ c) :
    ∃ c' : List ℕ, IsAdditionChain c' ∧ (∀ x ∈ c, x ∈ c') ∧
      c'.getLast? = some (2 ^ (a + j) - 1) ∧ c'.length = c.length + j + 1 := by
  obtain ⟨c₁, hc₁, hsub₁, hlast₁, hlen₁⟩ := append_doubles j hc hlast
  obtain ⟨hc₂, -, hlen₂⟩ := append_add_last hc₁ hlast₁ (hsub₁ _ hmemj)
  have hval : 2 ^ j * (2 ^ a - 1) + (2 ^ j - 1) = 2 ^ (a + j) - 1 := by
    have h2j : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hmul_sub : 2 ^ j * (2 ^ a - 1) = 2 ^ (a + j) - 2 ^ j := by
      rw [Nat.mul_sub_left_distrib, mul_one]
      have hpow : 2 ^ j * 2 ^ a = 2 ^ (a + j) := by ring
      rw [hpow]
    have hle_pow : 2 ^ j ≤ 2 ^ (a + j) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  refine ⟨c₁ ++ [2 ^ j * (2 ^ a - 1) + (2 ^ j - 1)], hc₂,
    fun x hx => List.mem_append_left _ (hsub₁ x hx), ?_, ?_⟩
  · simp [hval]
  · omega

lemma brauer_prefix {cs : List ℕ} (hcs : IsAdditionChain cs)
    (hstar : ∀ (i : ℕ) (hi : i + 1 < cs.length), ∃ j ∈ cs, cs[i + 1] = cs[i] + j) :
    ∀ (m : ℕ) (hm : m < cs.length),
      ∃ B : List ℕ, IsAdditionChain B ∧
        B.getLast? = some (2 ^ cs[m] - 1) ∧
        B.length = (cs[m] - 1) + m + 1 ∧
        ∀ (t : ℕ) (ht : t ≤ m), 2 ^ cs[t]'(Nat.lt_of_le_of_lt ht hm) - 1 ∈ B := by
  intro m
  induction m with
  | zero =>
    intro hm
    have hcs0 : cs[0] = 1 := by
      cases cs with
      | nil => simp at hm
      | cons a t =>
        have hh := hcs.1
        simpa using hh
    refine ⟨[1], ⟨rfl, List.pairwise_singleton _ _, ?_⟩, ?_, ?_, ?_⟩
    · intro x hx hx1
      exact absurd (List.mem_singleton.mp hx) hx1
    · simp [hcs0]
    · simp [hcs0]
    · intro t ht
      have ht0 : t = 0 := by omega
      subst ht0
      simp [hcs0]
  | succ m ih =>
    intro hm1
    have hm : m < cs.length := by omega
    obtain ⟨B, hB_chain, hB_last, hB_len, hB_mem⟩ := ih hm
    obtain ⟨j, hj_mem, hj_eq⟩ := hstar m hm1
    obtain ⟨t, ht_lt, hcs_t⟩ := List.mem_iff_getElem.mp hj_mem
    have ha1 : 1 ≤ cs[m] := hcs.one_le_of_mem (List.getElem_mem hm)
    have hj1 : 1 ≤ j := hcs.one_le_of_mem hj_mem
    have ht_le : t ≤ m := by
      by_contra hgt
      have hpair := List.pairwise_iff_getElem.mp hcs.2.1
      rcases eq_or_lt_of_le (by omega : m + 1 ≤ t) with heq | hlt
      · subst heq
        omega
      · have hlt_val : cs[m + 1] < cs[t] := hpair (m + 1) t hm1 ht_lt hlt
        omega
    have hj_in_B : 2 ^ j - 1 ∈ B := by
      rw [← hcs_t]
      exact hB_mem t ht_le
    obtain ⟨B', hB'_chain, hB'_sub, hB'_last, hB'_len⟩ :=
      brauer_step hB_chain hB_last ha1 hj1 hj_in_B
    rw [← hj_eq] at hB'_last
    refine ⟨B', hB'_chain, hB'_last, ?_, ?_⟩
    · omega
    · intro s hs
      rcases eq_or_lt_of_le hs with rfl | hslt
      · have hB'_ne : B' ≠ [] := by
          rintro rfl
          simp at hB'_last
        exact getLast_eq_of_getLast? hB'_ne hB'_last ▸ List.getLast_mem hB'_ne
      · exact hB'_sub _ (hB_mem s (by omega))

end ScholzStep

theorem prove_Scholz_H1 :
    ∀ n : ℕ, 0 < n →
      (∃ cs : List ℕ, IsAdditionChain cs ∧ cs.getLast? = some n ∧
        cs.length = additionChainLength n + 1 ∧
        ∀ (i : ℕ) (hi : i + 1 < cs.length), ∃ j ∈ cs, cs[i + 1] = cs[i] + j) →
      additionChainLength (2 ^ n - 1) ≤ n - 1 + additionChainLength n := by
  intro n hn ⟨cs, hcs, hlast, hlen, hstar⟩
  set l := additionChainLength n
  have hl_lt : l < cs.length := by omega
  obtain ⟨B, hB_chain, hB_last, hB_len, -⟩ := ScholzStep.brauer_prefix hcs hstar l hl_lt
  have hcs_ne : cs ≠ [] := by
    rintro rfl
    simp at hlen
  have hcs_last : cs[l] = n := by
    have h1 := ScholzStep.getLast_eq_of_getLast? hcs_ne hlast
    rw [List.getLast_eq_getElem] at h1
    have hidx : cs.length - 1 = l := by omega
    simpa [hidx] using h1
  rw [hcs_last] at hB_last hB_len
  exact additionChainLength_le B hB_chain hB_last (by omega)

theorem OMA.solution : OMA.R_ScholzConjecture_scholz_conjecture_R1.H1 :=
  prove_Scholz_H1
