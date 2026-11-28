import FormalConjectures.ErdosProblems.«1075»

/-!
# Erdős 1075 — a reduction that isolates the ε → 0 core

Problem: Erdős Problem 1075 (lefttosolve.com/p/Erdos1075.erdos_1075).
Credit: @MBimrose

The statement asks for a single constant `c > r^{-r}` such that every `r`-uniform
hypergraph on `n` vertices with at least `(1+ε)(n/r)^r` edges has an `m`-vertex
subgraph (`m = m(n) → ∞`) whose edge density `e(S)/|S|^r` is at least `c`, for
*every* `ε > 0`.  Two facts structure the problem (both checked by hand, see the
artifact dir):

* `1 + ε` only ever helps: the hypothesis is *weaker* for larger `ε`.  Hence the
  whole content of the statement sits in the regime `ε < 1` (indeed `ε → 0`), and
  it is enough to know the claim for `ε ≤ 1/2`.  That is `H1` below: the
  "`r^{-r}` is a jump" step, in the limit `ε → 0`, which is exactly the open
  mathematical content (Erdős's jump problem for `r`-graphs).

* For the remaining, *large* `ε` the statement is reachable by counting only.
  The double-counting (averaging) identity

      ∑_{S : |S| = s} #{e ∈ H : e ⊆ S} = e(H) * C(n-r, s-r)

  gives, for **every** `r ≤ s ≤ n`, an `s`-set `S` with
  `e(S) ≥ (1+ε) * ((s-r+1)/r)^r`; taking `s` a fixed fraction of `n` and using
  `ε > 1/2` beats any constant below `9/(8 r^r)`.  That statement is `H2`; it is
  the free half of the proof, and it is true unconditionally (it is the lemma a
  proof of `H1` will have to improve on).

So `main` proves the target from `H1` (the open core) and `H2` (the counting
step), with `c = min c₁ (9/(8 r^r))`.  Both hypotheses are used: `H1` covers
`ε ≤ 1/2`, `H2` covers `ε > 1/2` at the scale `s = n / (8r²)`.
-/

namespace OMA.R_Erdos1075_erdos_1075_R1

open Filter

/-- **The counting (averaging) step.**  If `H` is an `r`-uniform hypergraph on
`n` vertices with at least `(1+ε)(n/r)^r` edges, then for every `r ≤ s ≤ n`
there is an `s`-vertex set spanning at least `(1+ε)((s-r+1)/r)^r` edges.

This is exact double counting and is true for all `r`, `ε > 0`, with no
asymptotics: `#` of `s`-sets containing a fixed `r`-edge is `C(n-r, s-r)`, and
`C(n-r,s-r)/C(n,s) = ∏_{i<r} (s-i)/(n-i) ≥ ((s-r+1)/n)^r`. -/
def H2 : Prop :=
  ∀ (n r s : ℕ), 0 < r → r ≤ s → s ≤ n →
    ∀ H : Finset (Finset (Fin n)), H.IsUniform r →
      ∀ ε : ℝ, 0 < ε → (1 + ε) * ((n : ℝ) / r) ^ r ≤ (H.card : ℝ) →
        ∃ S : Finset (Fin n), S.card = s ∧
          (1 + ε) * (((s : ℝ) - (r - 1)) / r) ^ r ≤
            ((H.hypergraphInduce S).card : ℝ)

/-- **The open core: `r^{-r}` is a jump, in the limit `ε → 0`.**  There is a
constant `c > r^{-r}` (independent of `ε`) such that for every `ε ≤ 1/2` the
conclusion of Erdős 1075 holds.  By the monotonicity of the hypothesis in `ε`
this is the entire mathematical content of the problem; it is *strictly* what
happens as `ε → 0`, where averaging only gives density `(1+ε)/r^r → r^{-r}`.

`H1` is not the target verbatim: it restricts to `ε ≤ 1/2` and thereby fixes the
only regime in which the statement is not immediate.  Its satisfiability side is
non-vacuous: for `r = 3` the hypothesis is satisfiable whenever
`1 + ε ≤ r^r/r! = 4.5` (see the artifact), so `ε ≤ 1/2` is deep inside the
non-vacuous range. -/
def H1 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ c : ℝ, ((r : ℝ))⁻¹ ^ r < c ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧
      ∀ᶠ n : ℕ in atTop, ∀ H : Finset (Finset (Fin n)), H.IsUniform r →
        (1 + ε) * ((n : ℝ) / r) ^ r ≤ (H.card : ℝ) →
          ∃ S : Finset (Fin n), S.card = m n ∧
            c * (S.card : ℝ) ^ r ≤ ((H.hypergraphInduce S).card : ℝ)

theorem main : H1 → H2 → type_of% @Erdos1075.erdos_1075 := by
  intro h1 h2 r hr
  obtain ⟨c₁, hc₁, hstep⟩ := h1 r hr
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hpow : (0 : ℝ) < (r : ℝ) ^ r := pow_pos hr0 r
  refine ⟨min c₁ (9 / (8 * (r : ℝ) ^ r)), ?_, ?_⟩
  · rw [lt_min_iff]
    refine ⟨hc₁, ?_⟩
    have hkey : ((r : ℝ))⁻¹ ^ r = 1 / (r : ℝ) ^ r := by
      rw [inv_pow, one_div]
    have hkey2 : 9 / (8 * (r : ℝ) ^ r) = (9 / 8) * (1 / (r : ℝ) ^ r) := by
      have hne : (r : ℝ) ^ r ≠ 0 := ne_of_gt hpow
      field_simp
    rw [hkey, hkey2]
    have hpos : (0 : ℝ) < 1 / (r : ℝ) ^ r := by positivity
    nlinarith
  · intro ε hε
    by_cases hsmall : ε ≤ 1 / 2
    · obtain ⟨m, hm, hfin⟩ := hstep ε hε hsmall
      refine ⟨m, hm, ?_⟩
      filter_upwards [hfin] with n hn H hU hcard
      obtain ⟨S, hS, hle⟩ := hn H hU hcard
      exact ⟨S, hS, (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans hle⟩
    · -- large ε: run the counting step at the scale s = n / (8r²)
      have hbig : 1 / 2 < ε := lt_of_not_ge hsmall
      set K : ℕ := 8 * r * r with hKdef
      have hK : 0 < K := by
        have : 0 < r := by omega
        simp only [hKdef]
        positivity
      have hhalf : (3 : ℝ) / 2 ≤ 1 + ε := by linarith
      refine ⟨fun n => n / K, ?_, ?_⟩
      · rw [tendsto_atTop_atTop]
        intro N
        refine ⟨N * K, fun n hn => ?_⟩
        exact (Nat.le_div_iff_mul_le hK).2 (by simpa [Nat.mul_comm] using hn)
      · filter_upwards [eventually_ge_atTop (K * (8 * r * (r - 1)))] with n hn H hU hcard
        have hM : 8 * r * (r - 1) ≤ n / K :=
          (Nat.le_div_iff_mul_le hK).2 (by simpa [Nat.mul_comm] using hn)
        have hsle : n / K ≤ n := Nat.div_le_self _ _
        have hdle : r ≤ 8 * r * (r - 1) := by
          have h1 : 1 ≤ 8 * (r - 1) := by omega
          calc r = r * 1 := by ring
            _ ≤ r * (8 * (r - 1)) := Nat.mul_le_mul_left r h1
            _ = 8 * r * (r - 1) := by ring
        obtain ⟨S, hS, hle⟩ := h2 n r (n / K) (by omega) (le_trans hdle hM) hsle H hU ε hε hcard
        refine ⟨S, hS, ?_⟩
        rw [hS]
        -- rewrite the Nat-subtraction cast `↑(r-1)` as `↑r - 1`, in `hle` and in the goal
        have hrcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ r)]
          norm_num
        set s : ℕ := n / K with hsdef
        have hs0 : (0 : ℝ) < (s : ℝ) := by
          have : 0 < s := lt_of_lt_of_le (by omega : 0 < r) (le_trans hdle hM)
          exact_mod_cast this
        have hsR : (8 : ℝ) * (r : ℝ) * ((r : ℝ) - 1) ≤ (s : ℝ) := by
          have hcast : ((8 * r * (r - 1) : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hM
          have heq : ((8 * r * (r - 1) : ℕ) : ℝ) = (8 : ℝ) * (r : ℝ) * ((r : ℝ) - 1) := by
            push_cast [hrcast]
            ring
          linarith
        have hr1 : (0 : ℝ) ≤ (r : ℝ) - 1 := by linarith
        have hmul : (r : ℝ) - 1 ≤ (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
        have hstep1 : (r : ℝ) * ((r : ℝ) - 1) ≤ (s : ℝ) / 8 := by linarith
        have hx8 : ((r : ℝ) - 1) / (s : ℝ) ≤ 1 / 8 := by
          rw [div_le_iff₀ hs0]
          linarith
        have hx1 : (0 : ℝ) ≤ 1 - ((r : ℝ) - 1) / (s : ℝ) := by linarith
        -- Bernoulli: `(1 - x)^r ≥ 1 - r x`
        have hbern : 1 + (r : ℝ) * ((1 - ((r : ℝ) - 1) / (s : ℝ)) - 1) ≤
            (1 - ((r : ℝ) - 1) / (s : ℝ)) ^ r := by
          apply one_add_mul_sub_le_pow
          linarith
        have h7 : (7 : ℝ) / 8 ≤ (1 - ((r : ℝ) - 1) / (s : ℝ)) ^ r := by
          have hprod : (r : ℝ) * (((r : ℝ) - 1) / (s : ℝ)) ≤ 1 / 8 := by
            have hid : (r : ℝ) * (((r : ℝ) - 1) / (s : ℝ)) =
                ((r : ℝ) * ((r : ℝ) - 1)) / (s : ℝ) := by
              field_simp
            rw [hid, div_le_iff₀ hs0]
            linarith
          linarith
        have hmain : (9 : ℝ) / 8 ≤ (1 + ε) * (1 - ((r : ℝ) - 1) / (s : ℝ)) ^ r := by
          have h3 : (3 / 2 : ℝ) * (7 / 8 : ℝ) ≤
              (1 + ε) * (1 - ((r : ℝ) - 1) / (s : ℝ)) ^ r :=
            mul_le_mul hhalf h7 (by norm_num) (by linarith)
          linarith
        -- multiply by `(s/r)^r`
        have hbase : ((s : ℝ) - ((r : ℝ) - 1)) / (r : ℝ) =
            (1 - ((r : ℝ) - 1) / (s : ℝ)) * ((s : ℝ) / (r : ℝ)) := by
          have hsne : (s : ℝ) ≠ 0 := ne_of_gt hs0
          have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
          field_simp
        have hbig2 : (9 / (8 * (r : ℝ) ^ r)) * (s : ℝ) ^ r ≤
            (1 + ε) * (((s : ℝ) - ((r : ℝ) - 1)) / (r : ℝ)) ^ r := by
          have hA : (0 : ℝ) ≤ (s : ℝ) ^ r / (r : ℝ) ^ r := by positivity
          have key := mul_le_mul_of_nonneg_right hmain hA
          rw [hbase, mul_pow, div_pow]
          have e1 : (9 / (8 * (r : ℝ) ^ r)) * (s : ℝ) ^ r =
              (9 / 8) * ((s : ℝ) ^ r / (r : ℝ) ^ r) := by
            field_simp
          rw [e1]
          calc (9 / 8) * ((s : ℝ) ^ r / (r : ℝ) ^ r)
              ≤ ((1 + ε) * (1 - ((r : ℝ) - 1) / (s : ℝ)) ^ r) *
                  ((s : ℝ) ^ r / (r : ℝ) ^ r) := key
            _ = (1 + ε) * ((1 - ((r : ℝ) - 1) / (s : ℝ)) ^ r *
                  ((s : ℝ) ^ r / (r : ℝ) ^ r)) := by ring
        exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans
          (le_trans hbig2 hle)

end OMA.R_Erdos1075_erdos_1075_R1
