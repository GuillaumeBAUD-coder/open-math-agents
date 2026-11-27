import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1
import Mathlib

-- Step Erdos307.erdos_307.variants.coprime_one_notMem.R1.H2: hypothesis H2 of reduction Erdos307.erdos_307.variants.coprime_one_notMem.R1
-- Credit: @ivillar
-- H2 := the closing quotients p = (M N' + N^2) / D and q = (M' N + M^2) / D (D = M N - M' N')
--   are at least 2, lie outside P0 and Q0, and keep insert p P0 and insert q Q0 pairwise coprime.
-- Proof: p, q >= 2 because 2 D bounds the numerators. The reduction's own lemma frame_cross_eq gives
-- p M' + M = N q and q N' + N = M p. A prime r dividing p and some a in P0 divides M, hence N q;
-- r cannot divide N (P0 and Q0 are mutually coprime), so r divides q, and then the second identity
-- forces r to divide N, a contradiction. So p is coprime to all of P0 (hence p is not in P0), and
-- symmetrically for q and Q0.

open Finset

namespace OMA.E307H2

lemma prime_dvd_prod {S : Finset ℕ} {r : ℕ} (hr : r.Prime) (h : r ∣ ∏ a ∈ S, a) :
    ∃ a ∈ S, r ∣ a :=
  (Prime.dvd_finsetProd_iff hr.prime _).mp h

-- If r is a prime dividing x and y, x and y are not coprime.
lemma not_cop {r x y : ℕ} (hr : r.Prime) (hx : r ∣ x) (hy : r ∣ y) : ¬ Nat.Coprime x y := by
  intro h
  exact hr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h hx hy)

-- The key coprimality: a fresh element p with p*M' + M = N*q and q*N' + N = M*p is coprime to
-- every member of P0, provided P0 and Q0 are mutually coprime.
lemma cop_new {P₀ Q₀ : Finset ℕ} {M M' N N' p q : ℕ}
    (hM : M = ∏ a ∈ P₀, a) (hN : N = ∏ b ∈ Q₀, b)
    (hPQ : ∀ a ∈ P₀, ∀ b ∈ Q₀, Nat.Coprime a b)
    (h1 : p * M' + M = N * q) (h2 : q * N' + N = M * p) :
    ∀ a ∈ P₀, Nat.Coprime p a := by
  intro a ha
  apply Nat.coprime_of_dvd
  intro r hr hrp hra
  have hrM : r ∣ M := hM ▸ dvd_trans hra (Finset.dvd_prod_of_mem _ ha)
  have hNN : ¬ r ∣ N := by
    intro hrN
    obtain ⟨b, hb, hrb⟩ := prime_dvd_prod hr (hN ▸ hrN)
    exact not_cop hr hra hrb (hPQ a ha b hb)
  have hNq : r ∣ N * q := by
    rw [← h1]
    exact dvd_add (dvd_mul_of_dvd_left hrp _) hrM
  rcases (Nat.Prime.dvd_mul hr).mp hNq with h | h
  · exact hNN h
  · apply hNN
    have : r ∣ q * N' + N := by rw [h2]; exact dvd_mul_of_dvd_left hrM _
    exact (Nat.dvd_add_right (dvd_mul_of_dvd_left h _)).mp this

end OMA.E307H2

theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H2 := by
  unfold OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H2
  intro P₀ Q₀ hP hQ hP2 hQ2 hPc hQc hPQ M M' N N' hlt h2p h2q hdp hdq p q
  have hΔ : 0 < M * N - M' * N' := Nat.sub_pos_of_lt hlt
  have hp : (M * N - M' * N') * p = M * N' + N ^ 2 := Nat.mul_div_cancel' hdp
  have hq : (M * N - M' * N') * q = M' * N + M ^ 2 := Nat.mul_div_cancel' hdq
  obtain ⟨h1, h2⟩ := OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.frame_cross_eq
    hlt rfl hp hq
  have hp2 : 2 ≤ p := (Nat.le_div_iff_mul_le hΔ).mpr (by linarith)
  have hq2 : 2 ≤ q := (Nat.le_div_iff_mul_le hΔ).mpr (by linarith)
  have hcp : ∀ a ∈ P₀, Nat.Coprime p a :=
    OMA.E307H2.cop_new rfl rfl hPQ h1 h2
  have hPQ' : ∀ b ∈ Q₀, ∀ a ∈ P₀, Nat.Coprime b a :=
    fun b hb a ha => (hPQ a ha b hb).symm
  have hcq : ∀ b ∈ Q₀, Nat.Coprime q b :=
    OMA.E307H2.cop_new rfl rfl hPQ' h2 h1
  have hpn : p ∉ P₀ := by
    intro hm
    have := (Nat.coprime_self p).mp (hcp p hm)
    omega
  have hqn : q ∉ Q₀ := by
    intro hm
    have := (Nat.coprime_self q).mp (hcq q hm)
    omega
  refine ⟨hp2, hpn, hq2, hqn, ?_, ?_⟩
  · rw [Finset.coe_insert, Set.pairwise_insert]
    exact ⟨hPc, fun a ha _ => ⟨hcp a ha, (hcp a ha).symm⟩⟩
  · rw [Finset.coe_insert, Set.pairwise_insert]
    exact ⟨hQc, fun b hb _ => ⟨hcq b hb, (hcq b hb).symm⟩⟩
