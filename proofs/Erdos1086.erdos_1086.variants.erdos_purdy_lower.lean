import FormalConjectures.ErdosProblems.«1086»

-- Problem: Erdős Problem 1086 — erdos purdy lower
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1086.lean:88 (declaration Erdos1086.erdos_1086.variants.erdos_purdy_lower)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Proof: Erdős–Purdy grid construction. In the grid [0,3K]^2, count ordered triples p, p+v, p+w
-- with det(v,w) = t! (t! < K): v = h(x,y) with h ≤ t, (x,y) coprime (density ≥ 1/4), and w running
-- over h lattice points of the line det(v,w) = t! (Bezout). This gives ≫ K^4 · H_t ≥ K^4 log(t+1),
-- and log(t+1) ≫ log log n.


open Finset




open Filter Asymptotics

namespace OMAx
lemma bez (x γ e : ℕ) : ∃ d0 b0 : ℤ, (0 < x → 0 < γ → Nat.Coprime x γ →
    0 ≤ d0 ∧ d0 < γ ∧ (x:ℤ) * d0 - γ * b0 = e ∧ -(e:ℤ) ≤ b0 ∧ b0 < x) := by
  by_cases hh : 0 < x ∧ 0 < γ ∧ Nat.Coprime x γ
  · obtain ⟨hx, hγ, hc⟩ := hh
    have hg : Int.gcd (x:ℤ) (γ:ℤ) = 1 := by simpa [Int.gcd_natCast_natCast] using hc
    have hb := Int.gcd_eq_gcd_ab (x:ℤ) (γ:ℤ)
    rw [hg] at hb
    set a := Int.gcdA (x:ℤ) γ
    set b := Int.gcdB (x:ℤ) γ
    set d := (e:ℤ) * a
    have hγz : (0:ℤ) < γ := by exact_mod_cast hγ
    refine ⟨d % γ, -(e:ℤ) * b - x * (d / γ), fun _ _ _ => ?_⟩
    have h1 : d % γ + γ * (d / γ) = d := by linarith [Int.mul_ediv_add_emod d γ]
    have h0 : 0 ≤ d % γ := Int.emod_nonneg _ hγz.ne'
    have h2 : d % γ < γ := Int.emod_lt_of_pos _ hγz
    have key : (x:ℤ) * (d % γ) - γ * (-(e:ℤ) * b - x * (d / γ)) = e := by
      have : (x:ℤ) * d - γ * (-(e:ℤ) * b) = e := by
        simp only [d]; linear_combination (e:ℤ) * hb.symm
      linear_combination this + (x:ℤ) * h1
    refine ⟨h0, h2, key, ?_, ?_⟩
    · set B := -(e:ℤ) * b - x * (d / γ)
      have hx0 : (0:ℤ) ≤ x := by positivity
      have : (γ:ℤ) * B ≥ -(e:ℤ) := by nlinarith
      by_contra hcon
      push Not at hcon
      nlinarith
    · set B := -(e:ℤ) * b - x * (d / γ)
      have hxz : (0:ℤ) < x := by exact_mod_cast hx
      have he : (0:ℤ) ≤ e := by positivity
      have : (γ:ℤ) * B < γ * x := by nlinarith
      exact lt_of_mul_lt_mul_left this hγz.le
  · exact ⟨0, 0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hh⟩

lemma sum_inv_sq (L : ℕ) (hL : 2 ≤ L) :
    ∑ d ∈ Icc 2 L, (1:ℝ) / (d:ℝ)^2 ≤ 3/4 - 1/(L:ℝ) := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hL' : (2:ℝ) ≤ L := by exact_mod_cast hL
    have : (1:ℝ) / ((L+1:ℕ):ℝ)^2 ≤ 1/(L:ℝ) - 1/((L+1:ℕ):ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

def cop (L : ℕ) : Finset (ℕ × ℕ) := (Ioc 0 L ×ˢ Ioc 0 L).filter (fun z => Nat.Coprime z.1 z.2)

lemma cop_card (L : ℕ) : (L:ℝ)^2 ≤ 4 * (cop L).card := by
  classical
  set bad := (Icc 2 L).biUnion (fun d => (Ioc 0 L).filter (d ∣ ·) ×ˢ (Ioc 0 L).filter (d ∣ ·))
  have hsub : (Ioc 0 L ×ˢ Ioc 0 L).filter (fun z => ¬ Nat.Coprime z.1 z.2) ⊆ bad := by
    intro z hz
    simp only [mem_filter, mem_product, mem_Ioc] at hz
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hc⟩ := hz
    simp only [bad, mem_biUnion, mem_Icc, mem_product, mem_filter, mem_Ioc]
    refine ⟨Nat.gcd z.1 z.2, ⟨?_, ?_⟩, ⟨⟨h1, h2⟩, Nat.gcd_dvd_left _ _⟩, ⟨h3, h4⟩, Nat.gcd_dvd_right _ _⟩
    · have : Nat.gcd z.1 z.2 ≠ 1 := hc
      have : 0 < Nat.gcd z.1 z.2 := Nat.gcd_pos_of_pos_left _ h1
      omega
    · exact (Nat.gcd_le_left _ h1).trans h2
  have htot := card_filter_add_card_filter_not (s := Ioc 0 L ×ˢ Ioc 0 L)
    (fun z : ℕ × ℕ => Nat.Coprime z.1 z.2)
  rw [card_product, Nat.card_Ioc, Nat.sub_zero] at htot
  have hbad : (bad.card : ℝ) ≤ ∑ d ∈ Icc 2 L, ((L:ℝ) / d)^2 := by
    have := card_biUnion_le (s := Icc 2 L)
      (t := fun d => (Ioc 0 L).filter (d ∣ ·) ×ˢ (Ioc 0 L).filter (d ∣ ·))
    have h2 : (bad.card : ℝ) ≤ ∑ d ∈ Icc 2 L, (((L / d : ℕ)) : ℝ)^2 := by
      have : bad.card ≤ ∑ d ∈ Icc 2 L, (L / d)^2 := by
        refine this.trans (le_of_eq (sum_congr rfl fun d _ => ?_))
        rw [card_product, Nat.Ioc_filter_dvd_card_eq_div, sq]
      exact_mod_cast this
    refine h2.trans (sum_le_sum fun d hd => ?_)
    have hd0 : (0:ℝ) < d := by simp at hd; exact_mod_cast (by omega : 0 < d)
    gcongr
    exact Nat.cast_div_le
  have hsum : ∑ d ∈ Icc 2 L, ((L:ℝ) / d)^2 ≤ 3/4 * (L:ℝ)^2 := by
    rcases Nat.lt_or_ge L 2 with hL | hL
    · rw [Finset.Icc_eq_empty (by omega)]; simp
    have := sum_inv_sq L hL
    have h : ∑ d ∈ Icc 2 L, ((L:ℝ) / d)^2 = (L:ℝ)^2 * ∑ d ∈ Icc 2 L, (1:ℝ) / (d:ℝ)^2 := by
      rw [mul_sum]; refine sum_congr rfl fun d _ => by ring
    rw [h]
    have : (0:ℝ) ≤ 1/(L:ℝ) := by positivity
    nlinarith [sq_nonneg (L:ℝ)]
  have hb2 := card_le_card hsub
  have : ((L * L : ℕ) : ℝ) = (cop L).card + ((Ioc 0 L ×ˢ Ioc 0 L).filter (fun z => ¬ Nat.Coprime z.1 z.2)).card := by
    rw [← htot]; push_cast; rfl
  push_cast at this
  have hb3 : (((Ioc 0 L ×ˢ Ioc 0 L).filter (fun z => ¬ Nat.Coprime z.1 z.2)).card : ℝ) ≤ bad.card := by
    exact_mod_cast hb2
  nlinarith


def cr (u v : ℤ × ℤ) : ℤ := u.1 * v.2 - u.2 * v.1

lemma core (K t : ℕ) (_ht : 1 ≤ t) (htK : t.factorial < K) :
    ∃ A : Finset ((ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ)),
      (∀ a ∈ A, a.1 ∈ Icc (0:ℤ) (3*K) ×ˢ Icc (0:ℤ) (3*K) ∧ a.2.1 ∈ Icc (0:ℤ) (3*K) ×ˢ Icc (0:ℤ) (3*K) ∧
        a.2.2 ∈ Icc (0:ℤ) (3*K) ×ˢ Icc (0:ℤ) (3*K) ∧
        cr (a.2.1.1 - a.1.1, a.2.1.2 - a.1.2) (a.2.2.1 - a.1.1, a.2.2.2 - a.1.2) = t.factorial) ∧
      (K:ℝ)^4 / 16 * (harmonic t : ℝ) ≤ A.card := by
  classical
  choose d0 b0 hdb using (fun x γ e => bez x γ e)
  set D := t.factorial with hD
  let f : ℕ → (ℤ × ℤ) × (ℕ × ℕ) × ℕ → (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ) := fun h w =>
    (w.1, (w.1.1 + h * w.2.1.1, w.1.2 + h * w.2.1.2),
      (w.1.1 + b0 w.2.1.1 w.2.1.2 (D / h) + w.2.2 * w.2.1.1,
       w.1.2 + d0 w.2.1.1 w.2.1.2 (D / h) + w.2.2 * w.2.1.2))
  let box : Finset (ℤ × ℤ) := Icc (K:ℤ) (2*K) ×ˢ Icc (K:ℤ) (2*K)
  let dom : ℕ → Finset ((ℤ × ℤ) × (ℕ × ℕ) × ℕ) := fun h => box ×ˢ cop (K / h) ×ˢ range h
  refine ⟨(Icc 1 t).biUnion (fun h => (dom h).image (f h)), ?_, ?_⟩
  · intro a ha
    simp only [mem_biUnion, mem_image, mem_Icc] at ha
    obtain ⟨h, ⟨h1, ht'⟩, w, hw, rfl⟩ := ha
    obtain ⟨⟨p1, p2⟩, ⟨x, γ⟩, s⟩ := w
    simp only [dom, box, cop, mem_product, mem_Icc, mem_filter, mem_Ioc, mem_range] at hw
    obtain ⟨⟨⟨hp1, hp1'⟩, hp2, hp2'⟩, ⟨⟨⟨hx, hxL⟩, hγ, hγL⟩, hc⟩, hs⟩ := hw
    obtain ⟨hd0, hd0', hkey, hb0, hb0'⟩ := hdb x γ (D / h) hx hγ hc
    have hhD : h ∣ D := Nat.dvd_factorial (by omega) ht'
    have heD : D / h ≤ D := Nat.div_le_self _ _
    have hDK : (D:ℤ) < K := by exact_mod_cast htK
    have heK : ((D / h : ℕ) : ℤ) < K := by
      have : ((D / h : ℕ) : ℤ) ≤ D := by exact_mod_cast heD
      omega
    have hLh : h * (K / h) ≤ K := Nat.mul_div_le K h
    have hLhz : (h:ℤ) * ((K / h : ℕ) : ℤ) ≤ K := by exact_mod_cast hLh
    have hxz : (x:ℤ) ≤ ((K / h : ℕ) : ℤ) := by exact_mod_cast hxL
    have hγz : (γ:ℤ) ≤ ((K / h : ℕ) : ℤ) := by exact_mod_cast hγL
    have hx1 : (1:ℤ) ≤ x := by exact_mod_cast hx
    have hγ1 : (1:ℤ) ≤ γ := by exact_mod_cast hγ
    have hs1 : (s:ℤ) + 1 ≤ h := by exact_mod_cast hs
    have hs0 : (0:ℤ) ≤ s := by positivity
    have hhx : (h:ℤ) * x ≤ K := le_trans (mul_le_mul_of_nonneg_left hxz (by positivity)) hLhz
    have hhγ : (h:ℤ) * γ ≤ K := le_trans (mul_le_mul_of_nonneg_left hγz (by positivity)) hLhz
    have hsx : (s:ℤ) * x + x ≤ K := by nlinarith
    have hsγ : (s:ℤ) * γ + γ ≤ K := by nlinarith
    have hsx0 : (0:ℤ) ≤ s * x := by positivity
    have hsγ0 : (0:ℤ) ≤ s * γ := by positivity
    have hh0 : (0:ℤ) ≤ h := by positivity
    have hhx0 : (0:ℤ) ≤ h * x := by positivity
    have hhγ0 : (0:ℤ) ≤ h * γ := by positivity
    have hK0 : (0:ℤ) ≤ K := by positivity
    simp only [f, mem_product, mem_Icc]
    refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩,
      ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩,
      ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ?_⟩
    simp only [cr]
    have : ((h:ℕ):ℤ) * ((D / h : ℕ) : ℤ) = D := by exact_mod_cast Nat.mul_div_cancel' hhD
    linear_combination (h:ℤ) * hkey + this
  · rw [card_biUnion]
    · have hcard : ∀ h ∈ Icc 1 t, ((dom h).image (f h)).card = (K+1)^2 * ((cop (K / h)).card * h) := by
        intro h hh
        rw [card_image_of_injOn]
        · simp only [dom, box, card_product, Int.card_Icc, card_range]
          have : (2 * (K:ℤ) + 1 - K).toNat = K + 1 := by omega
          rw [this]; ring
        · rintro ⟨⟨p1, p2⟩, ⟨x, γ⟩, s⟩ hw ⟨⟨p1', p2'⟩, ⟨x', γ'⟩, s'⟩ hw' heq
          simp only [dom, box, cop, coe_product, Set.mem_prod, mem_coe, mem_product, mem_Icc,
            mem_filter, mem_Ioc, mem_range] at hw hw'
          simp only [f, Prod.mk.injEq] at heq
          obtain ⟨⟨rfl, rfl⟩, ⟨h1, h2⟩, h3, h4⟩ := heq
          have hh0 : (h:ℤ) ≠ 0 := by simp at hh; exact_mod_cast (by omega : h ≠ 0)
          have hx : (x:ℤ) = x' := by
            have := mul_left_cancel₀ hh0 (by linarith : (h:ℤ) * x = h * x'); exact this
          have hγ : (γ:ℤ) = γ' := by
            have := mul_left_cancel₀ hh0 (by linarith : (h:ℤ) * γ = h * γ'); exact this
          have hx' : x = x' := by exact_mod_cast hx
          have hγ' : γ = γ' := by exact_mod_cast hγ
          subst hx' hγ'
          have hγ0 : (γ:ℤ) ≠ 0 := by exact_mod_cast (by omega : γ ≠ 0)
          have : (s:ℤ) * γ = s' * γ := by linarith
          have hs : (s:ℤ) = s' := mul_right_cancel₀ hγ0 this
          have : s = s' := by exact_mod_cast hs
          subst this; rfl
      rw [sum_congr rfl hcard]
      push_cast
      rw [harmonic_eq_sum_Icc]
      push_cast
      rw [mul_sum]
      refine sum_le_sum fun h hh => ?_
      simp only [mem_Icc] at hh
      have hhK : h ≤ K := by
        have := Nat.self_le_factorial t; omega
      have hq : K ≤ 2 * (K / h) * h := by
        have h1 := Nat.div_add_mod K h
        have h2 := Nat.mod_lt K (by omega : h > 0)
        have h3 : 1 ≤ K / h := (Nat.one_le_div_iff (by omega)).mpr hhK
        nlinarith
      have hqr : (K:ℝ) ≤ 2 * ((K / h : ℕ) : ℝ) * h := by exact_mod_cast hq
      have hc := cop_card (K / h)
      have hh1 : (1:ℝ) ≤ h := by exact_mod_cast hh.1
      have hK0 : (0:ℝ) ≤ K := by positivity
      have hq0 : (0:ℝ) ≤ ((K / h : ℕ) : ℝ) := by positivity
      -- goal: K^4/16 * h⁻¹ ≤ (K+1)^2 * (cop * h)
      have e1 : (K:ℝ)^2 ≤ 4 * ((K / h : ℕ) : ℝ)^2 * (h:ℝ)^2 := by nlinarith
      have e2 : (K:ℝ)^2 ≤ 16 * (cop (K / h)).card * (h:ℝ)^2 := by nlinarith
      have e3 : (K:ℝ)^2 ≤ ((K:ℝ)+1)^2 := by nlinarith
      rw [show (K:ℝ)^4 / 16 * (h:ℝ)⁻¹ = (K:ℝ)^2 * (K:ℝ)^2 / (16 * h) by field_simp]
      rw [div_le_iff₀ (by positivity)]
      have : (K:ℝ)^2 * (K:ℝ)^2 ≤ ((K:ℝ)+1)^2 * (16 * (cop (K / h)).card * (h:ℝ)^2) :=
        mul_le_mul e3 e2 (by positivity) (by positivity)
      nlinarith
    · intro h hh h' hh' hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro a ha ha'
      simp only [mem_image] at ha ha'
      obtain ⟨⟨⟨p1, p2⟩, ⟨x, γ⟩, s⟩, hw, rfl⟩ := ha
      obtain ⟨⟨⟨p1', p2'⟩, ⟨x', γ'⟩, s'⟩, hw', heq⟩ := ha'
      simp only [dom, box, cop, mem_product, mem_Icc, mem_filter, mem_Ioc, mem_range] at hw hw'
      simp only [f, Prod.mk.injEq] at heq
      obtain ⟨⟨rfl, rfl⟩, ⟨h1, h2⟩, -⟩ := heq
      have e1 : h' * x' = h * x := by
        have : (h':ℤ) * x' = h * x := by linarith
        exact_mod_cast this
      have e2 : h' * γ' = h * γ := by
        have : (h':ℤ) * γ' = h * γ := by linarith
        exact_mod_cast this
      have : Nat.gcd (h * x) (h * γ) = Nat.gcd (h' * x') (h' * γ') := by rw [e1, e2]
      rw [Nat.gcd_mul_left, Nat.gcd_mul_left, hw.2.1.2, hw'.2.1.2] at this
      exact hne (by simpa using this)
  

open scoped EuclideanGeometry

noncomputable def emb (z : ℤ × ℤ) : ℝ² := !₂[(z.1:ℝ), (z.2:ℝ)]

lemma emb_inj : Function.Injective emb := by
  intro z w h
  have h0 := congrArg (fun v : ℝ² => v 0) h
  have h1 := congrArg (fun v : ℝ² => v 1) h
  simp [emb] at h0 h1
  exact Prod.ext h0 h1

lemma area_emb (p q r : ℤ × ℤ) :
    EuclideanGeometry.triangle_area (emb p) (emb q) (emb r) =
      (cr (q.1 - p.1, q.2 - p.2) (r.1 - p.1, r.2 - p.2) : ℝ) / 2 := by
  rw [EuclideanGeometry.triangle_area_eq_det]
  simp [emb, Matrix.det_fin_three, cr]
  ring

lemma g_ge (n : ℕ) (P : Finset ℝ²) (hP : P.card = n) (a : ℝ) (ha : 0 < a) :
    Erdos1086.triangleAreaCount P a ≤ Erdos1086.g n := by
  refine le_csSup ⟨n.choose 3, ?_⟩ ⟨P, a, hP, ha, rfl⟩
  rintro m ⟨Q, b, hQ, -, rfl⟩
  classical
  unfold Erdos1086.triangleAreaCount
  rw [← hQ]
  exact (Finset.card_filter_le _ _).trans (Finset.card_powersetCard 3 Q).le

lemma g_bound (K t n : ℕ) (ht : 1 ≤ t) (htK : t.factorial < K) (hn : (3*K+1)^2 ≤ n) :
    (K:ℝ)^4 / 16 * (harmonic t : ℝ) ≤ 27 * Erdos1086.g n := by
  classical
  obtain ⟨A, hA, hcard⟩ := core K t ht htK
  set G : Finset (ℤ × ℤ) := Icc (0:ℤ) (3*K) ×ˢ Icc (0:ℤ) (3*K)
  have hG : (G.image emb).card = (3*K+1)^2 := by
    rw [card_image_of_injective _ emb_inj]
    simp only [G, card_product, Int.card_Icc]
    have : (3 * (K:ℤ) + 1 - 0).toNat = 3 * K + 1 := by omega
    rw [this]; ring
  obtain ⟨P, hPsub, hPcard⟩ := Infinite.exists_superset_card_eq (G.image emb) n (by rw [hG]; exact hn)
  set a : ℝ := (t.factorial : ℝ) / 2
  have ha : 0 < a := by positivity
  let φ : (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ) → Finset ℝ² := fun x => {emb x.1, emb x.2.1, emb x.2.2}
  have hD0 : (t.factorial : ℤ) ≠ 0 := by positivity
  have hdist : ∀ x ∈ A, x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ x.2.1 ≠ x.2.2 := by
    intro x hx
    obtain ⟨-, -, -, hc⟩ := hA x hx
    refine ⟨fun h => hD0 ?_, fun h => hD0 ?_, fun h => hD0 ?_⟩
    · rw [← hc, h]; simp [cr]
    · rw [← hc, h]; simp [cr]
    · rw [← hc, h]; simp [cr]; ring
  have himg : A.image φ ⊆ (P.powersetCard 3).filter fun T =>
      ∃ p q r : ℝ², T = {p, q, r} ∧ |EuclideanGeometry.triangle_area p q r| = a := by
    intro T hT
    simp only [mem_image] at hT
    obtain ⟨x, hx, rfl⟩ := hT
    obtain ⟨h1, h2, h3, hc⟩ := hA x hx
    obtain ⟨d1, d2, d3⟩ := hdist x hx
    rw [mem_filter, mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, emb x.1, emb x.2.1, emb x.2.2, rfl, ?_⟩
    · intro y hy
      simp only [φ, mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> exact hPsub (mem_image_of_mem _ (by assumption))
    · rw [card_eq_three]
      exact ⟨_, _, _, fun h => d1 (emb_inj h), fun h => d2 (emb_inj h), fun h => d3 (emb_inj h), rfl⟩
    · rw [area_emb, hc]; simp only [a]; push_cast
      rw [abs_of_nonneg (by positivity)]
  have hfib : A.card ≤ 27 * (A.image φ).card := by
    refine card_le_mul_card_image _ 27 fun T hT => ?_
    have hT3 : T.card ≤ 3 := by
      simp only [mem_image] at hT
      obtain ⟨x, -, rfl⟩ := hT
      exact card_le_three
    calc (A.filter fun x => φ x = T).card ≤ (T ×ˢ T ×ˢ T).card := by
          refine card_le_card_of_injOn (fun x => (emb x.1, emb x.2.1, emb x.2.2)) ?_ ?_
          · intro x hx
            simp only [coe_filter, Set.mem_ofPred_eq] at hx
            obtain ⟨-, rfl⟩ := hx
            simp [φ, mem_product]
          · intro x _ y _ h
            simp only [Prod.mk.injEq] at h
            obtain ⟨h1, h2, h3⟩ := h
            exact Prod.ext (emb_inj h1) (Prod.ext (emb_inj h2) (emb_inj h3))
      _ = T.card ^ 3 := by simp [card_product]; ring
      _ ≤ 3 ^ 3 := Nat.pow_le_pow_left hT3 3
      _ = 27 := by norm_num
  have hcnt : (A.image φ).card ≤ Erdos1086.triangleAreaCount P a := by
    unfold Erdos1086.triangleAreaCount
    convert card_le_card himg
  have := g_ge n P hPcard a ha
  have h27 : (A.card : ℝ) ≤ 27 * Erdos1086.g n := by
    have : A.card ≤ 27 * Erdos1086.g n := hfib.trans (Nat.mul_le_mul_left _ (hcnt.trans this))
    exact_mod_cast this
  linarith


lemma loglog_le (n t K : ℕ) (hn : 64 ≤ n) (hnK : n ≤ 25 * K^2) (hK : K ≤ (t+1).factorial) (ht : 1 ≤ t) :
    Real.log (Real.log n) ≤ 5 * (harmonic t : ℝ) := by
  set s := t + 1 with hs
  have hs2 : 2 ≤ s := by omega
  have hKs : K ≤ s ^ s := hK.trans (Nat.factorial_le_pow s)
  have hn7 : n ≤ s ^ (7 * s) := by
    have h1 : 25 ≤ s ^ (5 * s) := by
      calc 25 ≤ 2 ^ 5 := by norm_num
        _ ≤ s ^ 5 := Nat.pow_le_pow_left hs2 5
        _ ≤ s ^ (5 * s) := Nat.pow_le_pow_right (by omega) (by omega)
    calc n ≤ 25 * K^2 := hnK
      _ ≤ s ^ (5 * s) * (s ^ s)^2 := Nat.mul_le_mul h1 (Nat.pow_le_pow_left hKs 2)
      _ = s ^ (7 * s) := by rw [← pow_mul, ← pow_add]; ring_nf
  have hsR : (2:ℝ) ≤ s := by exact_mod_cast hs2
  have hn1 : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlogn : Real.log n ≤ 7 * s * Real.log s := by
    have : (n:ℝ) ≤ (s:ℝ) ^ (7 * s) := by exact_mod_cast hn7
    have := Real.log_le_log (by positivity) this
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hls : Real.log s ≤ s := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hls0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hlogn2 : Real.log n ≤ (s:ℝ) ^ 5 := by
    have : 7 * (s:ℝ) * Real.log s ≤ 7 * s * s := by gcongr
    have h8 : (8:ℝ) ≤ (s:ℝ)^3 := by
      have := pow_le_pow_left₀ (by norm_num) hsR 3; norm_num at this; linarith
    nlinarith
  have hpos : 0 < Real.log n := Real.log_pos hn1
  have : Real.log (Real.log n) ≤ 5 * Real.log s := by
    have := Real.log_le_log hpos hlogn2
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hh := log_add_one_le_harmonic t
  push_cast at hh
  rw [hs] at this; push_cast at this
  linarith

theorem main : (fun n : ℕ ↦ (n : ℝ) ^ 2 * Real.log (Real.log n)) =O[atTop]
    fun n : ℕ ↦ (Erdos1086.g n : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 1350000 ?_
  filter_upwards [eventually_ge_atTop 64] with n hn
  set M := Nat.sqrt n
  have hM1 : M * M ≤ n := Nat.sqrt_le n
  have hM2 : n < (M + 1) * (M + 1) := Nat.lt_succ_sqrt n
  have hM8 : 8 ≤ M := Nat.le_sqrt'.mpr (by omega)
  set K := (M - 1) / 3
  have hK2 : 2 ≤ K := by omega
  have hK3 : 3 * K + 1 ≤ M := by omega
  have hK4 : M ≤ 3 * K + 3 := by omega
  have hgrid : (3 * K + 1)^2 ≤ n := by nlinarith
  have hnK : n ≤ 25 * K^2 := by nlinarith
  set t := Nat.findGreatest (fun s => s.factorial < K) K
  have ht1 : 1 ≤ t := Nat.le_findGreatest (by omega) (by simp; omega)
  have htK : t.factorial < K := Nat.findGreatest_spec (P := fun s => s.factorial < K) (m := 1)
    (by omega) (by simp; omega)
  have hKt : K ≤ (t+1).factorial := by
    by_contra hc
    push Not at hc
    by_cases h : t + 1 ≤ K
    · exact Nat.findGreatest_is_greatest (P := fun s => s.factorial < K) (by omega) h hc
    · have : t ≤ K := Nat.findGreatest_le K
      have : t = K := by omega
      rw [this] at htK
      exact absurd (Nat.self_le_factorial K) (by omega)
  have hb := g_bound K t n ht1 htK hgrid
  have hll := loglog_le n t K hn hnK hKt ht1
  have hn1 : (1:ℝ) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (64:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hll0 : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hn1
  have hH0 : (0:ℝ) ≤ (harmonic t : ℝ) := by
    have := log_add_one_le_harmonic t
    have : 0 ≤ Real.log ((t + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t + 1))
    linarith
  have hnK' : (n:ℝ)^2 ≤ 625 * (K:ℝ)^4 := by
    have : (n:ℝ) ≤ 25 * (K:ℝ)^2 := by exact_mod_cast hnK
    nlinarith [sq_nonneg (n:ℝ)]
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hll0), Real.norm_of_nonneg (by positivity)]
  calc (n:ℝ)^2 * Real.log (Real.log n) ≤ (625 * (K:ℝ)^4) * (5 * (harmonic t : ℝ)) :=
        mul_le_mul hnK' hll hll0 (by positivity)
    _ ≤ 1350000 * (Erdos1086.g n : ℝ) := by nlinarith

end OMAx

theorem OMA.solution : type_of% @Erdos1086.erdos_1086.variants.erdos_purdy_lower := OMAx.main
