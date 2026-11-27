import OMAReductions.R_Erdos888_erdos_888_variants_semiprimes_R1
import Mathlib.Data.Nat.Factorization.Basic

namespace OMA.SemiprimeSquare

lemma ordered (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (he : a*b=c*d ∨ a*c=b*d ∨ a*d=b*c) : a*d=b*c := by
  rcases he with he | he | he
  · have hac : a=c := by
      by_contra hne
      have hlt : a < c := by omega
      have h1 := Nat.mul_lt_mul_of_pos_right hlt hb
      have h2 := Nat.mul_le_mul_left c (le_trans hbc hcd)
      nlinarith only [he,h1,h2]
    have hab' : a=b := by omega
    subst c
    subst b
    have had : a=d := Nat.eq_of_mul_eq_mul_left ha he
    subst d
    rfl
  · have hab' : a=b := by
      by_contra hne
      have hlt : a < b := by omega
      have h1 := Nat.mul_lt_mul_of_pos_right hlt hc
      have h2 := Nat.mul_le_mul_left b hcd
      nlinarith only [he,h1,h2]
    subst b
    have hcd' : c=d := Nat.eq_of_mul_eq_mul_left ha he
    subst d
    rfl
  · exact he

lemma parity (p q r s t u v w : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hs : s.Prime) (ht : t.Prime) (hu : u.Prime)
    (hv : v.Prime) (hw : w.Prime) (h : IsSquare (p*q*(r*s)*(t*u)*(v*w))) :
    ∀ z : ℕ, Even ((if p=z then 1 else 0)+(if q=z then 1 else 0)+
      (if r=z then 1 else 0)+(if s=z then 1 else 0)+(if t=z then 1 else 0)+
      (if u=z then 1 else 0)+(if v=z then 1 else 0)+(if w=z then 1 else 0)) := by
  have hp0 := hp.pos
  have hq0 := hq.pos
  have hr0 := hr.pos
  have hs0 := hs.pos
  have ht0 := ht.pos
  have hu0 := hu.pos
  have hv0 := hv.pos
  have hw0 := hw.pos
  intro z
  have hf : (p*q*(r*s)*(t*u)*(v*w)).factorization z =
      (if p=z then 1 else 0)+(if q=z then 1 else 0)+(if r=z then 1 else 0)+
      (if s=z then 1 else 0)+(if t=z then 1 else 0)+(if u=z then 1 else 0)+
      (if v=z then 1 else 0)+(if w=z then 1 else 0) := by
    repeat rw [Nat.factorization_mul (by positivity) (by positivity)]
    simp only [hp.factorization, hq.factorization, hr.factorization, hs.factorization,
      ht.factorization, hu.factorization, hv.factorization, hw.factorization,
      Finsupp.add_apply, Finsupp.single_apply]
    omega
  rw [← hf]
  obtain ⟨a,ha⟩ := h
  rw [ha, ← pow_two, Nat.factorization_pow]
  change Even (2*a.factorization z)
  exact even_two_mul _

-- Finite equality classification of eight prime occurrences.
-- Cyclic strict-order branches close by arithmetic; odd multiplicities contradict parity.
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 5000 in
lemma pairing (p q r s t u v w : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hs : s.Prime) (ht : t.Prime) (hu : u.Prime)
    (hv : v.Prime) (hw : w.Prime)
    (hpq : p<q) (hrs : r<s) (htu : t<u) (hvw : v<w)
    (hsq : IsSquare (p*q*(r*s)*(t*u)*(v*w))) :
    p*q*(r*s)=t*u*(v*w) ∨ p*q*(t*u)=r*s*(v*w) ∨ p*q*(v*w)=r*s*(t*u) := by
  have hpar := parity p q r s t u v w hp hq hr hs ht hu hv hw hsq
  clear hp hq hr hs ht hu hv hw hsq
  have h10 : q ≠ p := by omega
  have h10r := Ne.symm h10
  by_cases h20 : r = p
  · subst r
    have h30 : s ≠ p := by omega
    have h30r := Ne.symm h30
    by_cases h31 : s = q
    · subst s
      by_cases h40 : t = p
      · subst t
        have h50 : u ≠ p := by omega
        have h50r := Ne.symm h50
        by_cases h51 : u = q
        · subst u
          by_cases h60 : v = p
          · subst v
            have h70 : w ≠ p := by omega
            have h70r := Ne.symm h70
            by_cases h71 : w = q
            · subst w
              exact Or.inl (by ring)
            · have h71r := Ne.symm h71
              have hh := hpar q
              clear hpar
              norm_num [*] at hh
          · have h60r := Ne.symm h60
            by_cases h61 : v = q
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              have h71 : w ≠ q := by omega
              have h71r := Ne.symm h71
              have hh := hpar p
              clear hpar
              norm_num [*] at hh
            · have h61r := Ne.symm h61
              by_cases h70 : w = p
              · subst w
                have hh := hpar q
                clear hpar
                norm_num [*] at hh
              · have h70r := Ne.symm h70
                by_cases h71 : w = q
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h71r := Ne.symm h71
                  have h76 : w ≠ v := by omega
                  have h76r := Ne.symm h76
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
        · have h51r := Ne.symm h51
          by_cases h60 : v = p
          · subst v
            have h70 : w ≠ p := by omega
            have h70r := Ne.symm h70
            by_cases h71 : w = q
            · subst w
              have hh := hpar q
              clear hpar
              norm_num [*] at hh
            · have h71r := Ne.symm h71
              by_cases h75 : w = u
              · subst w
                exact Or.inr (Or.inl (by ring))
              · have h75r := Ne.symm h75
                have hh := hpar u
                clear hpar
                norm_num [*] at hh
          · have h60r := Ne.symm h60
            by_cases h61 : v = q
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              have h71 : w ≠ q := by omega
              have h71r := Ne.symm h71
              by_cases h75 : w = u
              · subst w
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
              · have h75r := Ne.symm h75
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
            · have h61r := Ne.symm h61
              by_cases h65 : v = u
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                by_cases h71 : w = q
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h71r := Ne.symm h71
                  have h75 : w ≠ u := by omega
                  have h75r := Ne.symm h75
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
              · have h65r := Ne.symm h65
                by_cases h70 : w = p
                · subst w
                  have hh := hpar u
                  clear hpar
                  norm_num [*] at hh
                · have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h71r := Ne.symm h71
                    by_cases h75 : w = u
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h75r := Ne.symm h75
                      have h76 : w ≠ v := by omega
                      have h76r := Ne.symm h76
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
      · have h40r := Ne.symm h40
        by_cases h41 : t = q
        · subst t
          have h50 : u ≠ p := by omega
          have h50r := Ne.symm h50
          have h51 : u ≠ q := by omega
          have h51r := Ne.symm h51
          by_cases h60 : v = p
          · subst v
            have h70 : w ≠ p := by omega
            have h70r := Ne.symm h70
            by_cases h71 : w = q
            · subst w
              have hh := hpar p
              clear hpar
              norm_num [*] at hh
            · have h71r := Ne.symm h71
              by_cases h75 : w = u
              · subst w
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
              · have h75r := Ne.symm h75
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
          · have h60r := Ne.symm h60
            by_cases h61 : v = q
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              have h71 : w ≠ q := by omega
              have h71r := Ne.symm h71
              by_cases h75 : w = u
              · subst w
                exact Or.inr (Or.inl (by ring))
              · have h75r := Ne.symm h75
                have hh := hpar u
                clear hpar
                norm_num [*] at hh
            · have h61r := Ne.symm h61
              by_cases h65 : v = u
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                have h75 : w ≠ u := by omega
                have h75r := Ne.symm h75
                have hh := hpar q
                clear hpar
                norm_num [*] at hh
              · have h65r := Ne.symm h65
                by_cases h70 : w = p
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    have hh := hpar u
                    clear hpar
                    norm_num [*] at hh
                  · have h71r := Ne.symm h71
                    by_cases h75 : w = u
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h75r := Ne.symm h75
                      have h76 : w ≠ v := by omega
                      have h76r := Ne.symm h76
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
        · have h41r := Ne.symm h41
          by_cases h50 : u = p
          · subst u
            by_cases h60 : v = p
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              by_cases h71 : w = q
              · subst w
                have hh := hpar q
                clear hpar
                norm_num [*] at hh
              · have h71r := Ne.symm h71
                have h74 : w ≠ t := by omega
                have h74r := Ne.symm h74
                have hh := hpar t
                clear hpar
                norm_num [*] at hh
            · have h60r := Ne.symm h60
              by_cases h61 : v = q
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                have h74 : w ≠ t := by omega
                have h74r := Ne.symm h74
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
              · have h61r := Ne.symm h61
                by_cases h64 : v = t
                · subst v
                  by_cases h70 : w = p
                  · subst w
                    exact Or.inr (Or.inl (by ring))
                  · have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      have h74 : w ≠ t := by omega
                      have h74r := Ne.symm h74
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                · have h64r := Ne.symm h64
                  by_cases h70 : w = p
                  · subst w
                    have hh := hpar t
                    clear hpar
                    norm_num [*] at hh
                  · have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h74 : w = t
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h74r := Ne.symm h74
                        have h76 : w ≠ v := by omega
                        have h76r := Ne.symm h76
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
          · have h50r := Ne.symm h50
            by_cases h51 : u = q
            · subst u
              by_cases h60 : v = p
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                by_cases h71 : w = q
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h71r := Ne.symm h71
                  by_cases h74 : w = t
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h74r := Ne.symm h74
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
              · have h60r := Ne.symm h60
                by_cases h61 : v = q
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  have h74 : w ≠ t := by omega
                  have h74r := Ne.symm h74
                  have hh := hpar t
                  clear hpar
                  norm_num [*] at hh
                · have h61r := Ne.symm h61
                  by_cases h64 : v = t
                  · subst v
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        exact Or.inr (Or.inl (by ring))
                      · have h71r := Ne.symm h71
                        have h74 : w ≠ t := by omega
                        have h74r := Ne.symm h74
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                  · have h64r := Ne.symm h64
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar t
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        by_cases h74 : w = t
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h74r := Ne.symm h74
                          have h76 : w ≠ v := by omega
                          have h76r := Ne.symm h76
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
            · have h51r := Ne.symm h51
              have h54 : u ≠ t := by omega
              have h54r := Ne.symm h54
              by_cases h60 : v = p
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                by_cases h71 : w = q
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h71r := Ne.symm h71
                  by_cases h74 : w = t
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h74r := Ne.symm h74
                    by_cases h75 : w = u
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h75r := Ne.symm h75
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
              · have h60r := Ne.symm h60
                by_cases h61 : v = q
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  by_cases h74 : w = t
                  · subst w
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h74r := Ne.symm h74
                    by_cases h75 : w = u
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h75r := Ne.symm h75
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                · have h61r := Ne.symm h61
                  by_cases h64 : v = t
                  · subst v
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        have h74 : w ≠ t := by omega
                        have h74r := Ne.symm h74
                        by_cases h75 : w = u
                        · subst w
                          exact Or.inr (Or.inl (by ring))
                        · have h75r := Ne.symm h75
                          have hh := hpar u
                          clear hpar
                          norm_num [*] at hh
                  · have h64r := Ne.symm h64
                    by_cases h65 : v = u
                    · subst v
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          have h74 : w ≠ t := by omega
                          have h74r := Ne.symm h74
                          have h75 : w ≠ u := by omega
                          have h75r := Ne.symm h75
                          have hh := hpar t
                          clear hpar
                          norm_num [*] at hh
                    · have h65r := Ne.symm h65
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h74 : w = t
                          · subst w
                            have hh := hpar u
                            clear hpar
                            norm_num [*] at hh
                          · have h74r := Ne.symm h74
                            by_cases h75 : w = u
                            · subst w
                              have hh := hpar t
                              clear hpar
                              norm_num [*] at hh
                            · have h75r := Ne.symm h75
                              have h76 : w ≠ v := by omega
                              have h76r := Ne.symm h76
                              have hh := hpar t
                              clear hpar
                              norm_num [*] at hh
    · have h31r := Ne.symm h31
      by_cases h40 : t = p
      · subst t
        have h50 : u ≠ p := by omega
        have h50r := Ne.symm h50
        by_cases h51 : u = q
        · subst u
          by_cases h60 : v = p
          · subst v
            have h70 : w ≠ p := by omega
            have h70r := Ne.symm h70
            by_cases h71 : w = q
            · subst w
              have hh := hpar q
              clear hpar
              norm_num [*] at hh
            · have h71r := Ne.symm h71
              by_cases h73 : w = s
              · subst w
                exact Or.inl (by ring)
              · have h73r := Ne.symm h73
                have hh := hpar s
                clear hpar
                norm_num [*] at hh
          · have h60r := Ne.symm h60
            by_cases h61 : v = q
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              have h71 : w ≠ q := by omega
              have h71r := Ne.symm h71
              by_cases h73 : w = s
              · subst w
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
              · have h73r := Ne.symm h73
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
            · have h61r := Ne.symm h61
              by_cases h63 : v = s
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                by_cases h71 : w = q
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h71r := Ne.symm h71
                  have h73 : w ≠ s := by omega
                  have h73r := Ne.symm h73
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
              · have h63r := Ne.symm h63
                by_cases h70 : w = p
                · subst w
                  have hh := hpar s
                  clear hpar
                  norm_num [*] at hh
                · have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h71r := Ne.symm h71
                    by_cases h73 : w = s
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h73r := Ne.symm h73
                      have h76 : w ≠ v := by omega
                      have h76r := Ne.symm h76
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
        · have h51r := Ne.symm h51
          by_cases h53 : u = s
          · subst u
            by_cases h60 : v = p
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              by_cases h71 : w = q
              · subst w
                exact Or.inl (by ring)
              · have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
            · have h60r := Ne.symm h60
              by_cases h61 : v = q
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
              · have h61r := Ne.symm h61
                by_cases h63 : v = s
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h71r := Ne.symm h71
                    have h73 : w ≠ s := by omega
                    have h73r := Ne.symm h73
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                · have h63r := Ne.symm h63
                  by_cases h70 : w = p
                  · subst w
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        have h76 : w ≠ v := by omega
                        have h76r := Ne.symm h76
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
          · have h53r := Ne.symm h53
            by_cases h60 : v = p
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              by_cases h71 : w = q
              · subst w
                have hh := hpar s
                clear hpar
                norm_num [*] at hh
              · have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  by_cases h75 : w = u
                  · subst w
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h75r := Ne.symm h75
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
            · have h60r := Ne.symm h60
              by_cases h61 : v = q
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  by_cases h75 : w = u
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h75r := Ne.symm h75
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
              · have h61r := Ne.symm h61
                by_cases h63 : v = s
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h71r := Ne.symm h71
                    have h73 : w ≠ s := by omega
                    have h73r := Ne.symm h73
                    by_cases h75 : w = u
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h75r := Ne.symm h75
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                · have h63r := Ne.symm h63
                  by_cases h65 : v = u
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        have h75 : w ≠ u := by omega
                        have h75r := Ne.symm h75
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                  · have h65r := Ne.symm h65
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have h76 : w ≠ v := by omega
                            have h76r := Ne.symm h76
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
      · have h40r := Ne.symm h40
        by_cases h41 : t = q
        · subst t
          have h50 : u ≠ p := by omega
          have h50r := Ne.symm h50
          have h51 : u ≠ q := by omega
          have h51r := Ne.symm h51
          by_cases h53 : u = s
          · subst u
            by_cases h60 : v = p
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              by_cases h71 : w = q
              · subst w
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
              · have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
            · have h60r := Ne.symm h60
              by_cases h61 : v = q
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
              · have h61r := Ne.symm h61
                by_cases h63 : v = s
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  have h73 : w ≠ s := by omega
                  have h73r := Ne.symm h73
                  have hh := hpar s
                  clear hpar
                  norm_num [*] at hh
                · have h63r := Ne.symm h63
                  by_cases h70 : w = p
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar s
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        have h76 : w ≠ v := by omega
                        have h76r := Ne.symm h76
                        have hh := hpar v
                        clear hpar
                        norm_num [*] at hh
          · have h53r := Ne.symm h53
            by_cases h60 : v = p
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              by_cases h71 : w = q
              · subst w
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
              · have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  by_cases h75 : w = u
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h75r := Ne.symm h75
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
            · have h60r := Ne.symm h60
              by_cases h61 : v = q
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  by_cases h75 : w = u
                  · subst w
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h75r := Ne.symm h75
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
              · have h61r := Ne.symm h61
                by_cases h63 : v = s
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h71r := Ne.symm h71
                    have h73 : w ≠ s := by omega
                    have h73r := Ne.symm h73
                    by_cases h75 : w = u
                    · subst w
                      exact Or.inr (Or.inr (by ring))
                    · have h75r := Ne.symm h75
                      have hh := hpar u
                      clear hpar
                      norm_num [*] at hh
                · have h63r := Ne.symm h63
                  by_cases h65 : v = u
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    have h71 : w ≠ q := by omega
                    have h71r := Ne.symm h71
                    by_cases h73 : w = s
                    · subst w
                      exact Or.inr (Or.inr (by ring))
                    · have h73r := Ne.symm h73
                      have h75 : w ≠ u := by omega
                      have h75r := Ne.symm h75
                      have hh := hpar s
                      clear hpar
                      norm_num [*] at hh
                  · have h65r := Ne.symm h65
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar u
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have h76 : w ≠ v := by omega
                            have h76r := Ne.symm h76
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
        · have h41r := Ne.symm h41
          by_cases h43 : t = s
          · subst t
            have h50 : u ≠ p := by omega
            have h50r := Ne.symm h50
            by_cases h51 : u = q
            · subst u
              by_cases h60 : v = p
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                by_cases h71 : w = q
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h71r := Ne.symm h71
                  by_cases h73 : w = s
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h73r := Ne.symm h73
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
              · have h60r := Ne.symm h60
                by_cases h61 : v = q
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  have h73 : w ≠ s := by omega
                  have h73r := Ne.symm h73
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
                · have h61r := Ne.symm h61
                  by_cases h63 : v = s
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      have h73 : w ≠ s := by omega
                      have h73r := Ne.symm h73
                      have hh := hpar s
                      clear hpar
                      norm_num [*] at hh
                  · have h63r := Ne.symm h63
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar s
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          have h76 : w ≠ v := by omega
                          have h76r := Ne.symm h76
                          have hh := hpar v
                          clear hpar
                          norm_num [*] at hh
            · have h51r := Ne.symm h51
              have h53 : u ≠ s := by omega
              have h53r := Ne.symm h53
              by_cases h60 : v = p
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                by_cases h71 : w = q
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h71r := Ne.symm h71
                  by_cases h73 : w = s
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h73r := Ne.symm h73
                    by_cases h75 : w = u
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h75r := Ne.symm h75
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
              · have h60r := Ne.symm h60
                by_cases h61 : v = q
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  by_cases h73 : w = s
                  · subst w
                    have hh := hpar s
                    clear hpar
                    norm_num [*] at hh
                  · have h73r := Ne.symm h73
                    by_cases h75 : w = u
                    · subst w
                      exact Or.inr (Or.inl (by ring))
                    · have h75r := Ne.symm h75
                      have hh := hpar u
                      clear hpar
                      norm_num [*] at hh
                · have h61r := Ne.symm h61
                  by_cases h63 : v = s
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar s
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      have h73 : w ≠ s := by omega
                      have h73r := Ne.symm h73
                      by_cases h75 : w = u
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h75r := Ne.symm h75
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                  · have h63r := Ne.symm h63
                    by_cases h65 : v = u
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        exact Or.inr (Or.inl (by ring))
                      · have h71r := Ne.symm h71
                        have h73 : w ≠ s := by omega
                        have h73r := Ne.symm h73
                        have h75 : w ≠ u := by omega
                        have h75r := Ne.symm h75
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                    · have h65r := Ne.symm h65
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar u
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h73 : w = s
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h73r := Ne.symm h73
                            by_cases h75 : w = u
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h75r := Ne.symm h75
                              have h76 : w ≠ v := by omega
                              have h76r := Ne.symm h76
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
          · have h43r := Ne.symm h43
            by_cases h50 : u = p
            · subst u
              by_cases h60 : v = p
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                by_cases h71 : w = q
                · subst w
                  have hh := hpar s
                  clear hpar
                  norm_num [*] at hh
                · have h71r := Ne.symm h71
                  by_cases h73 : w = s
                  · subst w
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h73r := Ne.symm h73
                    have h74 : w ≠ t := by omega
                    have h74r := Ne.symm h74
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
              · have h60r := Ne.symm h60
                by_cases h61 : v = q
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  by_cases h73 : w = s
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h73r := Ne.symm h73
                    have h74 : w ≠ t := by omega
                    have h74r := Ne.symm h74
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                · have h61r := Ne.symm h61
                  by_cases h63 : v = s
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      have h73 : w ≠ s := by omega
                      have h73r := Ne.symm h73
                      have h74 : w ≠ t := by omega
                      have h74r := Ne.symm h74
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                  · have h63r := Ne.symm h63
                    by_cases h64 : v = t
                    · subst v
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h73 : w = s
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h73r := Ne.symm h73
                            have h74 : w ≠ t := by omega
                            have h74r := Ne.symm h74
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                    · have h64r := Ne.symm h64
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h73 : w = s
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h73r := Ne.symm h73
                            by_cases h74 : w = t
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h74r := Ne.symm h74
                              have h76 : w ≠ v := by omega
                              have h76r := Ne.symm h76
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
            · have h50r := Ne.symm h50
              by_cases h51 : u = q
              · subst u
                by_cases h60 : v = p
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h71r := Ne.symm h71
                    by_cases h73 : w = s
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h73r := Ne.symm h73
                      by_cases h74 : w = t
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h74r := Ne.symm h74
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                · have h60r := Ne.symm h60
                  by_cases h61 : v = q
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    have h71 : w ≠ q := by omega
                    have h71r := Ne.symm h71
                    by_cases h73 : w = s
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h73r := Ne.symm h73
                      have h74 : w ≠ t := by omega
                      have h74r := Ne.symm h74
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                  · have h61r := Ne.symm h61
                    by_cases h63 : v = s
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        have h73 : w ≠ s := by omega
                        have h73r := Ne.symm h73
                        by_cases h74 : w = t
                        · subst w
                          exact Or.inr (Or.inr (by ring))
                        · have h74r := Ne.symm h74
                          have hh := hpar t
                          clear hpar
                          norm_num [*] at hh
                    · have h63r := Ne.symm h63
                      by_cases h64 : v = t
                      · subst v
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            by_cases h73 : w = s
                            · subst w
                              exact Or.inr (Or.inr (by ring))
                            · have h73r := Ne.symm h73
                              have h74 : w ≠ t := by omega
                              have h74r := Ne.symm h74
                              have hh := hpar s
                              clear hpar
                              norm_num [*] at hh
                      · have h64r := Ne.symm h64
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar t
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              by_cases h74 : w = t
                              · subst w
                                have hh := hpar s
                                clear hpar
                                norm_num [*] at hh
                              · have h74r := Ne.symm h74
                                have h76 : w ≠ v := by omega
                                have h76r := Ne.symm h76
                                have hh := hpar s
                                clear hpar
                                norm_num [*] at hh
              · have h51r := Ne.symm h51
                by_cases h53 : u = s
                · subst u
                  by_cases h60 : v = p
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        by_cases h74 : w = t
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h74r := Ne.symm h74
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                  · have h60r := Ne.symm h60
                    by_cases h61 : v = q
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar s
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        by_cases h74 : w = t
                        · subst w
                          exact Or.inr (Or.inl (by ring))
                        · have h74r := Ne.symm h74
                          have hh := hpar t
                          clear hpar
                          norm_num [*] at hh
                    · have h61r := Ne.symm h61
                      by_cases h63 : v = s
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar s
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          have h73 : w ≠ s := by omega
                          have h73r := Ne.symm h73
                          have h74 : w ≠ t := by omega
                          have h74r := Ne.symm h74
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                      · have h63r := Ne.symm h63
                        by_cases h64 : v = t
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              exact Or.inr (Or.inl (by ring))
                            · have h71r := Ne.symm h71
                              by_cases h73 : w = s
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h73r := Ne.symm h73
                                have h74 : w ≠ t := by omega
                                have h74r := Ne.symm h74
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                        · have h64r := Ne.symm h64
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar t
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h73 : w = s
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h73r := Ne.symm h73
                                by_cases h74 : w = t
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h74r := Ne.symm h74
                                  have h76 : w ≠ v := by omega
                                  have h76r := Ne.symm h76
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                · have h53r := Ne.symm h53
                  have h54 : u ≠ t := by omega
                  have h54r := Ne.symm h54
                  by_cases h60 : v = p
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        by_cases h74 : w = t
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h74r := Ne.symm h74
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                  · have h60r := Ne.symm h60
                    by_cases h61 : v = q
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar t
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        by_cases h74 : w = t
                        · subst w
                          have hh := hpar s
                          clear hpar
                          norm_num [*] at hh
                        · have h74r := Ne.symm h74
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
                    · have h61r := Ne.symm h61
                      by_cases h63 : v = s
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar t
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          have h73 : w ≠ s := by omega
                          have h73r := Ne.symm h73
                          by_cases h74 : w = t
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h74r := Ne.symm h74
                            by_cases h75 : w = u
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h75r := Ne.symm h75
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                      · have h63r := Ne.symm h63
                        by_cases h64 : v = t
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar s
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h73 : w = s
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h73r := Ne.symm h73
                                have h74 : w ≠ t := by omega
                                have h74r := Ne.symm h74
                                by_cases h75 : w = u
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h75r := Ne.symm h75
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                        · have h64r := Ne.symm h64
                          by_cases h65 : v = u
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar s
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  have h74 : w ≠ t := by omega
                                  have h74r := Ne.symm h74
                                  have h75 : w ≠ u := by omega
                                  have h75r := Ne.symm h75
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                          · have h65r := Ne.symm h65
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar s
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  by_cases h74 : w = t
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h74r := Ne.symm h74
                                    by_cases h75 : w = u
                                    · subst w
                                      have hh := hpar q
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h75r := Ne.symm h75
                                      have h76 : w ≠ v := by omega
                                      have h76r := Ne.symm h76
                                      have hh := hpar q
                                      clear hpar
                                      norm_num [*] at hh
  · have h20r := Ne.symm h20
    by_cases h21 : r = q
    · subst r
      have h30 : s ≠ p := by omega
      have h30r := Ne.symm h30
      have h31 : s ≠ q := by omega
      have h31r := Ne.symm h31
      by_cases h40 : t = p
      · subst t
        have h50 : u ≠ p := by omega
        have h50r := Ne.symm h50
        by_cases h51 : u = q
        · subst u
          by_cases h60 : v = p
          · subst v
            have h70 : w ≠ p := by omega
            have h70r := Ne.symm h70
            by_cases h71 : w = q
            · subst w
              have hh := hpar p
              clear hpar
              norm_num [*] at hh
            · have h71r := Ne.symm h71
              by_cases h73 : w = s
              · subst w
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
              · have h73r := Ne.symm h73
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
          · have h60r := Ne.symm h60
            by_cases h61 : v = q
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              have h71 : w ≠ q := by omega
              have h71r := Ne.symm h71
              by_cases h73 : w = s
              · subst w
                exact Or.inl (by ring)
              · have h73r := Ne.symm h73
                have hh := hpar s
                clear hpar
                norm_num [*] at hh
            · have h61r := Ne.symm h61
              by_cases h63 : v = s
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                have h73 : w ≠ s := by omega
                have h73r := Ne.symm h73
                have hh := hpar q
                clear hpar
                norm_num [*] at hh
              · have h63r := Ne.symm h63
                by_cases h70 : w = p
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    have hh := hpar s
                    clear hpar
                    norm_num [*] at hh
                  · have h71r := Ne.symm h71
                    by_cases h73 : w = s
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h73r := Ne.symm h73
                      have h76 : w ≠ v := by omega
                      have h76r := Ne.symm h76
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
        · have h51r := Ne.symm h51
          by_cases h53 : u = s
          · subst u
            by_cases h60 : v = p
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              by_cases h71 : w = q
              · subst w
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
              · have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
            · have h60r := Ne.symm h60
              by_cases h61 : v = q
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
              · have h61r := Ne.symm h61
                by_cases h63 : v = s
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  have h73 : w ≠ s := by omega
                  have h73r := Ne.symm h73
                  have hh := hpar s
                  clear hpar
                  norm_num [*] at hh
                · have h63r := Ne.symm h63
                  by_cases h70 : w = p
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar s
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        have h76 : w ≠ v := by omega
                        have h76r := Ne.symm h76
                        have hh := hpar v
                        clear hpar
                        norm_num [*] at hh
          · have h53r := Ne.symm h53
            by_cases h60 : v = p
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              by_cases h71 : w = q
              · subst w
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
              · have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  by_cases h75 : w = u
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h75r := Ne.symm h75
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
            · have h60r := Ne.symm h60
              by_cases h61 : v = q
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  by_cases h75 : w = u
                  · subst w
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h75r := Ne.symm h75
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
              · have h61r := Ne.symm h61
                by_cases h63 : v = s
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  have h73 : w ≠ s := by omega
                  have h73r := Ne.symm h73
                  by_cases h75 : w = u
                  · subst w
                    exact Or.inr (Or.inr (by ring))
                  · have h75r := Ne.symm h75
                    have hh := hpar u
                    clear hpar
                    norm_num [*] at hh
                · have h63r := Ne.symm h63
                  by_cases h65 : v = u
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h73 : w = s
                      · subst w
                        exact Or.inr (Or.inr (by ring))
                      · have h73r := Ne.symm h73
                        have h75 : w ≠ u := by omega
                        have h75r := Ne.symm h75
                        have hh := hpar s
                        clear hpar
                        norm_num [*] at hh
                  · have h65r := Ne.symm h65
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar u
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have h76 : w ≠ v := by omega
                            have h76r := Ne.symm h76
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
      · have h40r := Ne.symm h40
        by_cases h41 : t = q
        · subst t
          have h50 : u ≠ p := by omega
          have h50r := Ne.symm h50
          have h51 : u ≠ q := by omega
          have h51r := Ne.symm h51
          by_cases h53 : u = s
          · subst u
            by_cases h60 : v = p
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              by_cases h71 : w = q
              · subst w
                exact Or.inl (by ring)
              · have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
            · have h60r := Ne.symm h60
              by_cases h61 : v = q
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
              · have h61r := Ne.symm h61
                by_cases h63 : v = s
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  have h73 : w ≠ s := by omega
                  have h73r := Ne.symm h73
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h63r := Ne.symm h63
                  by_cases h70 : w = p
                  · subst w
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        have h76 : w ≠ v := by omega
                        have h76r := Ne.symm h76
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
          · have h53r := Ne.symm h53
            by_cases h60 : v = p
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              by_cases h71 : w = q
              · subst w
                have hh := hpar s
                clear hpar
                norm_num [*] at hh
              · have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  by_cases h75 : w = u
                  · subst w
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h75r := Ne.symm h75
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
            · have h60r := Ne.symm h60
              by_cases h61 : v = q
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  by_cases h75 : w = u
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h75r := Ne.symm h75
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
              · have h61r := Ne.symm h61
                by_cases h63 : v = s
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  have h73 : w ≠ s := by omega
                  have h73r := Ne.symm h73
                  by_cases h75 : w = u
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h75r := Ne.symm h75
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                · have h63r := Ne.symm h63
                  by_cases h65 : v = u
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    have h71 : w ≠ q := by omega
                    have h71r := Ne.symm h71
                    by_cases h73 : w = s
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h73r := Ne.symm h73
                      have h75 : w ≠ u := by omega
                      have h75r := Ne.symm h75
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                  · have h65r := Ne.symm h65
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have h76 : w ≠ v := by omega
                            have h76r := Ne.symm h76
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
        · have h41r := Ne.symm h41
          by_cases h43 : t = s
          · subst t
            have h50 : u ≠ p := by omega
            have h50r := Ne.symm h50
            have h51 : u ≠ q := by omega
            have h51r := Ne.symm h51
            have h53 : u ≠ s := by omega
            have h53r := Ne.symm h53
            by_cases h60 : v = p
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              by_cases h71 : w = q
              · subst w
                have hh := hpar q
                clear hpar
                norm_num [*] at hh
              · have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar s
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  by_cases h75 : w = u
                  · subst w
                    exact Or.inr (Or.inl (by ring))
                  · have h75r := Ne.symm h75
                    have hh := hpar u
                    clear hpar
                    norm_num [*] at hh
            · have h60r := Ne.symm h60
              by_cases h61 : v = q
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                by_cases h73 : w = s
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h73r := Ne.symm h73
                  by_cases h75 : w = u
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h75r := Ne.symm h75
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
              · have h61r := Ne.symm h61
                by_cases h63 : v = s
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  have h73 : w ≠ s := by omega
                  have h73r := Ne.symm h73
                  by_cases h75 : w = u
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h75r := Ne.symm h75
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                · have h63r := Ne.symm h63
                  by_cases h65 : v = u
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    have h71 : w ≠ q := by omega
                    have h71r := Ne.symm h71
                    have h73 : w ≠ s := by omega
                    have h73r := Ne.symm h73
                    have h75 : w ≠ u := by omega
                    have h75r := Ne.symm h75
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h65r := Ne.symm h65
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar u
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have h76 : w ≠ v := by omega
                            have h76r := Ne.symm h76
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
          · have h43r := Ne.symm h43
            by_cases h50 : u = p
            · subst u
              by_cases h60 : v = p
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                by_cases h71 : w = q
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h71r := Ne.symm h71
                  by_cases h73 : w = s
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h73r := Ne.symm h73
                    have h74 : w ≠ t := by omega
                    have h74r := Ne.symm h74
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
              · have h60r := Ne.symm h60
                by_cases h61 : v = q
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  by_cases h73 : w = s
                  · subst w
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h73r := Ne.symm h73
                    have h74 : w ≠ t := by omega
                    have h74r := Ne.symm h74
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                · have h61r := Ne.symm h61
                  by_cases h63 : v = s
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    have h71 : w ≠ q := by omega
                    have h71r := Ne.symm h71
                    have h73 : w ≠ s := by omega
                    have h73r := Ne.symm h73
                    have h74 : w ≠ t := by omega
                    have h74r := Ne.symm h74
                    have hh := hpar t
                    clear hpar
                    norm_num [*] at hh
                  · have h63r := Ne.symm h63
                    by_cases h64 : v = t
                    · subst v
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h73 : w = s
                          · subst w
                            exact Or.inr (Or.inr (by ring))
                          · have h73r := Ne.symm h73
                            have h74 : w ≠ t := by omega
                            have h74r := Ne.symm h74
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
                    · have h64r := Ne.symm h64
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h73 : w = s
                          · subst w
                            have hh := hpar t
                            clear hpar
                            norm_num [*] at hh
                          · have h73r := Ne.symm h73
                            by_cases h74 : w = t
                            · subst w
                              have hh := hpar s
                              clear hpar
                              norm_num [*] at hh
                            · have h74r := Ne.symm h74
                              have h76 : w ≠ v := by omega
                              have h76r := Ne.symm h76
                              have hh := hpar s
                              clear hpar
                              norm_num [*] at hh
            · have h50r := Ne.symm h50
              by_cases h51 : u = q
              · subst u
                by_cases h60 : v = p
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    have hh := hpar s
                    clear hpar
                    norm_num [*] at hh
                  · have h71r := Ne.symm h71
                    by_cases h73 : w = s
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h73r := Ne.symm h73
                      by_cases h74 : w = t
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h74r := Ne.symm h74
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                · have h60r := Ne.symm h60
                  by_cases h61 : v = q
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    have h71 : w ≠ q := by omega
                    have h71r := Ne.symm h71
                    by_cases h73 : w = s
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h73r := Ne.symm h73
                      have h74 : w ≠ t := by omega
                      have h74r := Ne.symm h74
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                  · have h61r := Ne.symm h61
                    by_cases h63 : v = s
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      have h73 : w ≠ s := by omega
                      have h73r := Ne.symm h73
                      have h74 : w ≠ t := by omega
                      have h74r := Ne.symm h74
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h63r := Ne.symm h63
                      by_cases h64 : v = t
                      · subst v
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              have h74 : w ≠ t := by omega
                              have h74r := Ne.symm h74
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                      · have h64r := Ne.symm h64
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              by_cases h74 : w = t
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h74r := Ne.symm h74
                                have h76 : w ≠ v := by omega
                                have h76r := Ne.symm h76
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
              · have h51r := Ne.symm h51
                by_cases h53 : u = s
                · subst u
                  by_cases h60 : v = p
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar s
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        by_cases h74 : w = t
                        · subst w
                          exact Or.inr (Or.inl (by ring))
                        · have h74r := Ne.symm h74
                          have hh := hpar t
                          clear hpar
                          norm_num [*] at hh
                  · have h60r := Ne.symm h60
                    by_cases h61 : v = q
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        by_cases h74 : w = t
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h74r := Ne.symm h74
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                    · have h61r := Ne.symm h61
                      by_cases h63 : v = s
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        have h71 : w ≠ q := by omega
                        have h71r := Ne.symm h71
                        have h73 : w ≠ s := by omega
                        have h73r := Ne.symm h73
                        have h74 : w ≠ t := by omega
                        have h74r := Ne.symm h74
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h63r := Ne.symm h63
                        by_cases h64 : v = t
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            exact Or.inr (Or.inl (by ring))
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h73 : w = s
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h73r := Ne.symm h73
                                have h74 : w ≠ t := by omega
                                have h74r := Ne.symm h74
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                        · have h64r := Ne.symm h64
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar t
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h73 : w = s
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h73r := Ne.symm h73
                                by_cases h74 : w = t
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h74r := Ne.symm h74
                                  have h76 : w ≠ v := by omega
                                  have h76r := Ne.symm h76
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                · have h53r := Ne.symm h53
                  have h54 : u ≠ t := by omega
                  have h54r := Ne.symm h54
                  by_cases h60 : v = p
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar t
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        by_cases h74 : w = t
                        · subst w
                          have hh := hpar s
                          clear hpar
                          norm_num [*] at hh
                        · have h74r := Ne.symm h74
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
                  · have h60r := Ne.symm h60
                    by_cases h61 : v = q
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        by_cases h74 : w = t
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h74r := Ne.symm h74
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                    · have h61r := Ne.symm h61
                      by_cases h63 : v = s
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        have h71 : w ≠ q := by omega
                        have h71r := Ne.symm h71
                        have h73 : w ≠ s := by omega
                        have h73r := Ne.symm h73
                        by_cases h74 : w = t
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h74r := Ne.symm h74
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                      · have h63r := Ne.symm h63
                        by_cases h64 : v = t
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h73 : w = s
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h73r := Ne.symm h73
                                have h74 : w ≠ t := by omega
                                have h74r := Ne.symm h74
                                by_cases h75 : w = u
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h75r := Ne.symm h75
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                        · have h64r := Ne.symm h64
                          by_cases h65 : v = u
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar s
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  have h74 : w ≠ t := by omega
                                  have h74r := Ne.symm h74
                                  have h75 : w ≠ u := by omega
                                  have h75r := Ne.symm h75
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                          · have h65r := Ne.symm h65
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar s
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  by_cases h74 : w = t
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h74r := Ne.symm h74
                                    by_cases h75 : w = u
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h75r := Ne.symm h75
                                      have h76 : w ≠ v := by omega
                                      have h76r := Ne.symm h76
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
    · have h21r := Ne.symm h21
      by_cases h30 : s = p
      · subst s
        by_cases h40 : t = p
        · subst t
          have h50 : u ≠ p := by omega
          have h50r := Ne.symm h50
          by_cases h51 : u = q
          · subst u
            by_cases h60 : v = p
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              by_cases h71 : w = q
              · subst w
                have hh := hpar q
                clear hpar
                norm_num [*] at hh
              · have h71r := Ne.symm h71
                have h72 : w ≠ r := by omega
                have h72r := Ne.symm h72
                have hh := hpar r
                clear hpar
                norm_num [*] at hh
            · have h60r := Ne.symm h60
              by_cases h61 : v = q
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                have h72 : w ≠ r := by omega
                have h72r := Ne.symm h72
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
              · have h61r := Ne.symm h61
                by_cases h62 : v = r
                · subst v
                  by_cases h70 : w = p
                  · subst w
                    exact Or.inl (by ring)
                  · have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                · have h62r := Ne.symm h62
                  by_cases h70 : w = p
                  · subst w
                    have hh := hpar r
                    clear hpar
                    norm_num [*] at hh
                  · have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h72 : w = r
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h72r := Ne.symm h72
                        have h76 : w ≠ v := by omega
                        have h76r := Ne.symm h76
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
          · have h51r := Ne.symm h51
            have h52 : u ≠ r := by omega
            have h52r := Ne.symm h52
            by_cases h60 : v = p
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              by_cases h71 : w = q
              · subst w
                have hh := hpar r
                clear hpar
                norm_num [*] at hh
              · have h71r := Ne.symm h71
                have h72 : w ≠ r := by omega
                have h72r := Ne.symm h72
                by_cases h75 : w = u
                · subst w
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
                · have h75r := Ne.symm h75
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
            · have h60r := Ne.symm h60
              by_cases h61 : v = q
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                have h72 : w ≠ r := by omega
                have h72r := Ne.symm h72
                by_cases h75 : w = u
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h75r := Ne.symm h75
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
              · have h61r := Ne.symm h61
                by_cases h62 : v = r
                · subst v
                  by_cases h70 : w = p
                  · subst w
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      by_cases h75 : w = u
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h75r := Ne.symm h75
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                · have h62r := Ne.symm h62
                  by_cases h65 : v = u
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      have h75 : w ≠ u := by omega
                      have h75r := Ne.symm h75
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                  · have h65r := Ne.symm h65
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        by_cases h72 : w = r
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h72r := Ne.symm h72
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have h76 : w ≠ v := by omega
                            have h76r := Ne.symm h76
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
        · have h40r := Ne.symm h40
          by_cases h41 : t = q
          · subst t
            have h50 : u ≠ p := by omega
            have h50r := Ne.symm h50
            have h51 : u ≠ q := by omega
            have h51r := Ne.symm h51
            have h52 : u ≠ r := by omega
            have h52r := Ne.symm h52
            by_cases h60 : v = p
            · subst v
              have h70 : w ≠ p := by omega
              have h70r := Ne.symm h70
              by_cases h71 : w = q
              · subst w
                have hh := hpar p
                clear hpar
                norm_num [*] at hh
              · have h71r := Ne.symm h71
                have h72 : w ≠ r := by omega
                have h72r := Ne.symm h72
                by_cases h75 : w = u
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h75r := Ne.symm h75
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
            · have h60r := Ne.symm h60
              by_cases h61 : v = q
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                have h71 : w ≠ q := by omega
                have h71r := Ne.symm h71
                have h72 : w ≠ r := by omega
                have h72r := Ne.symm h72
                by_cases h75 : w = u
                · subst w
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
                · have h75r := Ne.symm h75
                  have hh := hpar q
                  clear hpar
                  norm_num [*] at hh
              · have h61r := Ne.symm h61
                by_cases h62 : v = r
                · subst v
                  by_cases h70 : w = p
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      by_cases h75 : w = u
                      · subst w
                        exact Or.inr (Or.inr (by ring))
                      · have h75r := Ne.symm h75
                        have hh := hpar u
                        clear hpar
                        norm_num [*] at hh
                · have h62r := Ne.symm h62
                  by_cases h65 : v = u
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    have h71 : w ≠ q := by omega
                    have h71r := Ne.symm h71
                    have h72 : w ≠ r := by omega
                    have h72r := Ne.symm h72
                    have h75 : w ≠ u := by omega
                    have h75r := Ne.symm h75
                    have hh := hpar r
                    clear hpar
                    norm_num [*] at hh
                  · have h65r := Ne.symm h65
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        by_cases h72 : w = r
                        · subst w
                          have hh := hpar u
                          clear hpar
                          norm_num [*] at hh
                        · have h72r := Ne.symm h72
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have h76 : w ≠ v := by omega
                            have h76r := Ne.symm h76
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
          · have h41r := Ne.symm h41
            by_cases h42 : t = r
            · subst t
              by_cases h50 : u = p
              · subst u
                by_cases h60 : v = p
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    exact Or.inl (by ring)
                  · have h71r := Ne.symm h71
                    have h72 : w ≠ r := by omega
                    have h72r := Ne.symm h72
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                · have h60r := Ne.symm h60
                  by_cases h61 : v = q
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    have h71 : w ≠ q := by omega
                    have h71r := Ne.symm h71
                    have h72 : w ≠ r := by omega
                    have h72r := Ne.symm h72
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h61r := Ne.symm h61
                    by_cases h62 : v = r
                    · subst v
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          have h72 : w ≠ r := by omega
                          have h72r := Ne.symm h72
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                    · have h62r := Ne.symm h62
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h72r := Ne.symm h72
                            have h76 : w ≠ v := by omega
                            have h76r := Ne.symm h76
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
              · have h50r := Ne.symm h50
                by_cases h51 : u = q
                · subst u
                  by_cases h60 : v = p
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                  · have h60r := Ne.symm h60
                    by_cases h61 : v = q
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h61r := Ne.symm h61
                      by_cases h62 : v = r
                      · subst v
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            have h72 : w ≠ r := by omega
                            have h72r := Ne.symm h72
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                      · have h62r := Ne.symm h62
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            by_cases h72 : w = r
                            · subst w
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                            · have h72r := Ne.symm h72
                              have h76 : w ≠ v := by omega
                              have h76r := Ne.symm h76
                              have hh := hpar v
                              clear hpar
                              norm_num [*] at hh
                · have h51r := Ne.symm h51
                  have h52 : u ≠ r := by omega
                  have h52r := Ne.symm h52
                  by_cases h60 : v = p
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      by_cases h75 : w = u
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h75r := Ne.symm h75
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                  · have h60r := Ne.symm h60
                    by_cases h61 : v = q
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      by_cases h75 : w = u
                      · subst w
                        exact Or.inr (Or.inl (by ring))
                      · have h75r := Ne.symm h75
                        have hh := hpar u
                        clear hpar
                        norm_num [*] at hh
                    · have h61r := Ne.symm h61
                      by_cases h62 : v = r
                      · subst v
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            have h72 : w ≠ r := by omega
                            have h72r := Ne.symm h72
                            by_cases h75 : w = u
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h75r := Ne.symm h75
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                      · have h62r := Ne.symm h62
                        by_cases h65 : v = u
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              exact Or.inr (Or.inl (by ring))
                            · have h71r := Ne.symm h71
                              have h72 : w ≠ r := by omega
                              have h72r := Ne.symm h72
                              have h75 : w ≠ u := by omega
                              have h75r := Ne.symm h75
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                        · have h65r := Ne.symm h65
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar u
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h72 : w = r
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h72r := Ne.symm h72
                                by_cases h75 : w = u
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h75r := Ne.symm h75
                                  have h76 : w ≠ v := by omega
                                  have h76r := Ne.symm h76
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
            · have h42r := Ne.symm h42
              by_cases h50 : u = p
              · subst u
                by_cases h60 : v = p
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    have hh := hpar r
                    clear hpar
                    norm_num [*] at hh
                  · have h71r := Ne.symm h71
                    have h72 : w ≠ r := by omega
                    have h72r := Ne.symm h72
                    have h74 : w ≠ t := by omega
                    have h74r := Ne.symm h74
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                · have h60r := Ne.symm h60
                  by_cases h61 : v = q
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    have h71 : w ≠ q := by omega
                    have h71r := Ne.symm h71
                    have h72 : w ≠ r := by omega
                    have h72r := Ne.symm h72
                    have h74 : w ≠ t := by omega
                    have h74r := Ne.symm h74
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h61r := Ne.symm h61
                    by_cases h62 : v = r
                    · subst v
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          have h72 : w ≠ r := by omega
                          have h72r := Ne.symm h72
                          by_cases h74 : w = t
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h74r := Ne.symm h74
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                    · have h62r := Ne.symm h62
                      by_cases h64 : v = t
                      · subst v
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            by_cases h72 : w = r
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h72r := Ne.symm h72
                              have h74 : w ≠ t := by omega
                              have h74r := Ne.symm h74
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                      · have h64r := Ne.symm h64
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            by_cases h72 : w = r
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h72r := Ne.symm h72
                              by_cases h74 : w = t
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h74r := Ne.symm h74
                                have h76 : w ≠ v := by omega
                                have h76r := Ne.symm h76
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
              · have h50r := Ne.symm h50
                by_cases h51 : u = q
                · subst u
                  by_cases h60 : v = p
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      by_cases h74 : w = t
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h74r := Ne.symm h74
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                  · have h60r := Ne.symm h60
                    by_cases h61 : v = q
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      have h74 : w ≠ t := by omega
                      have h74r := Ne.symm h74
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h61r := Ne.symm h61
                      by_cases h62 : v = r
                      · subst v
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            have h72 : w ≠ r := by omega
                            have h72r := Ne.symm h72
                            by_cases h74 : w = t
                            · subst w
                              exact Or.inr (Or.inr (by ring))
                            · have h74r := Ne.symm h74
                              have hh := hpar t
                              clear hpar
                              norm_num [*] at hh
                      · have h62r := Ne.symm h62
                        by_cases h64 : v = t
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h72 : w = r
                              · subst w
                                exact Or.inr (Or.inr (by ring))
                              · have h72r := Ne.symm h72
                                have h74 : w ≠ t := by omega
                                have h74r := Ne.symm h74
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                        · have h64r := Ne.symm h64
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h72 : w = r
                              · subst w
                                have hh := hpar t
                                clear hpar
                                norm_num [*] at hh
                              · have h72r := Ne.symm h72
                                by_cases h74 : w = t
                                · subst w
                                  have hh := hpar r
                                  clear hpar
                                  norm_num [*] at hh
                                · have h74r := Ne.symm h74
                                  have h76 : w ≠ v := by omega
                                  have h76r := Ne.symm h76
                                  have hh := hpar r
                                  clear hpar
                                  norm_num [*] at hh
                · have h51r := Ne.symm h51
                  by_cases h52 : u = r
                  · subst u
                    by_cases h60 : v = p
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        have h74 : w ≠ t := by omega
                        have h74r := Ne.symm h74
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                    · have h60r := Ne.symm h60
                      by_cases h61 : v = q
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        have h71 : w ≠ q := by omega
                        have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        have h74 : w ≠ t := by omega
                        have h74r := Ne.symm h74
                        have hh := hpar t
                        clear hpar
                        norm_num [*] at hh
                      · have h61r := Ne.symm h61
                        by_cases h62 : v = r
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              have h72 : w ≠ r := by omega
                              have h72r := Ne.symm h72
                              have h74 : w ≠ t := by omega
                              have h74r := Ne.symm h74
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                        · have h62r := Ne.symm h62
                          by_cases h64 : v = t
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                exact Or.inr (Or.inl (by ring))
                              · have h71r := Ne.symm h71
                                by_cases h72 : w = r
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h72r := Ne.symm h72
                                  have h74 : w ≠ t := by omega
                                  have h74r := Ne.symm h74
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                          · have h64r := Ne.symm h64
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar t
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                by_cases h72 : w = r
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h72r := Ne.symm h72
                                  by_cases h74 : w = t
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h74r := Ne.symm h74
                                    have h76 : w ≠ v := by omega
                                    have h76r := Ne.symm h76
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                  · have h52r := Ne.symm h52
                    have h54 : u ≠ t := by omega
                    have h54r := Ne.symm h54
                    by_cases h60 : v = p
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        by_cases h74 : w = t
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h74r := Ne.symm h74
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                    · have h60r := Ne.symm h60
                      by_cases h61 : v = q
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        have h71 : w ≠ q := by omega
                        have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        by_cases h74 : w = t
                        · subst w
                          have hh := hpar r
                          clear hpar
                          norm_num [*] at hh
                        · have h74r := Ne.symm h74
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                      · have h61r := Ne.symm h61
                        by_cases h62 : v = r
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar t
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              have h72 : w ≠ r := by omega
                              have h72r := Ne.symm h72
                              by_cases h74 : w = t
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h74r := Ne.symm h74
                                by_cases h75 : w = u
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h75r := Ne.symm h75
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                        · have h62r := Ne.symm h62
                          by_cases h64 : v = t
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                by_cases h72 : w = r
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h72r := Ne.symm h72
                                  have h74 : w ≠ t := by omega
                                  have h74r := Ne.symm h74
                                  by_cases h75 : w = u
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h75r := Ne.symm h75
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                          · have h64r := Ne.symm h64
                            by_cases h65 : v = u
                            · subst v
                              by_cases h70 : w = p
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar r
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  by_cases h72 : w = r
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h72r := Ne.symm h72
                                    have h74 : w ≠ t := by omega
                                    have h74r := Ne.symm h74
                                    have h75 : w ≠ u := by omega
                                    have h75r := Ne.symm h75
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                            · have h65r := Ne.symm h65
                              by_cases h70 : w = p
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar r
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  by_cases h72 : w = r
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h72r := Ne.symm h72
                                    by_cases h74 : w = t
                                    · subst w
                                      have hh := hpar q
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h74r := Ne.symm h74
                                      by_cases h75 : w = u
                                      · subst w
                                        have hh := hpar q
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h75r := Ne.symm h75
                                        have h76 : w ≠ v := by omega
                                        have h76r := Ne.symm h76
                                        have hh := hpar q
                                        clear hpar
                                        norm_num [*] at hh
      · have h30r := Ne.symm h30
        by_cases h31 : s = q
        · subst s
          by_cases h40 : t = p
          · subst t
            have h50 : u ≠ p := by omega
            have h50r := Ne.symm h50
            by_cases h51 : u = q
            · subst u
              by_cases h60 : v = p
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                by_cases h71 : w = q
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h71r := Ne.symm h71
                  by_cases h72 : w = r
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h72r := Ne.symm h72
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
              · have h60r := Ne.symm h60
                by_cases h61 : v = q
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  have h72 : w ≠ r := by omega
                  have h72r := Ne.symm h72
                  have hh := hpar r
                  clear hpar
                  norm_num [*] at hh
                · have h61r := Ne.symm h61
                  by_cases h62 : v = r
                  · subst v
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        exact Or.inl (by ring)
                      · have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                  · have h62r := Ne.symm h62
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar r
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        by_cases h72 : w = r
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h72r := Ne.symm h72
                          have h76 : w ≠ v := by omega
                          have h76r := Ne.symm h76
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
            · have h51r := Ne.symm h51
              by_cases h52 : u = r
              · subst u
                by_cases h60 : v = p
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h71r := Ne.symm h71
                    by_cases h72 : w = r
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h72r := Ne.symm h72
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                · have h60r := Ne.symm h60
                  by_cases h61 : v = q
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    have h71 : w ≠ q := by omega
                    have h71r := Ne.symm h71
                    have h72 : w ≠ r := by omega
                    have h72r := Ne.symm h72
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h61r := Ne.symm h61
                    by_cases h62 : v = r
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        have hh := hpar r
                        clear hpar
                        norm_num [*] at hh
                    · have h62r := Ne.symm h62
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                          · have h72r := Ne.symm h72
                            have h76 : w ≠ v := by omega
                            have h76r := Ne.symm h76
                            have hh := hpar v
                            clear hpar
                            norm_num [*] at hh
              · have h52r := Ne.symm h52
                by_cases h60 : v = p
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h71r := Ne.symm h71
                    by_cases h72 : w = r
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h72r := Ne.symm h72
                      by_cases h75 : w = u
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h75r := Ne.symm h75
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                · have h60r := Ne.symm h60
                  by_cases h61 : v = q
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    have h71 : w ≠ q := by omega
                    have h71r := Ne.symm h71
                    have h72 : w ≠ r := by omega
                    have h72r := Ne.symm h72
                    by_cases h75 : w = u
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h75r := Ne.symm h75
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                  · have h61r := Ne.symm h61
                    by_cases h62 : v = r
                    · subst v
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          have h72 : w ≠ r := by omega
                          have h72r := Ne.symm h72
                          by_cases h75 : w = u
                          · subst w
                            exact Or.inr (Or.inr (by ring))
                          · have h75r := Ne.symm h75
                            have hh := hpar u
                            clear hpar
                            norm_num [*] at hh
                    · have h62r := Ne.symm h62
                      by_cases h65 : v = u
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            exact Or.inr (Or.inr (by ring))
                          · have h72r := Ne.symm h72
                            have h75 : w ≠ u := by omega
                            have h75r := Ne.symm h75
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                      · have h65r := Ne.symm h65
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            by_cases h72 : w = r
                            · subst w
                              have hh := hpar u
                              clear hpar
                              norm_num [*] at hh
                            · have h72r := Ne.symm h72
                              by_cases h75 : w = u
                              · subst w
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                              · have h75r := Ne.symm h75
                                have h76 : w ≠ v := by omega
                                have h76r := Ne.symm h76
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
          · have h40r := Ne.symm h40
            by_cases h41 : t = q
            · subst t
              have h50 : u ≠ p := by omega
              have h50r := Ne.symm h50
              have h51 : u ≠ q := by omega
              have h51r := Ne.symm h51
              have h52 : u ≠ r := by omega
              have h52r := Ne.symm h52
              by_cases h60 : v = p
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                by_cases h71 : w = q
                · subst w
                  have hh := hpar r
                  clear hpar
                  norm_num [*] at hh
                · have h71r := Ne.symm h71
                  by_cases h72 : w = r
                  · subst w
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h72r := Ne.symm h72
                    by_cases h75 : w = u
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h75r := Ne.symm h75
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
              · have h60r := Ne.symm h60
                by_cases h61 : v = q
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  have h72 : w ≠ r := by omega
                  have h72r := Ne.symm h72
                  by_cases h75 : w = u
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h75r := Ne.symm h75
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                · have h61r := Ne.symm h61
                  by_cases h62 : v = r
                  · subst v
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        by_cases h75 : w = u
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h75r := Ne.symm h75
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                  · have h62r := Ne.symm h62
                    by_cases h65 : v = u
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      have h75 : w ≠ u := by omega
                      have h75r := Ne.symm h75
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h65r := Ne.symm h65
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h72r := Ne.symm h72
                            by_cases h75 : w = u
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h75r := Ne.symm h75
                              have h76 : w ≠ v := by omega
                              have h76r := Ne.symm h76
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
            · have h41r := Ne.symm h41
              by_cases h42 : t = r
              · subst t
                by_cases h50 : u = p
                · subst u
                  by_cases h60 : v = p
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                  · have h60r := Ne.symm h60
                    by_cases h61 : v = q
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h61r := Ne.symm h61
                      by_cases h62 : v = r
                      · subst v
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            have h72 : w ≠ r := by omega
                            have h72r := Ne.symm h72
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                      · have h62r := Ne.symm h62
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            by_cases h72 : w = r
                            · subst w
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                            · have h72r := Ne.symm h72
                              have h76 : w ≠ v := by omega
                              have h76r := Ne.symm h76
                              have hh := hpar v
                              clear hpar
                              norm_num [*] at hh
                · have h50r := Ne.symm h50
                  by_cases h51 : u = q
                  · subst u
                    by_cases h60 : v = p
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        exact Or.inl (by ring)
                      · have h71r := Ne.symm h71
                        by_cases h72 : w = r
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h72r := Ne.symm h72
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                    · have h60r := Ne.symm h60
                      by_cases h61 : v = q
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        have h71 : w ≠ q := by omega
                        have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h61r := Ne.symm h61
                        by_cases h62 : v = r
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              have h72 : w ≠ r := by omega
                              have h72r := Ne.symm h72
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                        · have h62r := Ne.symm h62
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h72 : w = r
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h72r := Ne.symm h72
                                have h76 : w ≠ v := by omega
                                have h76r := Ne.symm h76
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                  · have h51r := Ne.symm h51
                    have h52 : u ≠ r := by omega
                    have h52r := Ne.symm h52
                    by_cases h60 : v = p
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        by_cases h72 : w = r
                        · subst w
                          have hh := hpar r
                          clear hpar
                          norm_num [*] at hh
                        · have h72r := Ne.symm h72
                          by_cases h75 : w = u
                          · subst w
                            exact Or.inr (Or.inl (by ring))
                          · have h75r := Ne.symm h75
                            have hh := hpar u
                            clear hpar
                            norm_num [*] at hh
                    · have h60r := Ne.symm h60
                      by_cases h61 : v = q
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        have h71 : w ≠ q := by omega
                        have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        by_cases h75 : w = u
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h75r := Ne.symm h75
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                      · have h61r := Ne.symm h61
                        by_cases h62 : v = r
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              have h72 : w ≠ r := by omega
                              have h72r := Ne.symm h72
                              by_cases h75 : w = u
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h75r := Ne.symm h75
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                        · have h62r := Ne.symm h62
                          by_cases h65 : v = u
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              exact Or.inr (Or.inl (by ring))
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                have h72 : w ≠ r := by omega
                                have h72r := Ne.symm h72
                                have h75 : w ≠ u := by omega
                                have h75r := Ne.symm h75
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                          · have h65r := Ne.symm h65
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar u
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                by_cases h72 : w = r
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h72r := Ne.symm h72
                                  by_cases h75 : w = u
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h75r := Ne.symm h75
                                    have h76 : w ≠ v := by omega
                                    have h76r := Ne.symm h76
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
              · have h42r := Ne.symm h42
                by_cases h50 : u = p
                · subst u
                  by_cases h60 : v = p
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h72 : w = r
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h72r := Ne.symm h72
                        have h74 : w ≠ t := by omega
                        have h74r := Ne.symm h74
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                  · have h60r := Ne.symm h60
                    by_cases h61 : v = q
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      have h74 : w ≠ t := by omega
                      have h74r := Ne.symm h74
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h61r := Ne.symm h61
                      by_cases h62 : v = r
                      · subst v
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            have h72 : w ≠ r := by omega
                            have h72r := Ne.symm h72
                            by_cases h74 : w = t
                            · subst w
                              exact Or.inr (Or.inr (by ring))
                            · have h74r := Ne.symm h74
                              have hh := hpar t
                              clear hpar
                              norm_num [*] at hh
                      · have h62r := Ne.symm h62
                        by_cases h64 : v = t
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h72 : w = r
                              · subst w
                                exact Or.inr (Or.inr (by ring))
                              · have h72r := Ne.symm h72
                                have h74 : w ≠ t := by omega
                                have h74r := Ne.symm h74
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                        · have h64r := Ne.symm h64
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h72 : w = r
                              · subst w
                                have hh := hpar t
                                clear hpar
                                norm_num [*] at hh
                              · have h72r := Ne.symm h72
                                by_cases h74 : w = t
                                · subst w
                                  have hh := hpar r
                                  clear hpar
                                  norm_num [*] at hh
                                · have h74r := Ne.symm h74
                                  have h76 : w ≠ v := by omega
                                  have h76r := Ne.symm h76
                                  have hh := hpar r
                                  clear hpar
                                  norm_num [*] at hh
                · have h50r := Ne.symm h50
                  by_cases h51 : u = q
                  · subst u
                    by_cases h60 : v = p
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar r
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        by_cases h72 : w = r
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h72r := Ne.symm h72
                          by_cases h74 : w = t
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h74r := Ne.symm h74
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                    · have h60r := Ne.symm h60
                      by_cases h61 : v = q
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        have h71 : w ≠ q := by omega
                        have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        have h74 : w ≠ t := by omega
                        have h74r := Ne.symm h74
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h61r := Ne.symm h61
                        by_cases h62 : v = r
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              have h72 : w ≠ r := by omega
                              have h72r := Ne.symm h72
                              by_cases h74 : w = t
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h74r := Ne.symm h74
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                        · have h62r := Ne.symm h62
                          by_cases h64 : v = t
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                by_cases h72 : w = r
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h72r := Ne.symm h72
                                  have h74 : w ≠ t := by omega
                                  have h74r := Ne.symm h74
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                          · have h64r := Ne.symm h64
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                by_cases h72 : w = r
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h72r := Ne.symm h72
                                  by_cases h74 : w = t
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h74r := Ne.symm h74
                                    have h76 : w ≠ v := by omega
                                    have h76r := Ne.symm h76
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                  · have h51r := Ne.symm h51
                    by_cases h52 : u = r
                    · subst u
                      by_cases h60 : v = p
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                          · have h72r := Ne.symm h72
                            by_cases h74 : w = t
                            · subst w
                              exact Or.inr (Or.inl (by ring))
                            · have h74r := Ne.symm h74
                              have hh := hpar t
                              clear hpar
                              norm_num [*] at hh
                      · have h60r := Ne.symm h60
                        by_cases h61 : v = q
                        · subst v
                          have h70 : w ≠ p := by omega
                          have h70r := Ne.symm h70
                          have h71 : w ≠ q := by omega
                          have h71r := Ne.symm h71
                          have h72 : w ≠ r := by omega
                          have h72r := Ne.symm h72
                          have h74 : w ≠ t := by omega
                          have h74r := Ne.symm h74
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h61r := Ne.symm h61
                          by_cases h62 : v = r
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                have h72 : w ≠ r := by omega
                                have h72r := Ne.symm h72
                                have h74 : w ≠ t := by omega
                                have h74r := Ne.symm h74
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                          · have h62r := Ne.symm h62
                            by_cases h64 : v = t
                            · subst v
                              by_cases h70 : w = p
                              · subst w
                                exact Or.inr (Or.inl (by ring))
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  by_cases h72 : w = r
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h72r := Ne.symm h72
                                    have h74 : w ≠ t := by omega
                                    have h74r := Ne.symm h74
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                            · have h64r := Ne.symm h64
                              by_cases h70 : w = p
                              · subst w
                                have hh := hpar t
                                clear hpar
                                norm_num [*] at hh
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  by_cases h72 : w = r
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h72r := Ne.symm h72
                                    by_cases h74 : w = t
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h74r := Ne.symm h74
                                      have h76 : w ≠ v := by omega
                                      have h76r := Ne.symm h76
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                    · have h52r := Ne.symm h52
                      have h54 : u ≠ t := by omega
                      have h54r := Ne.symm h54
                      by_cases h60 : v = p
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            have hh := hpar t
                            clear hpar
                            norm_num [*] at hh
                          · have h72r := Ne.symm h72
                            by_cases h74 : w = t
                            · subst w
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                            · have h74r := Ne.symm h74
                              by_cases h75 : w = u
                              · subst w
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                              · have h75r := Ne.symm h75
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                      · have h60r := Ne.symm h60
                        by_cases h61 : v = q
                        · subst v
                          have h70 : w ≠ p := by omega
                          have h70r := Ne.symm h70
                          have h71 : w ≠ q := by omega
                          have h71r := Ne.symm h71
                          have h72 : w ≠ r := by omega
                          have h72r := Ne.symm h72
                          by_cases h74 : w = t
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h74r := Ne.symm h74
                            by_cases h75 : w = u
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h75r := Ne.symm h75
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                        · have h61r := Ne.symm h61
                          by_cases h62 : v = r
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar t
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                have h72 : w ≠ r := by omega
                                have h72r := Ne.symm h72
                                by_cases h74 : w = t
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h74r := Ne.symm h74
                                  by_cases h75 : w = u
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h75r := Ne.symm h75
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                          · have h62r := Ne.symm h62
                            by_cases h64 : v = t
                            · subst v
                              by_cases h70 : w = p
                              · subst w
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  by_cases h72 : w = r
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h72r := Ne.symm h72
                                    have h74 : w ≠ t := by omega
                                    have h74r := Ne.symm h74
                                    by_cases h75 : w = u
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h75r := Ne.symm h75
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                            · have h64r := Ne.symm h64
                              by_cases h65 : v = u
                              · subst v
                                by_cases h70 : w = p
                                · subst w
                                  have hh := hpar r
                                  clear hpar
                                  norm_num [*] at hh
                                · have h70r := Ne.symm h70
                                  by_cases h71 : w = q
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h71r := Ne.symm h71
                                    by_cases h72 : w = r
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h72r := Ne.symm h72
                                      have h74 : w ≠ t := by omega
                                      have h74r := Ne.symm h74
                                      have h75 : w ≠ u := by omega
                                      have h75r := Ne.symm h75
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                              · have h65r := Ne.symm h65
                                by_cases h70 : w = p
                                · subst w
                                  have hh := hpar r
                                  clear hpar
                                  norm_num [*] at hh
                                · have h70r := Ne.symm h70
                                  by_cases h71 : w = q
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h71r := Ne.symm h71
                                    by_cases h72 : w = r
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h72r := Ne.symm h72
                                      by_cases h74 : w = t
                                      · subst w
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h74r := Ne.symm h74
                                        by_cases h75 : w = u
                                        · subst w
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                        · have h75r := Ne.symm h75
                                          have h76 : w ≠ v := by omega
                                          have h76r := Ne.symm h76
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
        · have h31r := Ne.symm h31
          have h32 : s ≠ r := by omega
          have h32r := Ne.symm h32
          by_cases h40 : t = p
          · subst t
            have h50 : u ≠ p := by omega
            have h50r := Ne.symm h50
            by_cases h51 : u = q
            · subst u
              by_cases h60 : v = p
              · subst v
                have h70 : w ≠ p := by omega
                have h70r := Ne.symm h70
                by_cases h71 : w = q
                · subst w
                  have hh := hpar p
                  clear hpar
                  norm_num [*] at hh
                · have h71r := Ne.symm h71
                  by_cases h72 : w = r
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h72r := Ne.symm h72
                    by_cases h73 : w = s
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h73r := Ne.symm h73
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
              · have h60r := Ne.symm h60
                by_cases h61 : v = q
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  have h71 : w ≠ q := by omega
                  have h71r := Ne.symm h71
                  by_cases h72 : w = r
                  · subst w
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h72r := Ne.symm h72
                    by_cases h73 : w = s
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h73r := Ne.symm h73
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                · have h61r := Ne.symm h61
                  by_cases h62 : v = r
                  · subst v
                    by_cases h70 : w = p
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        by_cases h73 : w = s
                        · subst w
                          exact Or.inl (by ring)
                        · have h73r := Ne.symm h73
                          have hh := hpar s
                          clear hpar
                          norm_num [*] at hh
                  · have h62r := Ne.symm h62
                    by_cases h63 : v = s
                    · subst v
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          have h72 : w ≠ r := by omega
                          have h72r := Ne.symm h72
                          have h73 : w ≠ s := by omega
                          have h73r := Ne.symm h73
                          have hh := hpar r
                          clear hpar
                          norm_num [*] at hh
                    · have h63r := Ne.symm h63
                      by_cases h70 : w = p
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
                          · have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              have h76 : w ≠ v := by omega
                              have h76r := Ne.symm h76
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
            · have h51r := Ne.symm h51
              by_cases h52 : u = r
              · subst u
                by_cases h60 : v = p
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    have hh := hpar p
                    clear hpar
                    norm_num [*] at hh
                  · have h71r := Ne.symm h71
                    by_cases h72 : w = r
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h72r := Ne.symm h72
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                · have h60r := Ne.symm h60
                  by_cases h61 : v = q
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    have h71 : w ≠ q := by omega
                    have h71r := Ne.symm h71
                    by_cases h72 : w = r
                    · subst w
                      have hh := hpar r
                      clear hpar
                      norm_num [*] at hh
                    · have h72r := Ne.symm h72
                      by_cases h73 : w = s
                      · subst w
                        exact Or.inl (by ring)
                      · have h73r := Ne.symm h73
                        have hh := hpar s
                        clear hpar
                        norm_num [*] at hh
                  · have h61r := Ne.symm h61
                    by_cases h62 : v = r
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar r
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                    · have h62r := Ne.symm h62
                      by_cases h63 : v = s
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          exact Or.inl (by ring)
                        · have h71r := Ne.symm h71
                          have h72 : w ≠ r := by omega
                          have h72r := Ne.symm h72
                          have h73 : w ≠ s := by omega
                          have h73r := Ne.symm h73
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                      · have h63r := Ne.symm h63
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            by_cases h72 : w = r
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h72r := Ne.symm h72
                              by_cases h73 : w = s
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h73r := Ne.symm h73
                                have h76 : w ≠ v := by omega
                                have h76r := Ne.symm h76
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
              · have h52r := Ne.symm h52
                by_cases h53 : u = s
                · subst u
                  by_cases h60 : v = p
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h72 : w = r
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h72r := Ne.symm h72
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                  · have h60r := Ne.symm h60
                    by_cases h61 : v = q
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      by_cases h72 : w = r
                      · subst w
                        exact Or.inl (by ring)
                      · have h72r := Ne.symm h72
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar r
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          have hh := hpar r
                          clear hpar
                          norm_num [*] at hh
                    · have h61r := Ne.symm h61
                      by_cases h62 : v = r
                      · subst v
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            exact Or.inl (by ring)
                          · have h71r := Ne.symm h71
                            have h72 : w ≠ r := by omega
                            have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                      · have h62r := Ne.symm h62
                        by_cases h63 : v = s
                        · subst v
                          have h70 : w ≠ p := by omega
                          have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            have h72 : w ≠ r := by omega
                            have h72r := Ne.symm h72
                            have h73 : w ≠ s := by omega
                            have h73r := Ne.symm h73
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                        · have h63r := Ne.symm h63
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h72 : w = r
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h72r := Ne.symm h72
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  have h76 : w ≠ v := by omega
                                  have h76r := Ne.symm h76
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                · have h53r := Ne.symm h53
                  by_cases h60 : v = p
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h72 : w = r
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h72r := Ne.symm h72
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                  · have h60r := Ne.symm h60
                    by_cases h61 : v = q
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      by_cases h72 : w = r
                      · subst w
                        have hh := hpar s
                        clear hpar
                        norm_num [*] at hh
                      · have h72r := Ne.symm h72
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar r
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                    · have h61r := Ne.symm h61
                      by_cases h62 : v = r
                      · subst v
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            have h72 : w ≠ r := by omega
                            have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              by_cases h75 : w = u
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h75r := Ne.symm h75
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                      · have h62r := Ne.symm h62
                        by_cases h63 : v = s
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              have h72 : w ≠ r := by omega
                              have h72r := Ne.symm h72
                              have h73 : w ≠ s := by omega
                              have h73r := Ne.symm h73
                              by_cases h75 : w = u
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h75r := Ne.symm h75
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                        · have h63r := Ne.symm h63
                          by_cases h65 : v = u
                          · subst v
                            have h70 : w ≠ p := by omega
                            have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h72 : w = r
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h72r := Ne.symm h72
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  have h75 : w ≠ u := by omega
                                  have h75r := Ne.symm h75
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                          · have h65r := Ne.symm h65
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                by_cases h72 : w = r
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h72r := Ne.symm h72
                                  by_cases h73 : w = s
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h73r := Ne.symm h73
                                    by_cases h75 : w = u
                                    · subst w
                                      have hh := hpar q
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h75r := Ne.symm h75
                                      have h76 : w ≠ v := by omega
                                      have h76r := Ne.symm h76
                                      have hh := hpar q
                                      clear hpar
                                      norm_num [*] at hh
          · have h40r := Ne.symm h40
            by_cases h41 : t = q
            · subst t
              have h50 : u ≠ p := by omega
              have h50r := Ne.symm h50
              have h51 : u ≠ q := by omega
              have h51r := Ne.symm h51
              by_cases h52 : u = r
              · subst u
                by_cases h60 : v = p
                · subst v
                  have h70 : w ≠ p := by omega
                  have h70r := Ne.symm h70
                  by_cases h71 : w = q
                  · subst w
                    have hh := hpar q
                    clear hpar
                    norm_num [*] at hh
                  · have h71r := Ne.symm h71
                    by_cases h72 : w = r
                    · subst w
                      have hh := hpar r
                      clear hpar
                      norm_num [*] at hh
                    · have h72r := Ne.symm h72
                      by_cases h73 : w = s
                      · subst w
                        exact Or.inl (by ring)
                      · have h73r := Ne.symm h73
                        have hh := hpar s
                        clear hpar
                        norm_num [*] at hh
                · have h60r := Ne.symm h60
                  by_cases h61 : v = q
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    have h71 : w ≠ q := by omega
                    have h71r := Ne.symm h71
                    by_cases h72 : w = r
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h72r := Ne.symm h72
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                  · have h61r := Ne.symm h61
                    by_cases h62 : v = r
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                    · have h62r := Ne.symm h62
                      by_cases h63 : v = s
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        have h71 : w ≠ q := by omega
                        have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        have h73 : w ≠ s := by omega
                        have h73r := Ne.symm h73
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h63r := Ne.symm h63
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar s
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            by_cases h72 : w = r
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h72r := Ne.symm h72
                              by_cases h73 : w = s
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h73r := Ne.symm h73
                                have h76 : w ≠ v := by omega
                                have h76r := Ne.symm h76
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
              · have h52r := Ne.symm h52
                by_cases h53 : u = s
                · subst u
                  by_cases h60 : v = p
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h72 : w = r
                      · subst w
                        exact Or.inl (by ring)
                      · have h72r := Ne.symm h72
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar r
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          have hh := hpar r
                          clear hpar
                          norm_num [*] at hh
                  · have h60r := Ne.symm h60
                    by_cases h61 : v = q
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      by_cases h72 : w = r
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h72r := Ne.symm h72
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                    · have h61r := Ne.symm h61
                      by_cases h62 : v = r
                      · subst v
                        by_cases h70 : w = p
                        · subst w
                          exact Or.inl (by ring)
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            have h72 : w ≠ r := by omega
                            have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                      · have h62r := Ne.symm h62
                        by_cases h63 : v = s
                        · subst v
                          have h70 : w ≠ p := by omega
                          have h70r := Ne.symm h70
                          have h71 : w ≠ q := by omega
                          have h71r := Ne.symm h71
                          have h72 : w ≠ r := by omega
                          have h72r := Ne.symm h72
                          have h73 : w ≠ s := by omega
                          have h73r := Ne.symm h73
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h63r := Ne.symm h63
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h72 : w = r
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h72r := Ne.symm h72
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  have h76 : w ≠ v := by omega
                                  have h76r := Ne.symm h76
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                · have h53r := Ne.symm h53
                  by_cases h60 : v = p
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar q
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      by_cases h72 : w = r
                      · subst w
                        have hh := hpar s
                        clear hpar
                        norm_num [*] at hh
                      · have h72r := Ne.symm h72
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar r
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                  · have h60r := Ne.symm h60
                    by_cases h61 : v = q
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      by_cases h72 : w = r
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h72r := Ne.symm h72
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          by_cases h75 : w = u
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h75r := Ne.symm h75
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                    · have h61r := Ne.symm h61
                      by_cases h62 : v = r
                      · subst v
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar s
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            have h72 : w ≠ r := by omega
                            have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              by_cases h75 : w = u
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h75r := Ne.symm h75
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                      · have h62r := Ne.symm h62
                        by_cases h63 : v = s
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              have h72 : w ≠ r := by omega
                              have h72r := Ne.symm h72
                              have h73 : w ≠ s := by omega
                              have h73r := Ne.symm h73
                              by_cases h75 : w = u
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h75r := Ne.symm h75
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                        · have h63r := Ne.symm h63
                          by_cases h65 : v = u
                          · subst v
                            have h70 : w ≠ p := by omega
                            have h70r := Ne.symm h70
                            have h71 : w ≠ q := by omega
                            have h71r := Ne.symm h71
                            by_cases h72 : w = r
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h72r := Ne.symm h72
                              by_cases h73 : w = s
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h73r := Ne.symm h73
                                have h75 : w ≠ u := by omega
                                have h75r := Ne.symm h75
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                          · have h65r := Ne.symm h65
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                by_cases h72 : w = r
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h72r := Ne.symm h72
                                  by_cases h73 : w = s
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h73r := Ne.symm h73
                                    by_cases h75 : w = u
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h75r := Ne.symm h75
                                      have h76 : w ≠ v := by omega
                                      have h76r := Ne.symm h76
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
            · have h41r := Ne.symm h41
              by_cases h42 : t = r
              · subst t
                by_cases h50 : u = p
                · subst u
                  by_cases h60 : v = p
                  · subst v
                    have h70 : w ≠ p := by omega
                    have h70r := Ne.symm h70
                    by_cases h71 : w = q
                    · subst w
                      have hh := hpar p
                      clear hpar
                      norm_num [*] at hh
                    · have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      by_cases h73 : w = s
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h73r := Ne.symm h73
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                  · have h60r := Ne.symm h60
                    by_cases h61 : v = q
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      have h71 : w ≠ q := by omega
                      have h71r := Ne.symm h71
                      have h72 : w ≠ r := by omega
                      have h72r := Ne.symm h72
                      by_cases h73 : w = s
                      · subst w
                        exact Or.inl (by ring)
                      · have h73r := Ne.symm h73
                        have hh := hpar s
                        clear hpar
                        norm_num [*] at hh
                    · have h61r := Ne.symm h61
                      by_cases h62 : v = r
                      · subst v
                        by_cases h70 : w = p
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            have h72 : w ≠ r := by omega
                            have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                      · have h62r := Ne.symm h62
                        by_cases h63 : v = s
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              exact Or.inl (by ring)
                            · have h71r := Ne.symm h71
                              have h72 : w ≠ r := by omega
                              have h72r := Ne.symm h72
                              have h73 : w ≠ s := by omega
                              have h73r := Ne.symm h73
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                        · have h63r := Ne.symm h63
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar s
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h72 : w = r
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h72r := Ne.symm h72
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  have h76 : w ≠ v := by omega
                                  have h76r := Ne.symm h76
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                · have h50r := Ne.symm h50
                  by_cases h51 : u = q
                  · subst u
                    by_cases h60 : v = p
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar q
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        by_cases h72 : w = r
                        · subst w
                          have hh := hpar r
                          clear hpar
                          norm_num [*] at hh
                        · have h72r := Ne.symm h72
                          by_cases h73 : w = s
                          · subst w
                            exact Or.inl (by ring)
                          · have h73r := Ne.symm h73
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
                    · have h60r := Ne.symm h60
                      by_cases h61 : v = q
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        have h71 : w ≠ q := by omega
                        have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        by_cases h73 : w = s
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h73r := Ne.symm h73
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                      · have h61r := Ne.symm h61
                        by_cases h62 : v = r
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              have h72 : w ≠ r := by omega
                              have h72r := Ne.symm h72
                              by_cases h73 : w = s
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h73r := Ne.symm h73
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                        · have h62r := Ne.symm h62
                          by_cases h63 : v = s
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              exact Or.inl (by ring)
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                have h72 : w ≠ r := by omega
                                have h72r := Ne.symm h72
                                have h73 : w ≠ s := by omega
                                have h73r := Ne.symm h73
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                          · have h63r := Ne.symm h63
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar s
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                by_cases h72 : w = r
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h72r := Ne.symm h72
                                  by_cases h73 : w = s
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h73r := Ne.symm h73
                                    have h76 : w ≠ v := by omega
                                    have h76r := Ne.symm h76
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                  · have h51r := Ne.symm h51
                    have h52 : u ≠ r := by omega
                    have h52r := Ne.symm h52
                    by_cases h53 : u = s
                    · subst u
                      by_cases h60 : v = p
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          exact Or.inl (by ring)
                        · have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                      · have h60r := Ne.symm h60
                        by_cases h61 : v = q
                        · subst v
                          have h70 : w ≠ p := by omega
                          have h70r := Ne.symm h70
                          have h71 : w ≠ q := by omega
                          have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                        · have h61r := Ne.symm h61
                          by_cases h62 : v = r
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                have h72 : w ≠ r := by omega
                                have h72r := Ne.symm h72
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                          · have h62r := Ne.symm h62
                            by_cases h63 : v = s
                            · subst v
                              by_cases h70 : w = p
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  have h72 : w ≠ r := by omega
                                  have h72r := Ne.symm h72
                                  have h73 : w ≠ s := by omega
                                  have h73r := Ne.symm h73
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                            · have h63r := Ne.symm h63
                              by_cases h70 : w = p
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  by_cases h72 : w = r
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h72r := Ne.symm h72
                                    by_cases h73 : w = s
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h73r := Ne.symm h73
                                      have h76 : w ≠ v := by omega
                                      have h76r := Ne.symm h76
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                    · have h53r := Ne.symm h53
                      by_cases h60 : v = p
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar s
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              by_cases h75 : w = u
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h75r := Ne.symm h75
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                      · have h60r := Ne.symm h60
                        by_cases h61 : v = q
                        · subst v
                          have h70 : w ≠ p := by omega
                          have h70r := Ne.symm h70
                          have h71 : w ≠ q := by omega
                          have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              by_cases h75 : w = u
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h75r := Ne.symm h75
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                        · have h61r := Ne.symm h61
                          by_cases h62 : v = r
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                have h72 : w ≠ r := by omega
                                have h72r := Ne.symm h72
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  by_cases h75 : w = u
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h75r := Ne.symm h75
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                          · have h62r := Ne.symm h62
                            by_cases h63 : v = s
                            · subst v
                              by_cases h70 : w = p
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  have h72 : w ≠ r := by omega
                                  have h72r := Ne.symm h72
                                  have h73 : w ≠ s := by omega
                                  have h73r := Ne.symm h73
                                  by_cases h75 : w = u
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h75r := Ne.symm h75
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                            · have h63r := Ne.symm h63
                              by_cases h65 : v = u
                              · subst v
                                by_cases h70 : w = p
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h70r := Ne.symm h70
                                  by_cases h71 : w = q
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h71r := Ne.symm h71
                                    have h72 : w ≠ r := by omega
                                    have h72r := Ne.symm h72
                                    by_cases h73 : w = s
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h73r := Ne.symm h73
                                      have h75 : w ≠ u := by omega
                                      have h75r := Ne.symm h75
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                              · have h65r := Ne.symm h65
                                by_cases h70 : w = p
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h70r := Ne.symm h70
                                  by_cases h71 : w = q
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h71r := Ne.symm h71
                                    by_cases h72 : w = r
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h72r := Ne.symm h72
                                      by_cases h73 : w = s
                                      · subst w
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h73r := Ne.symm h73
                                        by_cases h75 : w = u
                                        · subst w
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                        · have h75r := Ne.symm h75
                                          have h76 : w ≠ v := by omega
                                          have h76r := Ne.symm h76
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
              · have h42r := Ne.symm h42
                by_cases h43 : t = s
                · subst t
                  by_cases h50 : u = p
                  · subst u
                    by_cases h60 : v = p
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        have h73 : w ≠ s := by omega
                        have h73r := Ne.symm h73
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                    · have h60r := Ne.symm h60
                      by_cases h61 : v = q
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        have h71 : w ≠ q := by omega
                        have h71r := Ne.symm h71
                        have h72 : w ≠ r := by omega
                        have h72r := Ne.symm h72
                        have h73 : w ≠ s := by omega
                        have h73r := Ne.symm h73
                        have hh := hpar r
                        clear hpar
                        norm_num [*] at hh
                      · have h61r := Ne.symm h61
                        by_cases h62 : v = r
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              exact Or.inl (by ring)
                            · have h71r := Ne.symm h71
                              have h72 : w ≠ r := by omega
                              have h72r := Ne.symm h72
                              by_cases h73 : w = s
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h73r := Ne.symm h73
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                        · have h62r := Ne.symm h62
                          by_cases h63 : v = s
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                have h72 : w ≠ r := by omega
                                have h72r := Ne.symm h72
                                have h73 : w ≠ s := by omega
                                have h73r := Ne.symm h73
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                          · have h63r := Ne.symm h63
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                by_cases h72 : w = r
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h72r := Ne.symm h72
                                  by_cases h73 : w = s
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h73r := Ne.symm h73
                                    have h76 : w ≠ v := by omega
                                    have h76r := Ne.symm h76
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                  · have h50r := Ne.symm h50
                    by_cases h51 : u = q
                    · subst u
                      by_cases h60 : v = p
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            exact Or.inl (by ring)
                          · have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                      · have h60r := Ne.symm h60
                        by_cases h61 : v = q
                        · subst v
                          have h70 : w ≠ p := by omega
                          have h70r := Ne.symm h70
                          have h71 : w ≠ q := by omega
                          have h71r := Ne.symm h71
                          have h72 : w ≠ r := by omega
                          have h72r := Ne.symm h72
                          have h73 : w ≠ s := by omega
                          have h73r := Ne.symm h73
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h61r := Ne.symm h61
                          by_cases h62 : v = r
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              exact Or.inl (by ring)
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                have h72 : w ≠ r := by omega
                                have h72r := Ne.symm h72
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                          · have h62r := Ne.symm h62
                            by_cases h63 : v = s
                            · subst v
                              by_cases h70 : w = p
                              · subst w
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  have h72 : w ≠ r := by omega
                                  have h72r := Ne.symm h72
                                  have h73 : w ≠ s := by omega
                                  have h73r := Ne.symm h73
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                            · have h63r := Ne.symm h63
                              by_cases h70 : w = p
                              · subst w
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  by_cases h72 : w = r
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h72r := Ne.symm h72
                                    by_cases h73 : w = s
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h73r := Ne.symm h73
                                      have h76 : w ≠ v := by omega
                                      have h76r := Ne.symm h76
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                    · have h51r := Ne.symm h51
                      have h52 : u ≠ r := by omega
                      have h52r := Ne.symm h52
                      have h53 : u ≠ s := by omega
                      have h53r := Ne.symm h53
                      by_cases h60 : v = p
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar r
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            have hh := hpar q
                            clear hpar
                            norm_num [*] at hh
                          · have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              by_cases h75 : w = u
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h75r := Ne.symm h75
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                      · have h60r := Ne.symm h60
                        by_cases h61 : v = q
                        · subst v
                          have h70 : w ≠ p := by omega
                          have h70r := Ne.symm h70
                          have h71 : w ≠ q := by omega
                          have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              by_cases h75 : w = u
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h75r := Ne.symm h75
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                        · have h61r := Ne.symm h61
                          by_cases h62 : v = r
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                have h72 : w ≠ r := by omega
                                have h72r := Ne.symm h72
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  by_cases h75 : w = u
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h75r := Ne.symm h75
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                          · have h62r := Ne.symm h62
                            by_cases h63 : v = s
                            · subst v
                              by_cases h70 : w = p
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  have h72 : w ≠ r := by omega
                                  have h72r := Ne.symm h72
                                  have h73 : w ≠ s := by omega
                                  have h73r := Ne.symm h73
                                  by_cases h75 : w = u
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h75r := Ne.symm h75
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                            · have h63r := Ne.symm h63
                              by_cases h65 : v = u
                              · subst v
                                by_cases h70 : w = p
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h70r := Ne.symm h70
                                  by_cases h71 : w = q
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h71r := Ne.symm h71
                                    have h72 : w ≠ r := by omega
                                    have h72r := Ne.symm h72
                                    have h73 : w ≠ s := by omega
                                    have h73r := Ne.symm h73
                                    have h75 : w ≠ u := by omega
                                    have h75r := Ne.symm h75
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                              · have h65r := Ne.symm h65
                                by_cases h70 : w = p
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h70r := Ne.symm h70
                                  by_cases h71 : w = q
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h71r := Ne.symm h71
                                    by_cases h72 : w = r
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h72r := Ne.symm h72
                                      by_cases h73 : w = s
                                      · subst w
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h73r := Ne.symm h73
                                        by_cases h75 : w = u
                                        · subst w
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                        · have h75r := Ne.symm h75
                                          have h76 : w ≠ v := by omega
                                          have h76r := Ne.symm h76
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                · have h43r := Ne.symm h43
                  by_cases h50 : u = p
                  · subst u
                    by_cases h60 : v = p
                    · subst v
                      have h70 : w ≠ p := by omega
                      have h70r := Ne.symm h70
                      by_cases h71 : w = q
                      · subst w
                        have hh := hpar p
                        clear hpar
                        norm_num [*] at hh
                      · have h71r := Ne.symm h71
                        by_cases h72 : w = r
                        · subst w
                          have hh := hpar p
                          clear hpar
                          norm_num [*] at hh
                        · have h72r := Ne.symm h72
                          by_cases h73 : w = s
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h73r := Ne.symm h73
                            have h74 : w ≠ t := by omega
                            have h74r := Ne.symm h74
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                    · have h60r := Ne.symm h60
                      by_cases h61 : v = q
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        have h71 : w ≠ q := by omega
                        have h71r := Ne.symm h71
                        by_cases h72 : w = r
                        · subst w
                          have hh := hpar s
                          clear hpar
                          norm_num [*] at hh
                        · have h72r := Ne.symm h72
                          by_cases h73 : w = s
                          · subst w
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                          · have h73r := Ne.symm h73
                            have h74 : w ≠ t := by omega
                            have h74r := Ne.symm h74
                            have hh := hpar r
                            clear hpar
                            norm_num [*] at hh
                      · have h61r := Ne.symm h61
                        by_cases h62 : v = r
                        · subst v
                          by_cases h70 : w = p
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar s
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              have h72 : w ≠ r := by omega
                              have h72r := Ne.symm h72
                              by_cases h73 : w = s
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h73r := Ne.symm h73
                                by_cases h74 : w = t
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h74r := Ne.symm h74
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                        · have h62r := Ne.symm h62
                          by_cases h63 : v = s
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                have h72 : w ≠ r := by omega
                                have h72r := Ne.symm h72
                                have h73 : w ≠ s := by omega
                                have h73r := Ne.symm h73
                                by_cases h74 : w = t
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h74r := Ne.symm h74
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                          · have h63r := Ne.symm h63
                            by_cases h64 : v = t
                            · subst v
                              by_cases h70 : w = p
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar r
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  by_cases h72 : w = r
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h72r := Ne.symm h72
                                    by_cases h73 : w = s
                                    · subst w
                                      have hh := hpar q
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h73r := Ne.symm h73
                                      have h74 : w ≠ t := by omega
                                      have h74r := Ne.symm h74
                                      have hh := hpar q
                                      clear hpar
                                      norm_num [*] at hh
                            · have h64r := Ne.symm h64
                              by_cases h70 : w = p
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar r
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  by_cases h72 : w = r
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h72r := Ne.symm h72
                                    by_cases h73 : w = s
                                    · subst w
                                      have hh := hpar q
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h73r := Ne.symm h73
                                      by_cases h74 : w = t
                                      · subst w
                                        have hh := hpar q
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h74r := Ne.symm h74
                                        have h76 : w ≠ v := by omega
                                        have h76r := Ne.symm h76
                                        have hh := hpar q
                                        clear hpar
                                        norm_num [*] at hh
                  · have h50r := Ne.symm h50
                    by_cases h51 : u = q
                    · subst u
                      by_cases h60 : v = p
                      · subst v
                        have h70 : w ≠ p := by omega
                        have h70r := Ne.symm h70
                        by_cases h71 : w = q
                        · subst w
                          have hh := hpar q
                          clear hpar
                          norm_num [*] at hh
                        · have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
                          · have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              by_cases h74 : w = t
                              · subst w
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                              · have h74r := Ne.symm h74
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                      · have h60r := Ne.symm h60
                        by_cases h61 : v = q
                        · subst v
                          have h70 : w ≠ p := by omega
                          have h70r := Ne.symm h70
                          have h71 : w ≠ q := by omega
                          have h71r := Ne.symm h71
                          by_cases h72 : w = r
                          · subst w
                            have hh := hpar p
                            clear hpar
                            norm_num [*] at hh
                          · have h72r := Ne.symm h72
                            by_cases h73 : w = s
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h73r := Ne.symm h73
                              have h74 : w ≠ t := by omega
                              have h74r := Ne.symm h74
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                        · have h61r := Ne.symm h61
                          by_cases h62 : v = r
                          · subst v
                            by_cases h70 : w = p
                            · subst w
                              have hh := hpar s
                              clear hpar
                              norm_num [*] at hh
                            · have h70r := Ne.symm h70
                              by_cases h71 : w = q
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h71r := Ne.symm h71
                                have h72 : w ≠ r := by omega
                                have h72r := Ne.symm h72
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  by_cases h74 : w = t
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h74r := Ne.symm h74
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                          · have h62r := Ne.symm h62
                            by_cases h63 : v = s
                            · subst v
                              by_cases h70 : w = p
                              · subst w
                                have hh := hpar r
                                clear hpar
                                norm_num [*] at hh
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  have h72 : w ≠ r := by omega
                                  have h72r := Ne.symm h72
                                  have h73 : w ≠ s := by omega
                                  have h73r := Ne.symm h73
                                  by_cases h74 : w = t
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h74r := Ne.symm h74
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                            · have h63r := Ne.symm h63
                              by_cases h64 : v = t
                              · subst v
                                by_cases h70 : w = p
                                · subst w
                                  have hh := hpar r
                                  clear hpar
                                  norm_num [*] at hh
                                · have h70r := Ne.symm h70
                                  by_cases h71 : w = q
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h71r := Ne.symm h71
                                    by_cases h72 : w = r
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h72r := Ne.symm h72
                                      by_cases h73 : w = s
                                      · subst w
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h73r := Ne.symm h73
                                        have h74 : w ≠ t := by omega
                                        have h74r := Ne.symm h74
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                              · have h64r := Ne.symm h64
                                by_cases h70 : w = p
                                · subst w
                                  have hh := hpar r
                                  clear hpar
                                  norm_num [*] at hh
                                · have h70r := Ne.symm h70
                                  by_cases h71 : w = q
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h71r := Ne.symm h71
                                    by_cases h72 : w = r
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h72r := Ne.symm h72
                                      by_cases h73 : w = s
                                      · subst w
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h73r := Ne.symm h73
                                        by_cases h74 : w = t
                                        · subst w
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                        · have h74r := Ne.symm h74
                                          have h76 : w ≠ v := by omega
                                          have h76r := Ne.symm h76
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                    · have h51r := Ne.symm h51
                      by_cases h52 : u = r
                      · subst u
                        by_cases h60 : v = p
                        · subst v
                          have h70 : w ≠ p := by omega
                          have h70r := Ne.symm h70
                          by_cases h71 : w = q
                          · subst w
                            have hh := hpar s
                            clear hpar
                            norm_num [*] at hh
                          · have h71r := Ne.symm h71
                            by_cases h72 : w = r
                            · subst w
                              have hh := hpar q
                              clear hpar
                              norm_num [*] at hh
                            · have h72r := Ne.symm h72
                              by_cases h73 : w = s
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h73r := Ne.symm h73
                                by_cases h74 : w = t
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h74r := Ne.symm h74
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                        · have h60r := Ne.symm h60
                          by_cases h61 : v = q
                          · subst v
                            have h70 : w ≠ p := by omega
                            have h70r := Ne.symm h70
                            have h71 : w ≠ q := by omega
                            have h71r := Ne.symm h71
                            by_cases h72 : w = r
                            · subst w
                              have hh := hpar p
                              clear hpar
                              norm_num [*] at hh
                            · have h72r := Ne.symm h72
                              by_cases h73 : w = s
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h73r := Ne.symm h73
                                by_cases h74 : w = t
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h74r := Ne.symm h74
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                          · have h61r := Ne.symm h61
                            by_cases h62 : v = r
                            · subst v
                              by_cases h70 : w = p
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h70r := Ne.symm h70
                                by_cases h71 : w = q
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h71r := Ne.symm h71
                                  have h72 : w ≠ r := by omega
                                  have h72r := Ne.symm h72
                                  by_cases h73 : w = s
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h73r := Ne.symm h73
                                    have h74 : w ≠ t := by omega
                                    have h74r := Ne.symm h74
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                            · have h62r := Ne.symm h62
                              by_cases h63 : v = s
                              · subst v
                                by_cases h70 : w = p
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h70r := Ne.symm h70
                                  by_cases h71 : w = q
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h71r := Ne.symm h71
                                    have h72 : w ≠ r := by omega
                                    have h72r := Ne.symm h72
                                    have h73 : w ≠ s := by omega
                                    have h73r := Ne.symm h73
                                    have h74 : w ≠ t := by omega
                                    have h74r := Ne.symm h74
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                              · have h63r := Ne.symm h63
                                by_cases h64 : v = t
                                · subst v
                                  by_cases h70 : w = p
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h70r := Ne.symm h70
                                    by_cases h71 : w = q
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h71r := Ne.symm h71
                                      by_cases h72 : w = r
                                      · subst w
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h72r := Ne.symm h72
                                        by_cases h73 : w = s
                                        · subst w
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                        · have h73r := Ne.symm h73
                                          have h74 : w ≠ t := by omega
                                          have h74r := Ne.symm h74
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                · have h64r := Ne.symm h64
                                  by_cases h70 : w = p
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h70r := Ne.symm h70
                                    by_cases h71 : w = q
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h71r := Ne.symm h71
                                      by_cases h72 : w = r
                                      · subst w
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h72r := Ne.symm h72
                                        by_cases h73 : w = s
                                        · subst w
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                        · have h73r := Ne.symm h73
                                          by_cases h74 : w = t
                                          · subst w
                                            have hh := hpar p
                                            clear hpar
                                            norm_num [*] at hh
                                          · have h74r := Ne.symm h74
                                            have h76 : w ≠ v := by omega
                                            have h76r := Ne.symm h76
                                            have hh := hpar p
                                            clear hpar
                                            norm_num [*] at hh
                      · have h52r := Ne.symm h52
                        by_cases h53 : u = s
                        · subst u
                          by_cases h60 : v = p
                          · subst v
                            have h70 : w ≠ p := by omega
                            have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h72 : w = r
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h72r := Ne.symm h72
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  by_cases h74 : w = t
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h74r := Ne.symm h74
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                          · have h60r := Ne.symm h60
                            by_cases h61 : v = q
                            · subst v
                              have h70 : w ≠ p := by omega
                              have h70r := Ne.symm h70
                              have h71 : w ≠ q := by omega
                              have h71r := Ne.symm h71
                              by_cases h72 : w = r
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h72r := Ne.symm h72
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  by_cases h74 : w = t
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h74r := Ne.symm h74
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                            · have h61r := Ne.symm h61
                              by_cases h62 : v = r
                              · subst v
                                by_cases h70 : w = p
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h70r := Ne.symm h70
                                  by_cases h71 : w = q
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h71r := Ne.symm h71
                                    have h72 : w ≠ r := by omega
                                    have h72r := Ne.symm h72
                                    by_cases h73 : w = s
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h73r := Ne.symm h73
                                      by_cases h74 : w = t
                                      · subst w
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h74r := Ne.symm h74
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                              · have h62r := Ne.symm h62
                                by_cases h63 : v = s
                                · subst v
                                  by_cases h70 : w = p
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h70r := Ne.symm h70
                                    by_cases h71 : w = q
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h71r := Ne.symm h71
                                      have h72 : w ≠ r := by omega
                                      have h72r := Ne.symm h72
                                      have h73 : w ≠ s := by omega
                                      have h73r := Ne.symm h73
                                      have h74 : w ≠ t := by omega
                                      have h74r := Ne.symm h74
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                · have h63r := Ne.symm h63
                                  by_cases h64 : v = t
                                  · subst v
                                    by_cases h70 : w = p
                                    · subst w
                                      have hh := hpar q
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h70r := Ne.symm h70
                                      by_cases h71 : w = q
                                      · subst w
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h71r := Ne.symm h71
                                        by_cases h72 : w = r
                                        · subst w
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                        · have h72r := Ne.symm h72
                                          by_cases h73 : w = s
                                          · subst w
                                            have hh := hpar p
                                            clear hpar
                                            norm_num [*] at hh
                                          · have h73r := Ne.symm h73
                                            have h74 : w ≠ t := by omega
                                            have h74r := Ne.symm h74
                                            have hh := hpar p
                                            clear hpar
                                            norm_num [*] at hh
                                  · have h64r := Ne.symm h64
                                    by_cases h70 : w = p
                                    · subst w
                                      have hh := hpar q
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h70r := Ne.symm h70
                                      by_cases h71 : w = q
                                      · subst w
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h71r := Ne.symm h71
                                        by_cases h72 : w = r
                                        · subst w
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                        · have h72r := Ne.symm h72
                                          by_cases h73 : w = s
                                          · subst w
                                            have hh := hpar p
                                            clear hpar
                                            norm_num [*] at hh
                                          · have h73r := Ne.symm h73
                                            by_cases h74 : w = t
                                            · subst w
                                              have hh := hpar p
                                              clear hpar
                                              norm_num [*] at hh
                                            · have h74r := Ne.symm h74
                                              have h76 : w ≠ v := by omega
                                              have h76r := Ne.symm h76
                                              have hh := hpar p
                                              clear hpar
                                              norm_num [*] at hh
                        · have h53r := Ne.symm h53
                          have h54 : u ≠ t := by omega
                          have h54r := Ne.symm h54
                          by_cases h60 : v = p
                          · subst v
                            have h70 : w ≠ p := by omega
                            have h70r := Ne.symm h70
                            by_cases h71 : w = q
                            · subst w
                              have hh := hpar r
                              clear hpar
                              norm_num [*] at hh
                            · have h71r := Ne.symm h71
                              by_cases h72 : w = r
                              · subst w
                                have hh := hpar q
                                clear hpar
                                norm_num [*] at hh
                              · have h72r := Ne.symm h72
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  by_cases h74 : w = t
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h74r := Ne.symm h74
                                    by_cases h75 : w = u
                                    · subst w
                                      have hh := hpar q
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h75r := Ne.symm h75
                                      have hh := hpar q
                                      clear hpar
                                      norm_num [*] at hh
                          · have h60r := Ne.symm h60
                            by_cases h61 : v = q
                            · subst v
                              have h70 : w ≠ p := by omega
                              have h70r := Ne.symm h70
                              have h71 : w ≠ q := by omega
                              have h71r := Ne.symm h71
                              by_cases h72 : w = r
                              · subst w
                                have hh := hpar p
                                clear hpar
                                norm_num [*] at hh
                              · have h72r := Ne.symm h72
                                by_cases h73 : w = s
                                · subst w
                                  have hh := hpar p
                                  clear hpar
                                  norm_num [*] at hh
                                · have h73r := Ne.symm h73
                                  by_cases h74 : w = t
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h74r := Ne.symm h74
                                    by_cases h75 : w = u
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h75r := Ne.symm h75
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                            · have h61r := Ne.symm h61
                              by_cases h62 : v = r
                              · subst v
                                by_cases h70 : w = p
                                · subst w
                                  have hh := hpar q
                                  clear hpar
                                  norm_num [*] at hh
                                · have h70r := Ne.symm h70
                                  by_cases h71 : w = q
                                  · subst w
                                    have hh := hpar p
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h71r := Ne.symm h71
                                    have h72 : w ≠ r := by omega
                                    have h72r := Ne.symm h72
                                    by_cases h73 : w = s
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h73r := Ne.symm h73
                                      by_cases h74 : w = t
                                      · subst w
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h74r := Ne.symm h74
                                        by_cases h75 : w = u
                                        · subst w
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                        · have h75r := Ne.symm h75
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                              · have h62r := Ne.symm h62
                                by_cases h63 : v = s
                                · subst v
                                  by_cases h70 : w = p
                                  · subst w
                                    have hh := hpar q
                                    clear hpar
                                    norm_num [*] at hh
                                  · have h70r := Ne.symm h70
                                    by_cases h71 : w = q
                                    · subst w
                                      have hh := hpar p
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h71r := Ne.symm h71
                                      have h72 : w ≠ r := by omega
                                      have h72r := Ne.symm h72
                                      have h73 : w ≠ s := by omega
                                      have h73r := Ne.symm h73
                                      by_cases h74 : w = t
                                      · subst w
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h74r := Ne.symm h74
                                        by_cases h75 : w = u
                                        · subst w
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                        · have h75r := Ne.symm h75
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                · have h63r := Ne.symm h63
                                  by_cases h64 : v = t
                                  · subst v
                                    by_cases h70 : w = p
                                    · subst w
                                      have hh := hpar q
                                      clear hpar
                                      norm_num [*] at hh
                                    · have h70r := Ne.symm h70
                                      by_cases h71 : w = q
                                      · subst w
                                        have hh := hpar p
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h71r := Ne.symm h71
                                        by_cases h72 : w = r
                                        · subst w
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                        · have h72r := Ne.symm h72
                                          by_cases h73 : w = s
                                          · subst w
                                            have hh := hpar p
                                            clear hpar
                                            norm_num [*] at hh
                                          · have h73r := Ne.symm h73
                                            have h74 : w ≠ t := by omega
                                            have h74r := Ne.symm h74
                                            by_cases h75 : w = u
                                            · subst w
                                              have hh := hpar p
                                              clear hpar
                                              norm_num [*] at hh
                                            · have h75r := Ne.symm h75
                                              have hh := hpar p
                                              clear hpar
                                              norm_num [*] at hh
                                  · have h64r := Ne.symm h64
                                    by_cases h65 : v = u
                                    · subst v
                                      by_cases h70 : w = p
                                      · subst w
                                        have hh := hpar q
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h70r := Ne.symm h70
                                        by_cases h71 : w = q
                                        · subst w
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                        · have h71r := Ne.symm h71
                                          by_cases h72 : w = r
                                          · subst w
                                            have hh := hpar p
                                            clear hpar
                                            norm_num [*] at hh
                                          · have h72r := Ne.symm h72
                                            by_cases h73 : w = s
                                            · subst w
                                              have hh := hpar p
                                              clear hpar
                                              norm_num [*] at hh
                                            · have h73r := Ne.symm h73
                                              have h74 : w ≠ t := by omega
                                              have h74r := Ne.symm h74
                                              have h75 : w ≠ u := by omega
                                              have h75r := Ne.symm h75
                                              have hh := hpar p
                                              clear hpar
                                              norm_num [*] at hh
                                    · have h65r := Ne.symm h65
                                      by_cases h70 : w = p
                                      · subst w
                                        have hh := hpar q
                                        clear hpar
                                        norm_num [*] at hh
                                      · have h70r := Ne.symm h70
                                        by_cases h71 : w = q
                                        · subst w
                                          have hh := hpar p
                                          clear hpar
                                          norm_num [*] at hh
                                        · have h71r := Ne.symm h71
                                          by_cases h72 : w = r
                                          · subst w
                                            have hh := hpar p
                                            clear hpar
                                            norm_num [*] at hh
                                          · have h72r := Ne.symm h72
                                            by_cases h73 : w = s
                                            · subst w
                                              have hh := hpar p
                                              clear hpar
                                              norm_num [*] at hh
                                            · have h73r := Ne.symm h73
                                              by_cases h74 : w = t
                                              · subst w
                                                have hh := hpar p
                                                clear hpar
                                                norm_num [*] at hh
                                              · have h74r := Ne.symm h74
                                                by_cases h75 : w = u
                                                · subst w
                                                  have hh := hpar p
                                                  clear hpar
                                                  norm_num [*] at hh
                                                · have h75r := Ne.symm h75
                                                  have h76 : w ≠ v := by omega
                                                  have h76r := Ne.symm h76
                                                  have hh := hpar p
                                                  clear hpar
                                                  norm_num [*] at hh

end OMA.SemiprimeSquare

-- Step Erdos888.erdos_888.variants.semiprimes.R1.H2: hypothesis H2 of reduction Erdos888.erdos_888.variants.semiprimes.R1
-- Credit: @DeepDuke
-- H2 := ∀ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ : ℕ,     p₁.Prime → q₁.Prime → p₁ < q₁ → p₂.Prime → q₂.Prime → p₂ < q₂ →     p₃.Prime → q₃.Prime → p₃ < q₃ → p₄.Prime → q₄.Prime → p₄ < q₄ →     p₁ * q₁ ≤ p₂ * q₂ → p₂ * q₂ ≤ p₃ * q₃ → p₃ * q₃ ≤ p₄ * q₄ →     IsSquare (p₁ * q₁ * (p₂ * q₂) * (p₃ * q₃) * (p₄ * q₄)) →     p₁ * q₁ * (p₄ * q₄) = p₂ * q₂ * (p₃ * q₃)

theorem OMA.solution : OMA.R_Erdos888_erdos_888_variants_semiprimes_R1.H2 := by
  intro p q r s t u v w hp hq hpq hr hs hrs ht hu htu hv hw hvw hab hbc hcd hsq
  exact OMA.SemiprimeSquare.ordered (p*q) (r*s) (t*u) (v*w)
    (Nat.mul_pos hp.pos hq.pos) (Nat.mul_pos hr.pos hs.pos) (Nat.mul_pos ht.pos hu.pos)
    hab hbc hcd (OMA.SemiprimeSquare.pairing p q r s t u v w
      hp hq hr hs ht hu hv hw hpq hrs htu hvw hsq)

