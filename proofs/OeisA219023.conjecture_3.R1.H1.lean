import OMAReductions.R_OeisA219023_conjecture_3_R1
import Mathlib

def OMA.np (q : ℕ) : ℕ → Bool
  | 0 => true
  | d + 1 => (q % (d + 1) != 0 || decide (q ≤ d + 1) || d == 0) && OMA.np q d

theorem OMA.np_spec (q : ℕ) : ∀ d, OMA.np q d = true → ∀ m, 2 ≤ m → m ≤ d → m < q → ¬ m ∣ q := by
  intro d
  induction d with
  | zero => intro _ m h2 hm; omega
  | succ d ih =>
    intro h m h2 hm hq hdvd
    simp only [OMA.np, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq,
      beq_iff_eq, ne_eq] at h
    obtain ⟨h1, h3⟩ := h
    rcases Nat.lt_or_eq_of_le hm with hlt | rfl
    · exact ih h3 m h2 (by omega) hq hdvd
    · have := Nat.mod_eq_zero_of_dvd hdvd
      omega

theorem OMA.pr_prime (q r : ℕ) (h : 2 ≤ q ∧ q < (r + 1) * (r + 1) ∧ OMA.np q r = true) :
    q.Prime := by
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h.1, fun m h2 hm => OMA.np_spec q r h.2.2 m h2 ?_ ?_⟩
  · have : Nat.sqrt q < r + 1 := Nat.sqrt_lt.2 h.2.1
    omega
  · have := Nat.sqrt_lt_self (by omega : 1 < q)
    omega

def OMA.pb (q r : ℕ) : Bool := decide (2 ≤ q) && decide (q < (r + 1) * (r + 1)) && OMA.np q r

theorem OMA.pb_prime {q r : ℕ} (h : OMA.pb q r = true) : q.Prime := by
  simp only [OMA.pb, Bool.and_eq_true, decide_eq_true_eq] at h
  exact OMA.pr_prime q r ⟨h.1.1, h.1.2, h.2⟩

set_option maxRecDepth 1000000 in
def OMA.T : List ℕ := [
7491855,7495789,7499877,7503915,7507985,7512165,7516173,7520287,7524483,7529025,7532917,7536891,
7541007,7544873,7549107,7553085,7557131,7561245,7565595,7569535,7573683,7577673,7581785,7586055,
7589895,7594043,7598103,7602933,7606313,7610373,7614543,7618751,7623333,7627023,7631087,7635405,
7639101,7643153,7648515,7651395,7655467,7659549,7663725,7667785,7672857,7677285,7680073,7684125,
7688205,7692515,7696395,7700763,7704977,7708743,7713075,7717223,7721091,7725165,7729343,7733277,
7737483,7741511,7745727,7749903,7753733,7757835,7762077,7766075,7770213,7774785,7778365,7782447,
7786503,7791205,7794735,7798845,7802903,7807023,7811595,7815247,7819293,7823517,7827535,7831575,
7835667,7839805,7844187,7848003,7852045,7856145,7860303,7864393,7868517,7872753,7877575,7880835,
7884861,7888913,7893933,7897365,7901237,7905339,7909443,7913485,7918155,7922265]

def OMA.chk (n c : ℕ) : Bool :=
    decide ((c % 4096) < n) &&
    OMA.pb ((c % 4096)) (c / 4096 % 4096) &&
    OMA.pb (n ^ 2 - n - (c % 4096)) (c / 4096 % 4096) &&
    OMA.pb (n ^ 2 + n + (c % 4096)) (c / 4096 % 4096)

set_option maxRecDepth 1000000 in
theorem OMA.h : ∀ i < 106, OMA.chk (i + 1829) (OMA.T.getD i 0) = true := by
  decide +kernel

theorem OMA.solution : OMA.R_OeisA219023_conjecture_3_R1.H1 := by
  intro n h1 h2
  have h := OMA.h (n - 1829) (by omega)
  rw [show n - 1829 + 1829 = n by omega] at h
  generalize OMA.T.getD (n - 1829) 0 = c at h
  simp only [OMA.chk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨a0, p0⟩, p1⟩, p2⟩ := h
  exact ⟨(c % 4096), OMA.pb_prime p0, a0, OMA.pb_prime p1, OMA.pb_prime p2⟩
