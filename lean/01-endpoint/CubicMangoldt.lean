import CubicRate

open scoped BigOperators
open ArithmeticFunction
open Goldbach.PrimePowerError (middle sieveWeight)

namespace FixedEven.Cubic
noncomputable section

/-- Both calls use the paper's von Mangoldt coefficients and principal-character correction. -/
def mangoldtEndpoint {q : ℕ} [Fact q.Prime] (X : ℕ) (S : Finset ℕ) (c : ℝ)
    (w : ℕ → ℝ) (linear : DirichletCharacter ℂ q → ℝ) : ℝ :=
  let b := Goldbach.FourierWindow.dirichletCoeff S c ((q-1 : ℕ) : ℝ) w
    (id : DirichletCharacter ℂ q → _)
  PaperFourier.endpoint X (Goldbach.PrimeEndpoint.centeredSpectralRamp q X vonMangoldt b linear) +
    b 1 * (X : ℝ) * ((X : ℝ)+1) * Real.log (1 + 1 / (X : ℝ))

/-- The two weights on the full middle interval are precisely the Section 5
signed weight and its pointwise square, with integer sieve and tail cutoffs. -/
def mangoldtObservable {q : ℕ} [Fact q.Prime] (N z : ℕ) (c : ℝ)
    (linear : DirichletCharacter ℂ q → ℝ) : ℝ :=
  let w := sieveWeight N ((z-1 : ℕ) : ℝ) ((N/z : ℕ) : ℝ)
  (mangoldtEndpoint (N-2) (middle N) c (fun n => w n ^ 2) linear -
   mangoldtEndpoint (N-2) (middle N) c w linear) / 2

def selected (N z : ℕ) : Finset ℕ :=
  (screen N z).filter fun n => tail (N-n) (N/z) = -1

private theorem middle_spec {N : ℕ} :
    (∀ n ∈ middle N, 2 ≤ n ∧ n ≤ N-2) ∧
    (∀ n ∈ middle N, ∀ m ∈ middle N, n < 2*m) := by
  refine ⟨fun n hn => Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1, ?_⟩
  intro n hn m hm
  have ha := (Finset.mem_filter.mp hn).2.2
  have hb := (Finset.mem_filter.mp hm).2.1
  omega

private theorem member_screen {N z n : ℕ} (hN : 4 ≤ N) (hn : n ∈ middle N) :
    n ∈ screen N z ↔ n.Coprime N ∧ ((z-1 : ℕ) : ℝ) < ((N-n).minFac : ℝ) := by
  classical
  have hr := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  have hgt : 1 < N-n := by omega
  have hrough : Rough (z-1) (N-n) ↔ z-1 < (N-n).minFac := by
    refine ⟨fun h => h _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _), ?_⟩
    intro h p hp hd
    exact lt_of_lt_of_le h (Nat.minFac_le_of_dvd hp.two_le hd)
  change n ∈ (Finset.Icc 2 (N-2)).filter _ ↔ _
  rw [Finset.mem_filter]
  have hi := (Finset.mem_filter.mp hn).1
  have hh := (Finset.mem_filter.mp hn).2
  simp only [hi, hh.1, hh.2, true_and, hrough, Nat.cast_lt]

private theorem paper_weight {N z n : ℕ} (hN : 4 ≤ N) (hn : n ∈ middle N) :
    sieveWeight N ((z-1 : ℕ) : ℝ) ((N/z : ℕ) : ℝ) n =
      if n ∈ screen N z then (tail (N-n) (N/z) : ℝ) else 0 := by
  classical
  unfold sieveWeight
  by_cases hs : n ∈ screen N z
  · simp [hs,(member_screen hN hn).mp hs,tail]
  · rw [if_neg (mt (member_screen hN hn).mpr hs),if_neg hs]

/-- A direct identity for the quadratic difference of two true corrected Λ endpoints. -/
theorem mangoldtObservable_eq_sum {q N z : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hq : (N-2)*(N-2) < q)
    (c : ℝ) (hc : 0 < c) (linear : DirichletCharacter ℂ q → ℝ) :
    mangoldtObservable N z c linear = ∑ n ∈ selected N z, vonMangoldt n := by
  classical
  let w := sieveWeight N ((z-1 : ℕ) : ℝ) ((N/z : ℕ) : ℝ)
  have hr := (middle_spec (N:=N)).1
  have hRatio := (middle_spec (N:=N)).2
  have he (v : ℕ → ℝ) : mangoldtEndpoint (N-2) (middle N) c v linear =
      ∑ n ∈ middle N, vonMangoldt n * v n :=
    (Goldbach.PrimeEndpoint.vonMangoldt_endpoint (middle N) c v linear
      (by omega) hq hc hr hRatio).symm
  change (mangoldtEndpoint (N-2) (middle N) c (fun n => w n^2) linear -
      mangoldtEndpoint (N-2) (middle N) c w linear)/2 = _
  rw [he, he, ← Finset.sum_sub_distrib]
  apply (div_eq_iff (by norm_num : (2:ℝ) ≠ 0)).2
  have hsub : selected N z ⊆ middle N := by
    intro n hn
    obtain ⟨hs,_⟩ := Finset.mem_filter.mp hn
    have hh := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨hh.1,hh.2.1,hh.2.2.1⟩
  have hf : (middle N).filter (fun n => n ∈ selected N z) = selected N z := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun h => ⟨hsub h,h⟩⟩
  rw [← hf, Finset.sum_filter, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [w]
  rw [paper_weight (by omega) hn]
  by_cases hs : n ∈ screen N z
  · obtain ⟨h1,h2,h3⟩ := (screen_spec hN hz).2.2 n hs
    have hzz : z-1+1 = z := by omega
    have hv := tail_eq_mu (by omega : 0<N-n) (Nat.sub_le N n) h2
      (y:=z-1) (by simp [hzz]) h3
    rcases moebius_eq_or (N-n) with hm|hm|hm <;> simp [hs,selected,hv,hm]
    ring
  · simp [hs,selected]

private theorem detected_eq {N z : ℕ} :
    (selected N z).filter Nat.Prime = detected (screen N z) N (N/z) := by
  classical
  ext n
  simp [selected,detected,and_assoc,and_comm,and_left_comm]

private theorem genuine_subset {N z : ℕ} (hN : 4096 ≤ N) (hz : 8 ≤ z) :
    genuine (screen N z) N ⊆ detected (screen N z) N (N/z) := by
  intro n hn
  obtain ⟨hs,hp,hq⟩ := Finset.mem_filter.mp hn
  obtain ⟨h1,h2,h3⟩ := (screen_spec hN hz).2.2 n hs
  have hzz : z-1+1 = z := by omega
  exact Finset.mem_filter.mpr ⟨hs,hp,by
    rw [tail_eq_mu (by omega) (Nat.sub_le N n) h2 (y:=z-1) (by simp [hzz]) h3,
      moebius_apply_prime hq]⟩

/-- For each target, the contribution from false reflected primes is controlled
by their actual count. The second term comes only from proper prime powers
in the first coordinate. No bound on the cube-root scale is needed here. -/
theorem mangoldt_error_count {q N z : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hq : (N-2)*(N-2) < q)
    (c : ℝ) (hc : 0 < c) (linear : DirichletCharacter ℂ q → ℝ) :
    let e := mangoldtObservable N z c linear - ∑ p ∈ genuine (screen N z) N, Real.log p
    0 ≤ e ∧ e ≤ Real.log N *
      (((detected (screen N z) N (N/z)).card : ℝ) - (genuine (screen N z) N).card) +
      (Nat.sqrt (N-2) : ℝ) * Real.log 4 := by
  classical
  dsimp only
  rw [mangoldtObservable_eq_sum hN hz hq c hc]
  let A := selected N z
  let D := detected (screen N z) N (N/z)
  let G := genuine (screen N z) N
  have hss : A ⊆ screen N z := Finset.filter_subset _ _
  have hds : D ⊆ screen N z := Finset.filter_subset _ _
  have hGD : G ⊆ D := genuine_subset hN hz
  obtain ⟨hr,hRatio,_⟩ := screen_spec hN hz
  have hpr : A.filter Nat.Prime = D := detected_eq
  have hp := Goldbach.PrimePowerError.pollution (N-2) A (fun _ => 1) 1
    (by norm_num) (by simp) (fun n hn => (hr n (hss hn)).2)
    (fun n hn m hm => hRatio n (hss hn) m (hss hm))
  simp only [mul_one,one_mul,hpr] at hp
  have hDA : D ⊆ A := hpr ▸ Finset.filter_subset _ _
  have hDL : (∑ p ∈ D, Real.log p) ≤ ∑ n ∈ A, vonMangoldt n := by
    calc
      _ = ∑ p ∈ D, vonMangoldt p := Finset.sum_congr rfl fun p hp =>
        (vonMangoldt_apply_prime ((Finset.mem_filter.mp (hpr ▸ hp)).2)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hDA (fun _ _ _ => vonMangoldt_nonneg)
  have hrem := Finset.sum_sdiff hGD (f := fun p : ℕ => Real.log p)
  have htail : (∑ p ∈ D \ G, Real.log p) ≤ Real.log N * ((D.card : ℝ) - G.card) := by
    calc
      _ ≤ ∑ _p ∈ D \ G, Real.log N := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hp₁,hp₂⟩ := hr p (hds (Finset.mem_sdiff.mp hp).1)
        exact Real.log_le_log (by exact_mod_cast (show 0 < p by omega))
          (by exact_mod_cast (show p ≤ N by omega))
      _ = ((D \ G).card : ℝ)*Real.log N := by simp
      _ = _ := by rw [Finset.card_sdiff hGD,Nat.cast_sub (Finset.card_le_card hGD),mul_comm]
  have hpos : 0 ≤ ∑ p ∈ D \ G, Real.log p := Finset.sum_nonneg fun p hp =>
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by have := (hr p (hds (Finset.mem_sdiff.mp hp).1)).1; omega))
  change 0 ≤ (∑ n ∈ A, vonMangoldt n) - ∑ p ∈ G, Real.log p ∧
    (∑ n ∈ A, vonMangoldt n) - (∑ p ∈ G, Real.log p) ≤
      Real.log N * ((D.card : ℝ) - G.card) + (Nat.sqrt (N-2) : ℝ)*Real.log 4
  rw [abs_of_nonneg (sub_nonneg.mpr hDL)] at hp
  constructor <;> linarith

/-- The actual signed weight and its square, both applied to the von Mangoldt
endpoint, recover the screened weighted prime-pair sum with explicit
one-sided error at the cubic scale. -/
theorem mangoldt_error {q N z : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hsize : N < z^5) (hq : (N-2)*(N-2) < q)
    (c : ℝ) (hc : 0 < c) (linear : DirichletCharacter ℂ q → ℝ) :
    let e := mangoldtObservable N z c linear - ∑ p ∈ genuine (screen N z) N, Real.log p
    0 ≤ e ∧ e ≤ Real.log N * ((pool (z-1) (N/z^2)).card.choose 3 : ℝ) +
      (Nat.sqrt (N-2) : ℝ) * Real.log 4 := by
  obtain ⟨hl,hu⟩ := mangoldt_error_count hN hz hq c hc linear
  refine ⟨hl,hu.trans (add_le_add_right (mul_le_mul_of_nonneg_left ?_ ?_) _)⟩
  · have hzz : z-1+1 = z := by omega
    have herr := (count_error (screen N z) (N:=N) (y:=z-1) (t:=N/z)
      (by simp [hzz]) (by simpa [hzz] using hsize) (screen_spec hN hz).2.2).2
    simp only [hzz] at herr
    apply sub_le_iff_le_add'.2
    exact_mod_cast herr
  · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))

#print axioms mangoldtObservable_eq_sum
#print axioms mangoldt_error_count
#print axioms mangoldt_error
end
end FixedEven.Cubic
