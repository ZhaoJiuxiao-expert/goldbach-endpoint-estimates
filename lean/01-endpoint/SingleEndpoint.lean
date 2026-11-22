import CubicMangoldt
import ExactCutoff

open scoped BigOperators
open ArithmeticFunction
open Goldbach.PrimePowerError (middle sieveWeight)

namespace FixedEven.Cubic
noncomputable section

/-- The paper's single corrected endpoint with its signed Section 5 sieve weight. -/
def singleEndpoint {q : ℕ} [Fact q.Prime] (N z : ℕ) (c : ℝ)
    (linear : DirichletCharacter ℂ q → ℝ) : ℝ :=
  mangoldtEndpoint (N-2) (middle N) c
    (sieveWeight N ((z-1 : ℕ) : ℝ) ((N/z : ℕ) : ℝ)) linear

private theorem consecutive_product (k : ℤ) : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) := by
  by_cases hk : 0 ≤ k
  · have hh : (0 : ℝ) ≤ k := by exact_mod_cast hk
    exact mul_nonneg hh (by linarith)
  · have hh : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

private theorem weight_integer (N n : ℕ) (y t : ℝ) : ∃ k : ℤ, (k : ℝ) = sieveWeight N y t n := by
  classical
  unfold sieveWeight
  split_ifs
  · refine ⟨∑ d ∈ (N-n).divisors.filter (fun d : ℕ => t < (d : ℝ)), moebius d, ?_⟩
    push_cast
    rfl
  · exact ⟨0, by simp⟩

/-- The correction with the squared weight can be eliminated in this one-sided
bound because Λ is nonnegative and the signed weight takes integer values. -/
theorem neg_single_le_observable {N z q : ℕ} [Fact q.Prime]
    (hN : 4 ≤ N) (hq : (N-2)*(N-2) < q)
    (c : ℝ) (hc : 0 < c) (linear : DirichletCharacter ℂ q → ℝ) :
    -singleEndpoint N z c linear ≤ mangoldtObservable N z c linear := by
  let w := sieveWeight N ((z-1 : ℕ) : ℝ) ((N/z : ℕ) : ℝ)
  have he (v : ℕ → ℝ) : mangoldtEndpoint (N-2) (middle N) c v linear =
      ∑ n ∈ middle N, vonMangoldt n * v n := by
    apply (Goldbach.PrimeEndpoint.vonMangoldt_endpoint (middle N) c v linear
      (by omega) hq hc ?_ ?_).symm
    · exact fun n hn => Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    · intro n hn m hm
      have h1 := (Finset.mem_filter.mp hn).2.2
      have h2 := (Finset.mem_filter.mp hm).2.1
      omega
  change -mangoldtEndpoint (N-2) (middle N) c w linear ≤
    (mangoldtEndpoint (N-2) (middle N) c (fun n => w n^2) linear -
      mangoldtEndpoint (N-2) (middle N) c w linear)/2
  rw [he, he]
  have hsum : 0 ≤ ∑ n ∈ middle N, (vonMangoldt n * (w n)^2 + vonMangoldt n * w n) := by
    apply Finset.sum_nonneg
    intro n _
    obtain ⟨k,hk⟩ := weight_integer N n ((z-1 : ℕ) : ℝ) ((N/z : ℕ) : ℝ)
    change (k : ℝ) = w n at hk
    rw [← hk]
    nlinarith [mul_nonneg (vonMangoldt_nonneg (n:=n)) (consecutive_product k)]
  rw [Finset.sum_add_distrib] at hsum
  linarith

/-- Unconditional lower bound for the weight of genuine prime pairs, expressed
using only the original signed corrected endpoint and an explicit tolerance. -/
theorem prime_mass_from_single {N z q : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hsize : N < z^5) (hq : (N-2)*(N-2) < q)
    (c : ℝ) (hc : 0 < c) (linear : DirichletCharacter ℂ q → ℝ) :
    -singleEndpoint N z c linear -
      (Real.log N * ((pool (z-1) (N/z^2)).card.choose 3 : ℝ) +
       (Nat.sqrt (N-2) : ℝ)*Real.log 4) ≤
      ∑ p ∈ genuine (screen N z) N, Real.log p := by
  have hx := neg_single_le_observable (z:=z) (by omega : 4 ≤ N) hq c hc linear
  have he := (mangoldt_error hN hz hsize hq c hc linear).2
  linarith

/-- Crossing this explicitly negative threshold is sufficient for a
representation of N. The signed endpoint crossing is a hypothesis. -/
theorem representation_of_negative_single {N z q : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hsize : N < z^5) (hq : (N-2)*(N-2) < q)
    (c : ℝ) (hc : 0 < c) (linear : DirichletCharacter ℂ q → ℝ)
    (hneg : singleEndpoint N z c linear <
      -(Real.log N * ((pool (z-1) (N/z^2)).card.choose 3 : ℝ) +
        (Nat.sqrt (N-2) : ℝ)*Real.log 4)) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p+r=N := by
  have hm := prime_mass_from_single hN hz hsize hq c hc linear
  have hg : (genuine (screen N z) N).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hm
    linarith
  obtain ⟨p,hp⟩ := hg
  obtain ⟨hs,hp',hr⟩ := Finset.mem_filter.mp hp
  have hle := ((screen_spec hN hz).1 p hs).2
  exact ⟨p,N-p,hp',hr,by omega⟩

private theorem exact_reflected_set {N z : ℕ} (hN : 4096 ≤ N) (hz : 8 ≤ z)
    (hwindow : 2*N < 3*z^3) :
    detected (screen N z) N (N/z) = genuine (screen N z) N := by
  classical
  have hzz : z-1+1 = z := by omega
  have hcut : N / (z-1+1) ≤ N/z := by rw [hzz]
  apply detected_eq_genuine_of_cube (screen N z) hcut (screen_spec hN hz).2.2
  intro n hn
  rw [hzz]
  have hh := (Finset.mem_filter.mp hn).2.1
  omega

/-- At an exact cubic cutoff, all negative reflected Möbius signs represent
primes. Only proper prime powers in the first variable contribute to this
one-sided error estimate on the original signed endpoint. -/
theorem single_square_root_lower {N z q : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hwindow : 2*N < 3*z^3)
    (hq : (N-2)*(N-2) < q) (c : ℝ) (hc : 0 < c)
    (linear : DirichletCharacter ℂ q → ℝ) :
    -singleEndpoint N z c linear - (Nat.sqrt (N-2) : ℝ)*Real.log 4 ≤
      ∑ p ∈ genuine (screen N z) N, Real.log p := by
  have heq := exact_reflected_set hN hz hwindow
  have he := (mangoldt_error_count hN hz hq c hc linear).2
  rw [heq, sub_self, mul_zero, zero_add] at he
  have hx := neg_single_le_observable (z:=z) (by omega : 4 ≤ N) hq c hc linear
  linarith

/-- The threshold is sufficient for this target. No claim that endpoints
cross that threshold is required for the preceding unconditional bound. -/
theorem representation_of_single_below_sqrt {N z q : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hwindow : 2*N < 3*z^3)
    (hq : (N-2)*(N-2) < q) (c : ℝ) (hc : 0 < c)
    (linear : DirichletCharacter ℂ q → ℝ)
    (hneg : singleEndpoint N z c linear < -((Nat.sqrt (N-2) : ℝ)*Real.log 4)) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p+r=N := by
  have hm := single_square_root_lower hN hz hwindow hq c hc linear
  have hg : (genuine (screen N z) N).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hm
    linarith
  obtain ⟨p,hp⟩ := hg
  obtain ⟨hs,hp',hr⟩ := Finset.mem_filter.mp hp
  have hle := ((screen_spec hN hz).1 p hs).2
  exact ⟨p,N-p,hp',hr,by omega⟩

/-- For every target a suitable cutoff exists. The signed endpoint inequality
is still an explicit input of the implication. -/
theorem every_target_single_threshold {N : ℕ} (hN : 4096 ≤ N) :
    ∃ z : ℕ, 8 ≤ z ∧ N < z^3 ∧ z^3 ≤ 4*N ∧ 3*z ≤ N ∧
      ∀ (q : ℕ) [Fact q.Prime], (N-2)*(N-2) < q →
      ∀ (c : ℝ), 0 < c → ∀ linear : DirichletCharacter ℂ q → ℝ,
      singleEndpoint N z c linear < -((Nat.sqrt (N-2) : ℝ)*Real.log 4) →
      ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p+r=N := by
  obtain ⟨z,hz,hlo,hhi,hw⟩ := choose_exact_scale hN
  refine ⟨z,hz,hlo,hhi,hw,?_⟩
  intro q hprime hq c hc linear hneg
  exact representation_of_single_below_sqrt hN hz (by omega) hq c hc linear hneg

#print axioms neg_single_le_observable
#print axioms prime_mass_from_single
#print axioms representation_of_negative_single
#print axioms single_square_root_lower
#print axioms representation_of_single_below_sqrt
#print axioms every_target_single_threshold
end
end FixedEven.Cubic
