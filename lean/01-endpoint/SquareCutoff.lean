import SignedContrast
import ZeroTriple
import ExactPollution

open scoped BigOperators
open ArithmeticFunction
open Goldbach.PrimePowerError (middle sieveWeight)
namespace FixedEven.Cubic
noncomputable section

/-- The least prime factor of a composite cannot exceed its square root. -/
theorem prime_of_rough_below_square {m y : ℕ} (hm : 1 < m) (hr : Rough y m)
    (hsize : m < (y+1)^2) : m.Prime := by
  by_contra hcomp
  have hmin := hr m.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)
  have hpow := Nat.pow_le_pow_left (show y+1 ≤ m.minFac by omega) 2
  have hsmall := Nat.minFac_sq_le_self (by omega : 0 < m) hcomp
  omega

/-- The canonical cutoff is above the square root and below the balanced window. -/
theorem square_scale {N : ℕ} (hN : 4096 ≤ N) :
    let z := N.sqrt+1
    8 ≤ z ∧ N < z^2 ∧ 3*z ≤ N := by
  dsimp only
  have hlo : 64 ≤ N.sqrt := Nat.le_sqrt.mpr (by simpa using hN)
  have hsq := Nat.sqrt_le N
  have hmul := Nat.mul_le_mul_left N.sqrt (show 4 ≤ N.sqrt by omega)
  exact ⟨by omega, Nat.lt_succ_sqrt' _, by omega⟩

theorem prime_pair_mem_sqrt_screen {N n : ℕ} (hN : 4096 ≤ N)
    (hn : n.Prime) (hm : (N-n).Prime) (hl : N ≤ 3*n) (hu : 3*n < 2*N)
    (hc : n.Coprime N) : n ∈ genuine (screen N (N.sqrt+1)) N :=
  prime_pair_mem_exact_screen (by omega) (square_scale hN).2.2 hn hm hl hu hc

private theorem cube_window_of_square {N z : ℕ} (hz : 8 ≤ z) (h : N < z^2) :
    2*N < 3*z^3 := by
  have h23 : z^2 ≤ z^3 := Nat.pow_le_pow_right (by omega) (by decide)
  omega

/-- On the paper's middle interval the original signed weight equals minus
the indicator of the screen. Every member of this screen has a prime partner. -/
theorem square_weight {N z n : ℕ} (hN : 4096 ≤ N) (hz : 8 ≤ z)
    (hsize : N < z^2) (hn : n ∈ middle N) :
    sieveWeight N ((z-1 : ℕ) : ℝ) ((N/z : ℕ) : ℝ) n =
      if n ∈ screen N z then (-1 : ℝ) else 0 := by
  classical
  rw [signed_weight_split hN hz (cube_window_of_square hz hsize) hn]
  by_cases hs : n ∈ screen N z
  · obtain ⟨hm,_,hrough⟩ := (screen_spec hN hz).2.2 n hs
    have hzz : z-1+1 = z := by omega
    have hp := prime_of_rough_below_square hm hrough (by
      rw [hzz]; exact (Nat.sub_le N n).trans_lt hsize)
    have hnot : ¬DistinctSemiprime (N-n) := by
      rintro ⟨a,b,ha,hb,_,hab⟩
      exact Nat.not_prime_mul' hab.symm ha.ne_one hb.ne_one hp
    simp [hs,hp,hnot]
  · simp [hs]

theorem single_eq_neg_mangoldt_of_square {N z q : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hsize : N < z^2)
    (hq : (N-2)*(N-2) < q) (c : ℝ) (hc : 0 < c)
    (linear : DirichletCharacter ℂ q → ℝ) :
    singleEndpoint N z c linear = -mangoldtObservable N z c linear := by
  let w := sieveWeight N ((z-1 : ℕ) : ℝ) ((N/z : ℕ) : ℝ)
  have he (v : ℕ → ℝ) : mangoldtEndpoint (N-2) (middle N) c v linear =
      ∑ n ∈ middle N, vonMangoldt n * v n := by
    apply (Goldbach.PrimeEndpoint.vonMangoldt_endpoint (middle N) c v linear
      (by omega) hq hc ?_ ?_).symm
    · exact fun n hn => Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    · intro n hn m hm
      have hl := (Finset.mem_filter.mp hm).2.1
      have hu := (Finset.mem_filter.mp hn).2.2
      omega
  have hs : (∑ n ∈ middle N, vonMangoldt n * (w n)^2) =
      -∑ n ∈ middle N, vonMangoldt n * w n := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    change vonMangoldt n * (sieveWeight N _ _ n)^2 = -(vonMangoldt n * sieveWeight N _ _ n)
    rw [square_weight hN hz hsize hn]
    split_ifs <;> ring
  change mangoldtEndpoint (N-2) (middle N) c w linear =
    -((mangoldtEndpoint (N-2) (middle N) c (fun n => w n^2) linear -
       mangoldtEndpoint (N-2) (middle N) c w linear) / 2)
  rw [he,he]
  linarith

/-- Excess above the prime-pair log mass comes solely from positive higher
prime-power contributions in the first variable. -/
theorem single_square_cutoff_surplus {N z q : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hsize : N < z^2)
    (hq : (N-2)*(N-2) < q) (c : ℝ) (hc : 0 < c)
    (linear : DirichletCharacter ℂ q → ℝ) :
    let e := -singleEndpoint N z c linear - ∑ p ∈ genuine (screen N z) N, Real.log p
    0 ≤ e ∧ e ≤ (Nat.sqrt (N-2) : ℝ)*Real.log 4 := by
  have h23 : z^2 ≤ z^3 := Nat.pow_le_pow_right (by omega) (by decide)
  dsimp only
  rw [single_eq_neg_mangoldt_of_square hN hz hsize hq c hc linear, neg_neg]
  exact mangoldt_error_local_exact hN hz
    (fun n _ => ((Nat.sub_le N n).trans_lt hsize).trans_le h23) hq c hc linear

/-- This absolute error estimate does not assert that the signed endpoint
crosses a negative threshold. -/
theorem single_square_cutoff_error {N z q : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hsize : N < z^2)
    (hq : (N-2)*(N-2) < q) (c : ℝ) (hc : 0 < c)
    (linear : DirichletCharacter ℂ q → ℝ) :
    |singleEndpoint N z c linear + ∑ p ∈ genuine (screen N z) N, Real.log p| ≤
      (Nat.sqrt (N-2) : ℝ)*Real.log 4 := by
  obtain ⟨hl,hu⟩ := single_square_cutoff_surplus hN hz hsize hq c hc linear
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem single_sqrt_error_every_target {N q : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hq : (N-2)*(N-2) < q) (c : ℝ) (hc : 0 < c)
    (linear : DirichletCharacter ℂ q → ℝ) :
    let z := N.sqrt+1
    |singleEndpoint N z c linear + ∑ p ∈ genuine (screen N z) N, Real.log p| ≤
      (Nat.sqrt (N-2) : ℝ)*Real.log 4 :=
  single_square_cutoff_error hN (square_scale hN).1 (square_scale hN).2.1 hq c hc linear

/-- Subtracting the explicit higher-power correction recovers the genuine
logarithmic mass exactly from the original single signed endpoint. -/
theorem prime_mass_eq_neg_single_sub_correction {N z q : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hsize : N < z^2)
    (hq : (N-2)*(N-2) < q) (c : ℝ) (hc : 0 < c)
    (linear : DirichletCharacter ℂ q → ℝ) :
    (∑ p ∈ genuine (screen N z) N, Real.log p) =
      -singleEndpoint N z c linear - powerCorrection N z := by
  rw [single_eq_neg_mangoldt_of_square hN hz hsize hq c hc linear, neg_neg,
    observable_eq_prime_mass_add_correction hN hz (cube_window_of_square hz hsize) hq c hc linear]
  ring

#print axioms prime_of_rough_below_square
#print axioms square_scale
#print axioms prime_pair_mem_sqrt_screen
#print axioms square_weight
#print axioms single_eq_neg_mangoldt_of_square
#print axioms single_square_cutoff_surplus
#print axioms single_square_cutoff_error
#print axioms single_sqrt_error_every_target
#print axioms prime_mass_eq_neg_single_sub_correction
end
end FixedEven.Cubic
