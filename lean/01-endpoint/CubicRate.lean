import CubicEndpoint
import PrimePowerError
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find

open scoped BigOperators
namespace FixedEven.Cubic
noncomputable section

/-- Choose an integer only from the target N, with a genuine interval
of possible products of three primes above the roughness cutoff. -/
theorem choose_scale {N : ℕ} (hN : 4096 ≤ N) :
    ∃ z : ℕ, 8 ≤ z ∧ 8*z^3 ≤ N ∧ N < 27*z^3 := by
  let z := Nat.findGreatest (fun a => 8*a^3 ≤ N) N
  have h8 : 8 ≤ z := Nat.le_findGreatest (m:=8) (by omega) (by norm_num; exact hN)
  have hlo : 8*z^3 ≤ N := Nat.findGreatest_spec (P:=fun a => 8*a^3 ≤ N) (n:=N) (m:=8) (by omega) (by norm_num; exact hN)
  have hzi : z ≤ z^3 := Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) z
  have hnext : N < 8*(z+1)^3 := by
    by_contra! hn
    have hu : z+1 ≤ z := Nat.le_findGreatest (m:=z+1) (by omega) hn
    omega
  have hcube := Nat.pow_le_pow_left (show 2*(z+1) ≤ 3*z by omega) 3
  have hupper : 8*(z+1)^3 ≤ 27*z^3 := by
    simpa only [mul_pow] using hcube
  exact ⟨z,h8,hlo,hnext.trans_le hupper⟩

def screen (N z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 2 (N-2)).filter fun n =>
    N ≤ 3*n ∧ 3*n < 2*N ∧ Nat.Coprime n N ∧ Rough (z-1) (N-n)

theorem screen_spec {N z : ℕ} (hN : 4096 ≤ N) (hz : 8 ≤ z) :
    (∀ n ∈ screen N z, 2 ≤ n ∧ n ≤ N-2) ∧
    (∀ n ∈ screen N z, ∀ m ∈ screen N z, n < 2*m) ∧
    (∀ n ∈ screen N z, 1 < N-n ∧ N/z < N-n ∧ Rough (z-1) (N-n)) := by
  classical
  constructor
  · intro n hn
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  constructor
  · intro n hn m hm
    have hn' := (Finset.mem_filter.mp hn).2.2.1
    have hm' := (Finset.mem_filter.mp hm).2.1
    omega
  · intro n hn
    have hh := (Finset.mem_filter.mp hn).2
    have hd : N/z ≤ N/3 := Nat.div_le_div_left (by omega) (by decide)
    exact ⟨by omega,by omega,hh.2.2.2⟩

/-- A Chebyshev bound on the number of candidate primes. -/
theorem pool_log_bound {B z : ℕ} (hz : 1 ≤ z) :
    ((pool (z-1) B).card : ℝ) * Real.log z ≤ (B : ℝ) * Real.log 4 := by
  classical
  have hset : pool (z-1) B ⊆ (Finset.range (B+1)).filter Nat.Prime := by
    intro p hp
    obtain ⟨h, hpr⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := (Finset.mem_Ioc.mp h).2; omega),hpr⟩
  calc
    _ = ∑ _p ∈ pool (z-1) B, Real.log (z : ℝ) := by simp
    _ ≤ ∑ p ∈ pool (z-1) B, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      exact Real.log_le_log (by exact_mod_cast (show 0 < z by omega))
        (by exact_mod_cast (show z ≤ p by omega))
    _ ≤ ∑ p ∈ (Finset.range (B+1)).filter Nat.Prime, Real.log (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hset (fun p hp _ =>
        Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))
    _ ≤ _ := Goldbach.PrimePowerError.theta_le B

/-- Error in a count is O(N/log(N)^3), uniformly, with no distribution
hypothesis on the primes. The deliberately loose constant is explicit. -/
theorem cubic_error_rate {N z : ℕ} (hN : 4096 ≤ N) (hz : 8 ≤ z)
    (hlo : 8*z^3 ≤ N) (hhi : N < 27*z^3) :
    let S := screen N z
    (genuine S N).card ≤ (detected S N (N/z)).card ∧
    ((detected S N (N/z)).card - (genuine S N).card : ℝ) * (Real.log N)^3
      ≤ (135*Real.log 4)^3 * N := by
  let S := screen N z
  let B := N/z^2
  let M := (pool (z-1) B).card
  have hzz : z-1+1 = z := by omega
  have hsq : 27 ≤ z^2 := by nlinarith [Nat.pow_le_pow_left hz 2]
  have hsize : N < z^5 := by
    calc
      N < 27*z^3 := hhi
      _ ≤ z^2*z^3 := Nat.mul_le_mul_right _ hsq
      _ = z^5 := by ring
  have hspec := (screen_spec hN hz).2.2
  have herr := count_error S (y:=z-1) (t:=N/z) (by simp [hzz])
    (by simpa [hzz] using hsize) hspec
  simp only [hzz] at herr
  change (genuine S N).card ≤ (detected S N (N/z)).card ∧ _
  refine ⟨herr.1, ?_⟩
  have hsmall : B ≤ 27*z := by
    apply (Nat.div_le_iff_le_mul_add_pred (by positivity)).2
    nlinarith [hhi.le, Nat.zero_le (z^2-1)]
  have hlog : Real.log (N:ℝ) ≤ 5*Real.log (z:ℝ) := by
    have hh : (N:ℝ) ≤ (z:ℝ)^5 := by exact_mod_cast hsize.le
    simpa [Real.log_pow] using Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) hh
  have hnlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hB : (B:ℝ) ≤ 27*(z:ℝ) := by exact_mod_cast hsmall
  have hp : (M:ℝ) * Real.log (z:ℝ) ≤ (B:ℝ)*Real.log 4 := pool_log_bound (by omega)
  have hM : (M:ℝ)*Real.log (N:ℝ) ≤ (135*Real.log 4)*(z:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg M : (0:ℝ) ≤ M)
    have h2 := mul_le_mul_of_nonneg_right hB (show 0 ≤ Real.log 4 by positivity)
    linarith
  have hcount' : (detected S N (N/z)).card ≤ (genuine S N).card + M^3 :=
    herr.2.trans (Nat.add_le_add_left (Nat.choose_le_pow M 3) _)
  have hcount : ((detected S N (N/z)).card : ℝ) - (genuine S N).card ≤ (M:ℝ)^3 := by
    have hh : ((detected S N (N/z)).card : ℝ) ≤ (genuine S N).card + (M:ℝ)^3 := by exact_mod_cast hcount'
    linarith
  have hzN : (z:ℝ)^3 ≤ N := by exact_mod_cast (show z^3 ≤ N by omega)
  calc
    _ ≤ (M:ℝ)^3 * (Real.log N)^3 :=
      mul_le_mul_of_nonneg_right hcount (pow_nonneg hnlog _)
    _ = ((M:ℝ)*Real.log N)^3 := (mul_pow ..).symm
    _ ≤ ((135*Real.log 4)*(z:ℝ))^3 := pow_le_pow_left (by positivity) hM _
    _ = (135*Real.log 4)^3 * (z:ℝ)^3 := mul_pow .. 
    _ ≤ _ := mul_le_mul_of_nonneg_left hzN (by positivity)

/-- Uniform quantifiers on the target, including all even N above the threshold. -/
theorem every_target {N : ℕ} (hN : 4096 ≤ N) :
    ∃ z : ℕ, 8 ≤ z ∧ 8*z^3 ≤ N ∧ N < 27*z^3 ∧
      (genuine (screen N z) N).card ≤ (detected (screen N z) N (N/z)).card ∧
      ((detected (screen N z) N (N/z)).card - (genuine (screen N z) N).card : ℝ) *
        (Real.log N)^3 ≤ (135*Real.log 4)^3 * N := by
  obtain ⟨z,hz,hl,hh⟩ := choose_scale hN
  exact ⟨z,hz,hl,hh,cubic_error_rate hN hz hl hh⟩

/-- Our observable is a pair of the paper's corrected character endpoints. -/
def observable {q : ℕ} [Fact q.Prime] (N z : ℕ) (c : ℝ)
    (linear : DirichletCharacter ℂ q → ℝ) : ℝ :=
  let w := fun n : ℕ => (tail (N-n) (N/z) : ℝ)
  (corrected (N-2) (screen N z) c (fun n => w n ^ 2) linear -
   corrected (N-2) (screen N z) c w linear) / 2

theorem observable_eq_count {q N z : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hq : (N-2)*(N-2) < q)
    (c : ℝ) (hc : 0 < c) (linear : DirichletCharacter ℂ q → ℝ) :
    observable N z c linear = ((detected (screen N z) N (N/z)).card : ℝ) := by
  obtain ⟨hr, hRatio, hs⟩ := screen_spec hN hz
  have hzz : z-1+1 = z := by omega
  exact two_endpoints (y:=z-1) (screen N z) c linear (by omega) hq hc hr hRatio
    (by simp [hzz]) hs

/-- Every target admits a scale at which the actual spectral observable differs
from the screened count of prime pairs by at most a uniform logarithmic error. -/
theorem uniform_endpoint_error {N : ℕ} (hN : 4096 ≤ N) :
    ∃ z : ℕ, 8 ≤ z ∧ 8*z^3 ≤ N ∧ N < 27*z^3 ∧
      ∀ (q : ℕ) [Fact q.Prime], (N-2)*(N-2) < q →
      ∀ (c : ℝ), 0 < c → ∀ linear : DirichletCharacter ℂ q → ℝ,
        let e := observable N z c linear - ((genuine (screen N z) N).card : ℝ)
        0 ≤ e ∧ e * (Real.log N)^3 ≤ (135*Real.log 4)^3 * N := by
  obtain ⟨z,hz,hl,hu,hlo,hhi⟩ := every_target hN
  refine ⟨z,hz,hl,hu,?_⟩
  intro q hprim hq c hc linear
  dsimp only
  rw [observable_eq_count hN hz hq c hc]
  exact ⟨sub_nonneg.mpr (by exact_mod_cast hlo), hhi⟩

/-- A lower estimate on this observable above its explicit error would give a
Goldbach representation for this target. That lower estimate is a hypothesis. -/
theorem representation_of_endpoint_lower {N z q : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hl : 8*z^3 ≤ N) (hu : N < 27*z^3)
    (hq : (N-2)*(N-2) < q) (c : ℝ) (hc : 0 < c)
    (linear : DirichletCharacter ℂ q → ℝ)
    (hlower : (135*Real.log 4)^3 * N < observable N z c linear * (Real.log N)^3) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p+r=N := by
  rw [observable_eq_count hN hz hq c hc] at hlower
  have he := (cubic_error_rate hN hz hl hu).2
  have hg : (genuine (screen N z) N).Nonempty := by
    by_contra h
    have hem := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hem] at he
    linarith
  obtain ⟨p,hp⟩ := hg
  obtain ⟨hs,hpp,hrr⟩ := Finset.mem_filter.mp hp
  have hpN := ((screen_spec hN hz).1 p hs).2
  exact ⟨p,N-p,hpp,hrr,by omega⟩

#print axioms choose_scale
#print axioms screen_spec
#print axioms pool_log_bound
#print axioms cubic_error_rate
#print axioms every_target
#print axioms observable_eq_count
#print axioms uniform_endpoint_error
#print axioms representation_of_endpoint_lower
end
end FixedEven.Cubic
