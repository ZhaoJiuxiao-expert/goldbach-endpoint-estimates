import CubicRate

namespace FixedEven.Cubic
open ArithmeticFunction
noncomputable section

/-- Below the cube of the smallest allowed factor, a negative Möbius value
identifies a prime. Repeated prime factors have Möbius value zero. -/
theorem rough_mu_neg_iff_prime {m y : ℕ} (hm : 1 < m) (hr : Rough y m)
    (hsize : m < (y+1)^3) : moebius m = -1 ↔ m.Prime := by
  refine ⟨fun hmu => ?_, moebius_apply_prime⟩
  by_contra hcomp
  have h35 : (y+1)^3 ≤ (y+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  obtain ⟨htr,_⟩ := triple_signature hm (le_refl m) (hsize.trans_le h35) hr hmu hcomp
  obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp htr
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < m.primeFactors.card by omega)
  have hpool := Finset.mem_Ioc.mp (Finset.mem_filter.mp (hsub hp)).1
  have hbound : m / (y+1)^2 < y+1 := (Nat.div_lt_iff_lt_mul (by positivity)).2 (by
    calc m < (y+1)^3 := hsize
         _ = (y+1)*(y+1)^2 := by ring)
  omega

/-- The cubic condition is needed only for the reflected integers on the selected support. -/
theorem detected_eq_genuine_of_cube (S : Finset ℕ) {N y t : ℕ}
    (hcut : N / (y+1) ≤ t)
    (hs : ∀ n ∈ S, 1 < N-n ∧ t < N-n ∧ Rough y (N-n))
    (hsize : ∀ n ∈ S, N-n < (y+1)^3) : detected S N t = genuine S N := by
  classical
  ext n
  simp only [detected, genuine, Finset.mem_filter]
  by_cases hn : n ∈ S
  · obtain ⟨hm,ht,hr⟩ := hs n hn
    rw [tail_eq_mu (by omega) (Nat.sub_le N n) ht hcut hr,
      rough_mu_neg_iff_prime hm hr (hsize n hn)]
  · simp [hn]

/-- An explicit choice of cutoff, strictly above the cube root of N and
below the balanced window. Its cube remains within a constant factor of N. -/
theorem choose_exact_scale {N : ℕ} (hN : 4096 ≤ N) :
    ∃ z : ℕ, 8 ≤ z ∧ N < z^3 ∧ z^3 ≤ 4*N ∧ 3*z ≤ N := by
  obtain ⟨w, hw, hlo, hhi⟩ := choose_scale hN
  have h2 : 2 ≤ w^2 := by nlinarith [Nat.pow_le_pow_left hw 2]
  have hw3 : 2*w ≤ w^3 := by
    calc 2*w ≤ w^2*w := Nat.mul_le_mul_right w h2
         _ = w^3 := by ring
  refine ⟨3*w, by omega, ?_, ?_, by omega⟩
  · simpa only [mul_pow, Nat.reducePow] using hhi
  · rw [mul_pow]
    norm_num
    omega

/-- Every balanced coprime prime pair survives such a cutoff. The coprimality
condition is already present in the definition of the underlying screen. -/
theorem prime_pair_mem_exact_screen {N z n : ℕ} (hz : 1 ≤ z) (hzN : 3*z ≤ N)
    (hn : n.Prime) (hm : (N-n).Prime) (hl : N ≤ 3*n) (hu : 3*n < 2*N)
    (hc : n.Coprime N) : n ∈ genuine (screen N z) N := by
  classical
  have hn2 := hn.two_le
  have hm2 := hm.two_le
  have hrough : Rough (z-1) (N-n) := by
    intro p hp hpm
    have heq := (Nat.dvd_prime_two_le hm hp.two_le).mp hpm
    omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hn2, by omega⟩,hl,hu,hc,hrough⟩,hn,hm⟩

/-- Endpoint identity for any valid cutoff, including the non-vacuous scales
of `choose_exact_scale`. It gives no positive lower bound for the endpoint. -/
theorem exact_screen_endpoint {q N z : ℕ} [Fact q.Prime] (c : ℝ)
    (linear : DirichletCharacter ℂ q → ℝ)
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hsize : N < z^3)
    (hq : N*N < q) (hc : 0 < c) :
    let S := screen N z
    let w := fun n : ℕ => (tail (N-n) (N/z) : ℝ)
    (corrected N S c (fun n => w n ^ 2) linear - corrected N S c w linear) / 2 =
      ((genuine S N).card : ℝ) := by
  dsimp only
  have hzz : z-1+1 = z := by omega
  obtain ⟨hspan,hratio,hrefl⟩ := screen_spec hN hz
  have hcut : N / (z-1+1) ≤ N/z := by rw [hzz]
  have hlocal (n : ℕ) (_ : n ∈ screen N z) : N-n < (z-1+1)^3 := by
    rw [hzz]
    exact (Nat.sub_le ..).trans_lt hsize
  rw [← detected_eq_genuine_of_cube (screen N z) hcut hrefl hlocal]
  exact two_endpoints (screen N z) c linear (by omega) hq hc
    (fun n hn => ⟨(hspan n hn).1, (hspan n hn).2.trans (Nat.sub_le ..)⟩)
    hratio hcut hrefl

/-- At the paper's endpoint X=N−2, it suffices for the cutoff cube to lie
strictly above the top of the reflected central window. -/
theorem observable_exact_of_central {N z q : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hwindow : 2*N < 3*z^3)
    (hq : (N-2)*(N-2) < q) (c : ℝ) (hc : 0 < c)
    (linear : DirichletCharacter ℂ q → ℝ) :
    observable N z c linear = ((genuine (screen N z) N).card : ℝ) := by
  classical
  rw [observable_eq_count hN hz hq c hc]
  have hzz : z-1+1 = z := by omega
  have hrefl := (screen_spec hN hz).2.2
  have hlocal (n : ℕ) (hn : n ∈ screen N z) : N-n < (z-1+1)^3 := by
    rw [hzz]
    have hn₁ := (Finset.mem_filter.mp hn).2.1
    omega
  rw [detected_eq_genuine_of_cube (screen N z)
    (show N/(z-1+1) ≤ N/z by rw [hzz]) hrefl hlocal]

theorem observable_exact {N z q : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z) (hsize : N < z^3)
    (hq : (N-2)*(N-2) < q) (c : ℝ) (hc : 0 < c)
    (linear : DirichletCharacter ℂ q → ℝ) :
    observable N z c linear = ((genuine (screen N z) N).card : ℝ) :=
  observable_exact_of_central hN hz (by omega) hq c hc linear

#print axioms rough_mu_neg_iff_prime
#print axioms detected_eq_genuine_of_cube
#print axioms choose_exact_scale
#print axioms prime_pair_mem_exact_screen
#print axioms exact_screen_endpoint
#print axioms observable_exact_of_central
#print axioms observable_exact

end
end FixedEven.Cubic
