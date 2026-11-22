import CubicMangoldt
import ExactCutoff

open scoped BigOperators
namespace FixedEven.Cubic
noncomputable section

/-- In this range every negative reflected tail comes from a prime.
Only proper prime powers in the von Mangoldt coordinate can contribute error. -/
theorem mangoldt_error_local_exact {q N z : ℕ} [Fact q.Prime]
    (hN : 4096 ≤ N) (hz : 8 ≤ z)
    (hlocal : ∀ n ∈ screen N z, N-n < z^3) (hq : (N-2)*(N-2) < q)
    (c : ℝ) (hc : 0 < c) (linear : DirichletCharacter ℂ q → ℝ) :
    let e := mangoldtObservable N z c linear - ∑ p ∈ genuine (screen N z) N, Real.log p
    0 ≤ e ∧ e ≤ (Nat.sqrt (N-2) : ℝ) * Real.log 4 := by
  obtain ⟨hl,hu⟩ := mangoldt_error_count hN hz hq c hc linear
  have hzz : z-1+1 = z := by omega
  have hg := detected_eq_genuine_of_cube (screen N z) (N:=N) (t:=N/z) (y:=z-1)
    (by simp [hzz]) (screen_spec hN hz).2.2 (by simpa only [hzz] using hlocal)
  exact ⟨hl,by simpa only [hg,sub_self,mul_zero,zero_add] using hu⟩

/-- Each target admits a nonvacuous scale just above its cube root with zero
reflected-composite error and the same square-root bound on the true two
corrected von Mangoldt endpoints. Every balanced coprime prime pair survives
these scales by `prime_pair_mem_exact_screen`. -/
theorem every_target_mangoldt_sqrt {N : ℕ} (hN : 4096 ≤ N) :
    ∃ z : ℕ, 8 ≤ z ∧ N < z^3 ∧ z^3 ≤ 4*N ∧ 3*z ≤ N ∧
      ∀ (q : ℕ) [Fact q.Prime], (N-2)*(N-2) < q →
      ∀ (c : ℝ), 0 < c → ∀ linear : DirichletCharacter ℂ q → ℝ,
        let e := mangoldtObservable N z c linear - ∑ p ∈ genuine (screen N z) N, Real.log p
        0 ≤ e ∧ e ≤ (Nat.sqrt (N-2) : ℝ) * Real.log 4 := by
  obtain ⟨z,hz,hcube,hupper,hwindow⟩ := choose_exact_scale hN
  refine ⟨z,hz,hcube,hupper,hwindow,?_⟩
  intro q hq' hq c hc linear
  exact mangoldt_error_local_exact hN hz
    (fun n _ => (Nat.sub_le N n).trans_lt hcube) hq c hc linear

#print axioms mangoldt_error_local_exact
#print axioms every_target_mangoldt_sqrt
end
end FixedEven.Cubic
