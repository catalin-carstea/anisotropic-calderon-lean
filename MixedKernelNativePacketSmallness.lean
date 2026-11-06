import TaskInterface
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

/-- Pure scalar choices give every native packet smallness cap before delta or a physical point is chosen. -/
theorem exists_native_packet_smallness_parameters
    (c0 D D2 D3 rho t : ℝ)
    (hc0 : 0 < c0) (hD : 0 < D) (hD2 : 0 < D2) (hD3 : 0 < D3)
    (hRho : 0 < rho) (ht : 0 < t) :
    ∃ N : ℕ, ∃ rCap : ℝ, 0 < rCap ∧
      ∀ p : ℕ, N ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      ∀ beta r : ℝ, c0*(p : ℝ) ≤ beta → 0 < r → r ≤ rCap →
        1 ≤ beta ∧ r ≤ min 1 (4*rho) ∧ eps*r ≤ t ∧
        (2*D)*r^2 ≤ 1/320 ∧ D2*eps*r ≤ 1/320 ∧ D3*r^2 ≤ 1/8 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/c0)
  let rCap := min (min 1 (4*rho))
    (min t (min (1/(640*(D+1))) (min (1/(320*(D2+1))) (1/(8*(D3+1))))))
  have hrCap : 0 < rCap := by dsimp [rCap];positivity
  refine ⟨N,rCap,hrCap,?_⟩
  intro p hp eps heps heps1 beta r hBeta hr hrBound
  have hrMin : r ≤ min 1 (4*rho) := hrBound.trans (min_le_left _ _)
  have hr1 : r ≤ 1 := hrMin.trans (min_le_left _ _)
  have hrt : r ≤ t := hrBound.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrD : r ≤ 1/(640*(D+1)) := hrBound.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrD2 : r ≤ 1/(320*(D2+1)) := hrBound.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hrD3 : r ≤ 1/(8*(D3+1)) := hrBound.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hBeta1 : 1 ≤ beta := by
    have hNP : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hLarge := (div_lt_iff₀ hc0).mp hN
    have hh := mul_le_mul_of_nonneg_left hNP hc0.le
    nlinarith only [hLarge,hh,hBeta]
  have hSquare : r^2 ≤ r := by nlinarith only [mul_le_mul_of_nonneg_left hr1 hr.le]
  have hCapD := (le_div_iff₀ (by positivity : 0 < 640*(D+1))).mp hrD
  have hEta1 : (2*D)*r^2 ≤ 1/320 := by
    have hh := mul_le_mul_of_nonneg_left hSquare (by positivity : 0 ≤ 2*D)
    nlinarith only [hh,hCapD,hr.le]
  have hCapD2 := (le_div_iff₀ (by positivity : 0 < 320*(D2+1))).mp hrD2
  have hEta2 : D2*eps*r ≤ 1/320 := by
    have hh := mul_le_mul_of_nonneg_left heps1 (by positivity : 0 ≤ D2*r)
    nlinarith only [hh,hCapD2,hr.le]
  have hCapD3 := (le_div_iff₀ (by positivity : 0 < 8*(D3+1))).mp hrD3
  have hJacCap : D3*r^2 ≤ 1/8 := by
    have hh := mul_le_mul_of_nonneg_left hSquare hD3.le
    nlinarith only [hh,hCapD3,hr.le]
  have hSmall : eps*r ≤ t :=
    (mul_le_mul_of_nonneg_right heps1 hr.le).trans (by simpa only [one_mul] using hrt)
  exact ⟨hBeta1,hrMin,hSmall,hEta1,hEta2,hJacCap⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
