import Calderon.PhysicalHarmonicDilation

/-! The coefficient-normalized metric g(Rx) retains frozen admissibility for R≥1. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge

def enlargedBallNormalizedMetric (g : MatrixField) (R : ℝ) : MatrixField :=
  fun x => g (R • x)

theorem isAdmissibleMetric_enlargedBallNormalizedMetric
    (g : MatrixField) (hg : IsAdmissibleMetric g) (R : ℝ) (hR : 1 ≤ R) :
    IsAdmissibleMetric (enlargedBallNormalizedMetric g R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact (hg.smooth i j).comp ((R • ContinuousLinearMap.id ℝ R3).contDiff)
  · intro x
    exact hg.posDef (R • x)
  · intro x hx
    have hR0 : 0 ≤ R := le_trans zero_le_one hR
    have hnorm : 1 ≤ ‖R • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR0]
      calc
        1 ≤ ‖x‖ := hx
        _ = 1*‖x‖ := (one_mul ‖x‖).symm
        _ ≤ R*‖x‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg x)
    exact hg.euclidean_exterior (R • x) hnorm

theorem enlargedBallNormalizedMetric_one (g : MatrixField) :
    enlargedBallNormalizedMetric g 1 = g := by
  funext x
  simp only [enlargedBallNormalizedMetric, one_smul]

theorem vol_enlargedBallNormalizedMetric (g : MatrixField) (R : ℝ) (x : R3) :
    vol (enlargedBallNormalizedMetric g R) x = vol g (R • x) := rfl

theorem principalCoefficient_enlargedBallNormalizedMetric
    (g : MatrixField) (R : ℝ) (x : R3) :
    principalCoefficient (enlargedBallNormalizedMetric g R) x =
      principalCoefficient g (R • x) := rfl

theorem contDiff_principalCoefficient_enlargedBallNormalizedMetric_joint
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ContDiff ℝ ∞ (fun p : ℝ × R3 =>
      principalCoefficient (enlargedBallNormalizedMetric g p.1) p.2) :=
  (contDiff_principalCoefficient_of_smooth_posDef g hg.smooth hg.posDef).comp
    (contDiff_fst.smul contDiff_snd)

theorem coordinateFluxDivergence_enlargedBallNormalizedMetric_dilation
    (g : MatrixField) (hg : IsAdmissibleMetric g) (R : ℝ) (u : SmoothData) (x : R3) :
    coordinateFluxDivergence
      (metricDivergenceFlux (enlargedBallNormalizedMetric g R) (fun y : R3 => u.1 (R • y))) x =
      R^2 * coordinateFluxDivergence (metricDivergenceFlux g u.1) (R • x) :=
  coordinateFluxDivergence_metricDivergenceFlux_dilation g hg R u x

theorem metricHarmonic_enlargedBall_of_normalized_unitBall
    (g : MatrixField) (hg : IsAdmissibleMetric g) (R : ℝ) (hR : 0 < R) (v : SmoothData)
    (hv : ∀ z : R3, ‖z‖ < 1 →
      coordinateFluxDivergence (metricDivergenceFlux (enlargedBallNormalizedMetric g R) v.1) z = 0) :
    ∀ x : R3, ‖x‖ < R → coordinateFluxDivergence
      (metricDivergenceFlux g (fun y : R3 => v.1 (R⁻¹ • y))) x = 0 := by
  let u : SmoothData := ⟨fun y : R3 => v.1 (R⁻¹ • y),
    v.2.comp ((R⁻¹ • ContinuousLinearMap.id ℝ R3).contDiff)⟩
  have hPull : (fun z : R3 => u.1 (R • z)) = v.1 := by
    funext z
    change v.1 (R⁻¹ • (R • z)) = v.1 z
    rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  intro x hx
  let z : R3 := R⁻¹ • x
  have hzx : R • z = x := by
    dsimp only [z]
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hzNorm : ‖z‖ < 1 := by
    dsimp only [z]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    calc
      R⁻¹*‖x‖ < R⁻¹*R := mul_lt_mul_of_pos_left hx (inv_pos.mpr hR)
      _ = 1 := inv_mul_cancel₀ hR.ne'
  have hEq := coordinateFluxDivergence_enlargedBallNormalizedMetric_dilation g hg R u z
  rw [hPull] at hEq
  have h0 : 0 = R^2 * coordinateFluxDivergence (metricDivergenceFlux g u.1) (R • z) :=
    (hv z hzNorm).symm.trans hEq
  have hZero : coordinateFluxDivergence (metricDivergenceFlux g u.1) (R • z) = 0 :=
    (mul_eq_zero.mp h0.symm).resolve_left (pow_ne_zero 2 hR.ne')
  exact (congrArg (fun y : R3 => coordinateFluxDivergence (metricDivergenceFlux g u.1) y) hzx).symm.trans hZero

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.enlargedBallNormalizedMetric
#print axioms OAI.AnisotropicCalderon.ConnectionError.isAdmissibleMetric_enlargedBallNormalizedMetric
#print axioms OAI.AnisotropicCalderon.ConnectionError.enlargedBallNormalizedMetric_one
#print axioms OAI.AnisotropicCalderon.ConnectionError.vol_enlargedBallNormalizedMetric
#print axioms OAI.AnisotropicCalderon.ConnectionError.principalCoefficient_enlargedBallNormalizedMetric
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_principalCoefficient_enlargedBallNormalizedMetric_joint
#print axioms OAI.AnisotropicCalderon.ConnectionError.coordinateFluxDivergence_enlargedBallNormalizedMetric_dilation
#print axioms OAI.AnisotropicCalderon.ConnectionError.metricHarmonic_enlargedBall_of_normalized_unitBall
