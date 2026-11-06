import Calderon.MixedKernelConstruction.MixedKernelActualNormalizedOperatorDictionary
import Calderon.WeightedRaisingBounds
import Calderon.CompactParameterReferenceFramedNormalMetric
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError MetricOperator MetricVolume ConformalDepth
open NormalCoordinatesFrame ReferenceWeightedApproximation
open RadiusProfile ActualScalarPrincipalAdjoint
open scoped ContDiff Topology InnerProductSpace

/-- The literal coordinate vector of the actual frame covector. -/
def profileFrameCovectorVector (f : R3 → ℝ) (F : R3 →L[ℝ] R3) (y : R3) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 => fderiv ℝ f y (F (MetricVolume.coordinateVector i)))

/-- The SAME vector represents the full frame covector by true coordinate linearity. -/
theorem inner_profileFrameCovectorVector
    (f : R3 → ℝ) (F : R3 →L[ℝ] R3) (y eta : R3) :
    ⟪profileFrameCovectorVector f F y,eta⟫_ℝ=fderiv ℝ f y (F eta) := by
  have h := covector_coordinate_sum ((fderiv ℝ f y).comp F) eta
  change fderiv ℝ f y (F eta)=∑ i : Fin 3, eta i*fderiv ℝ f y (F (MetricVolume.coordinateVector i)) at h
  rw [h]
  simp only [profileFrameCovectorVector,EuclideanSpace.inner_eq_star_dotProduct,
    Pi.star_apply,star_trivial,WithLp.ofLp_toLp,dotProduct,ContinuousLinearMap.comp_apply]

/-- The frame covector's norm is EXACTLY the actual metric differential norm. -/
theorem norm_profileFrameCovectorVector_eq_metricDifferentialNorm
    (g : MatrixField) (hp : ∀ x, (g x).PosDef) (f : R3 → ℝ)
    (F : R3 →L[ℝ] R3) (y : R3)
    (hF : RadiusProfile.IsMetricOrthonormalFrame (metricOperatorField g y) (fun i => F (MetricVolume.coordinateVector i))) :
    ‖profileFrameCovectorVector f F y‖=metricDifferentialNorm g f y := by
  have hMetric := WeightedRaisingBounds.metricDifferentialNorm_sq_eq_frame_sum g hp f y _ hF
  have hVector := EuclideanSpace.real_norm_sq_eq (profileFrameCovectorVector f F y)
  change ‖profileFrameCovectorVector f F y‖^2=∑ i : Fin 3, (fderiv ℝ f y (F (MetricVolume.coordinateVector i)))^2 at hVector
  have hb : 0 ≤ metricDifferentialNorm g f y := Real.sqrt_nonneg _
  nlinarith only [hMetric,hVector,norm_nonneg (profileFrameCovectorVector f F y),hb]

/-- The actual logarithmic chain rule gives the exact radius factor. -/
theorem profileFrameCovectorVector_eq_mul_log
    (r : R3 → ℝ) (F : R3 →L[ℝ] R3) (y : R3)
    (hr : DifferentiableAt ℝ r y) (hrpos : 0 < r y) :
    profileFrameCovectorVector r F y=r y • profileFrameCovectorVector (fun Y => Real.log (r Y)) F y := by
  have hlog := (hr.hasFDerivAt.log hrpos.ne').fderiv
  ext i
  change fderiv ℝ r y (F (MetricVolume.coordinateVector i))=
    r y*fderiv ℝ (fun Y => Real.log (r Y)) y (F (MetricVolume.coordinateVector i))
  rw [hlog]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  field_simp [hrpos.ne'] <;> ring

/-- The native frame radius gradient has norm r times the ORIGINAL beta. -/
theorem norm_actual_radius_frame_covector_eq_radius_mul_beta
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar) (y : R3) :
    let r := referenceRadius delta Rstar p L
    let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
    ‖profileFrameCovectorVector r F y‖=r y*actualReferenceBeta S.g1 L lam delta Rstar p y := by
  intro r F
  have hr := contDiff_referenceRadius_actual delta Rstar p L hdelta hRstar
  have hrpos : 0 < r y := referenceRadius_pos delta Rstar p L y hdelta hRstar
  rw [profileFrameCovectorVector_eq_mul_log r F y (hr.differentiable (by simp) y) hrpos,
    norm_smul,Real.norm_eq_abs,abs_of_pos hrpos]
  congr 1
  let g := referenceMetric (dilatedMetric S.g1 lam) L
  have hp (Y : R3) : (g Y).PosDef :=
    EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef S.g1 S.g1_admissible lam) Y
  have hF : RadiusProfile.IsMetricOrthonormalFrame (metricOperatorField g y) (fun i => F (MetricVolume.coordinateVector i)) := by
    have hgEq : g=conformalReferenceMatrix S.g1 L lam := referenceMetric_eq_conformalReferenceMatrix S.g1 L lam
    rw [hgEq]
    change RadiusProfile.IsMetricOrthonormalFrame (conformalReferenceOperatorJoint S.g1 L (lam,y))
      (fun i => frameOperator (metricGramFrame (conformalReferenceOperatorJoint S.g1 L (lam,y))) (NormalCoordinatesFrame.coordinateVector i))
    simp only [frameOperator_coordinateVector]
    exact NormalCoordinatesFrame.metricGramFrame_isMetricOrthonormalFrame _
      (conformalReferenceOperatorJoint_symmetric S.g1 S.g1_admissible L (lam,y))
      (conformalReferenceOperatorJoint_pos S.g1 S.g1_admissible L (lam,y))
  exact norm_profileFrameCovectorVector_eq_metricDifferentialNorm g hp (fun Y => Real.log (r Y)) F y hF

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
