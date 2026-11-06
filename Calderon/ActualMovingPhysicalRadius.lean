import Calderon.MovingRadiusChainRule

/-! Additive actual moving-profile identity. The genuine radial
profile derivative and frame connection direction are retained. No Psi/E/F
operator claim or harmonic-PDE transport assumption is made. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator NormalCoordinatesFrame

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
  (hEnd : ConformalReferenceGeodesicEndpointData g L y0 Φ B)
include hg hEnd

theorem hasDerivAt_referencePhysicalSphereValue_radius
    (q : ℝ) (y z : R3) (r : ℝ) (u : SmoothData) :
    HasDerivAt (fun t : ℝ => u.1
      (referenceFramedPhysicalEndpoint g L Φ (q,((y,t),z))))
      (fderiv ℝ u.1 (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z)))
        (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)) z)) r := by
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hEnd.2.2.2.2.2.2.2.1
  let Θ : R3 × R3 → R3 := fun p => (Φ q p 1).1
  let F : R3 →L[ℝ] R3 := conformalReferenceGramFrameOperatorJoint g L (q,y)
  have hΘq : ContDiff ℝ ∞ Θ := hΘ.comp (contDiff_const.prodMk contDiff_id)
  have hCurve : HasDerivAt (fun t : ℝ => (y,t • F z)) (0,F z) r := by
    convert (hasDerivAt_const r y).prodMk ((hasDerivAt_id r).smul_const (F z)) using 1 <;>
      simp only [id_eq,one_smul]
  have hΘDeriv : HasFDerivAt Θ (fderiv ℝ Θ (y,r • F z)) (y,r • F z) :=
    (hΘq.differentiable (by simp) (y,r • F z)).hasFDerivAt
  have hX : HasDerivAt (fun t : ℝ => Θ (y,t • F z))
      (fderiv ℝ Θ (y,r • F z) (0,F z)) r := by
    change HasDerivAt (Θ ∘ (fun t : ℝ => (y,t • F z)))
      (fderiv ℝ Θ (y,r • F z) (0,F z)) r
    exact HasFDerivAt.comp_hasDerivAt (l := Θ)
      (f := fun t : ℝ => (y,t • F z)) r hΘDeriv hCurve
  have hU := (u.2.differentiable (by simp) (Θ (y,r • F z))).hasFDerivAt.comp_hasDerivAt r hX
  exact hU

theorem deriv_referencePhysicalSphereValue_radius
    (q : ℝ) (y z : R3) (r : ℝ) (hr : r ≠ 0) (u : SmoothData) :
    deriv (fun t : ℝ => u.1
      (referenceFramedPhysicalEndpoint g L Φ (q,((y,t),z)))) r =
      r⁻¹ * fderiv ℝ (referencePhysicalPullbackData g hg L y0 Φ B hEnd q y r u).1 z z := by
  rw [(hasDerivAt_referencePhysicalSphereValue_radius g hg L y0 Φ B hEnd q y z r u).deriv,
    fderiv_referencePhysicalPullbackData g hg L y0 Φ B hEnd q y z z r u,map_smul]
  simp only [smul_eq_mul]
  field_simp [hr]

theorem fderiv_referencePhysicalSphereValue_moving_radius_horizontal
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y z : R3) (hy : (y,0) ∈ B)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (hr : R y ≠ 0)
    (i : Fin 3) (u : SmoothData)
    (hInv : (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),z))).IsInvertible) :
    let F : R3 → R3 →L[ℝ] R3 := fun x => conformalReferenceGramFrameOperatorJoint g L (q,x)
    let Γ := coordinateConnectionField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
      (metricOperatorField (conformalReferenceMatrix g L q))
    fderiv ℝ (fun p : R3 × R3 => u.1
      (referenceFramedPhysicalEndpoint g L Φ (q,((p.1,R p.1),p.2)))) (y,z)
      (F y (coordinateVector i),framedParallelAngularVelocity F Γ y (F y (coordinateVector i)) z) =
      (R y)⁻¹ * fderiv ℝ (referencePhysicalPullbackData g hg L y0 Φ B hEnd q y (R y) u).1 z
        (coordinateVector i) +
      R y * fderiv ℝ (referencePhysicalPullbackData g hg L y0 Φ B hEnd q y (R y) u).1 z
        (referenceFramedJacobiVelocityRemainder g L Φ i (q,((y,R y),z))) +
      fderiv ℝ (fun x => Real.log (R x)) y (F y (coordinateVector i)) *
        fderiv ℝ (referencePhysicalPullbackData g hg L y0 Φ B hEnd q y (R y) u).1 z z := by
  dsimp only
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hEnd.2.2.2.2.2.2.2.1
  let f : (R3 × ℝ) × R3 → ℝ := fun p => u.1 (referenceFramedPhysicalEndpoint g L Φ (q,p))
  have hf : ContDiff ℝ ∞ f := u.2.comp
    ((contDiff_referenceFramedPhysicalEndpoint g hg L Φ hΘ).comp
      (contDiff_const.prodMk contDiff_id))
  rw [fderiv_movingRadius_comp f hf R hR y z
    (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i))
    (framedParallelAngularVelocity (fun x => conformalReferenceGramFrameOperatorJoint g L (q,x))
      (coordinateConnectionField
        (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
        (metricOperatorField (conformalReferenceMatrix g L q))) y
      (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)) z)]
  rw [fderiv_referencePhysicalSphereValue_center_horizontal_decomposition
    g hg L y0 Φ B hEnd q hq y z hy (R y) hr i u hInv,
    deriv_referencePhysicalSphereValue_radius g hg L y0 Φ B hEnd q y z (R y) hr u,
    fderiv_log_radius_apply R hR y
      (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)) hr]
  ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
