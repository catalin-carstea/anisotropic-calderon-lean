import Calderon.ActualFramedJacobiVelocityRemainder
import Calderon.NativeReferenceHarmonicBoundary

/-! Exact smooth same-witness physical/native trace correspondence. -/
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

def referencePhysicalPullbackData (q : ℝ) (y : R3) (r : ℝ) (u : SmoothData) : SmoothData := by
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hEnd.2.2.2.2.2.2.2.1
  refine ⟨fun z => u.1 (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z))),?_⟩
  exact u.2.comp ((contDiff_referenceFramedPhysicalEndpoint g hg L Φ hΘ).comp
    (contDiff_const.prodMk ((contDiff_const.prodMk contDiff_const).prodMk contDiff_id)))

theorem smoothSphereValue_referencePhysicalPullback_apply
    (q : ℝ) (y : R3) (r : ℝ) (u : SmoothData) (x : UnitSphere) :
    smoothSphereValue (referencePhysicalPullbackData g hg L y0 Φ B hEnd q y r u) x =
      u.1 (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x.val))) := rfl

theorem fderiv_referencePhysicalPullbackData
    (q : ℝ) (y z W : R3) (r : ℝ) (u : SmoothData) :
    fderiv ℝ (referencePhysicalPullbackData g hg L y0 Φ B hEnd q y r u).1 z W =
      fderiv ℝ u.1 (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z)))
        (r • referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)) W) := by
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hEnd.2.2.2.2.2.2.2.1
  have hX : HasFDerivAt (fun v : R3 => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),v)))
      (r • referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))) z :=
    hasFDerivAt_framedScaledEndpoint_slice (fun p => (Φ q p 1).1)
      (fun x => conformalReferenceGramFrameOperatorJoint g L (q,x))
      (hΘ.comp (contDiff_const.prodMk contDiff_id)) y z r
  have hd := (u.2.differentiable (by simp)
    (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z)))).hasFDerivAt.comp z hX
  change fderiv ℝ (u.1 ∘ (fun v : R3 =>
    referenceFramedPhysicalEndpoint g L Φ (q,((y,r),v)))) z W = _
  rw [hd.fderiv]
  rfl

theorem smoothRadialSphere_referencePhysicalPullback_apply
    (q : ℝ) (y : R3) (r : ℝ) (u : SmoothData) (x : UnitSphere) :
    smoothRadialSphere (referencePhysicalPullbackData g hg L y0 Φ B hEnd q y r u) x =
      fderiv ℝ u.1 (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x.val)))
        (r • referenceFramedNormalizedJacobian g L Φ (q,((y,r),x.val)) x.val) :=
  fderiv_referencePhysicalPullbackData g hg L y0 Φ B hEnd q y x.val x.val r u

theorem strongValueTraceL_referencePhysicalPullback
    (τ0 : UnitBallValueTrace) (s : ℕ) (q : ℝ) (y : R3) (r : ℝ) (u : SmoothData) :
    strongValueTraceL τ0 s
      (smoothBallSobolev (s+2) (referencePhysicalPullbackData g hg L y0 Φ B hEnd q y r u)) =
      (ContinuousMap.toLp 2 sphereProbability ℝ)
        (smoothSphereValue (referencePhysicalPullbackData g hg L y0 Φ B hEnd q y r u)) :=
  strongValueTraceL_smooth τ0 s _

theorem outwardRadialTraceL_referencePhysicalPullback
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (r : ℝ) (u : SmoothData) :
    outwardRadialTraceL hcalc τ0
      (smoothBallSobolev 2 (referencePhysicalPullbackData g hg L y0 Φ B hEnd q y r u)) =
      (ContinuousMap.toLp 2 sphereProbability ℝ)
        (smoothRadialSphere (referencePhysicalPullbackData g hg L y0 Φ B hEnd q y r u)) :=
  outwardRadialTraceL_smoothBallSobolev hcalc τ0 _

theorem fderiv_referencePhysicalSphereValue_center_horizontal
    (q : ℝ) (y z : R3) (r : ℝ) (i : Fin 3) (u : SmoothData) :
    let F : R3 → R3 →L[ℝ] R3 := fun x => conformalReferenceGramFrameOperatorJoint g L (q,x)
    let Γ := coordinateConnectionField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
      (metricOperatorField (conformalReferenceMatrix g L q))
    fderiv ℝ (fun p : R3 × R3 => u.1
      (referenceFramedPhysicalEndpoint g L Φ (q,((p.1,r),p.2)))) (y,z)
      (F y (coordinateVector i),framedParallelAngularVelocity F Γ y (F y (coordinateVector i)) z) =
      fderiv ℝ u.1 (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z)))
        (referenceFramedCenterHorizontalVelocity g L Φ i (q,((y,r),z))) := by
  dsimp only
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hEnd.2.2.2.2.2.2.2.1
  let f : R3 × R3 → R3 := fun p => referenceFramedPhysicalEndpoint g L Φ (q,((p.1,r),p.2))
  have hf : ContDiff ℝ ∞ f := (contDiff_referenceFramedPhysicalEndpoint g hg L Φ hΘ).comp
    (contDiff_const.prodMk ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd))
  have hd := (u.2.differentiable (by simp) (f (y,z))).hasFDerivAt.comp (y,z)
    (hf.differentiable (by simp) (y,z)).hasFDerivAt
  change fderiv ℝ (u.1 ∘ f) (y,z)
    (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i),
      framedParallelAngularVelocity (fun x => conformalReferenceGramFrameOperatorJoint g L (q,x))
        (coordinateConnectionField
          (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
          (metricOperatorField (conformalReferenceMatrix g L q))) y
        (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)) z) = _
  rw [hd.fderiv]
  change fderiv ℝ u.1 (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z)))
    (fderiv ℝ f (y,z)
      (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i),
        framedParallelAngularVelocity (fun x => conformalReferenceGramFrameOperatorJoint g L (q,x))
          (coordinateConnectionField
            (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
            (metricOperatorField (conformalReferenceMatrix g L q))) y
          (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)) z)) = _
  rw [referenceFramedPhysicalEndpoint_center_horizontal g hg L Φ hΘ q y z r i]

theorem fderiv_referencePhysicalSphereValue_center_horizontal_decomposition
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y z : R3) (hy : (y,0) ∈ B)
    (r : ℝ) (hr : r ≠ 0) (i : Fin 3) (u : SmoothData)
    (hInv : (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))).IsInvertible) :
    let F : R3 → R3 →L[ℝ] R3 := fun x => conformalReferenceGramFrameOperatorJoint g L (q,x)
    let Γ := coordinateConnectionField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
      (metricOperatorField (conformalReferenceMatrix g L q))
    fderiv ℝ (fun p : R3 × R3 => u.1
      (referenceFramedPhysicalEndpoint g L Φ (q,((p.1,r),p.2)))) (y,z)
      (F y (coordinateVector i),framedParallelAngularVelocity F Γ y (F y (coordinateVector i)) z) =
      r⁻¹ * fderiv ℝ (referencePhysicalPullbackData g hg L y0 Φ B hEnd q y r u).1 z
        (coordinateVector i) +
      r * fderiv ℝ (referencePhysicalPullbackData g hg L y0 Φ B hEnd q y r u).1 z
        (referenceFramedJacobiVelocityRemainder g L Φ i (q,((y,r),z))) := by
  dsimp only
  rw [fderiv_referencePhysicalSphereValue_center_horizontal g hg L y0 Φ B hEnd q y z r i u]
  have hJac := referenceFramedCenterHorizontalVelocity_inverse_quadratic
    g hg L y0 Φ B hEnd q hq y hy r z i hInv
  have hK : referenceFramedCenterHorizontalVelocity g L Φ i (q,((y,r),z)) =
      referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)) (coordinateVector i) +
        r^2 • referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))
          (referenceFramedJacobiVelocityRemainder g L Φ i (q,((y,r),z))) := by
    have h := congrArg (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))) hJac
    rw [hInv.self_apply_inverse] at h
    simpa only [map_add,map_smul] using h
  rw [fderiv_referencePhysicalPullbackData g hg L y0 Φ B hEnd q y z (coordinateVector i) r u,
    fderiv_referencePhysicalPullbackData g hg L y0 Φ B hEnd q y z
      (referenceFramedJacobiVelocityRemainder g L Φ i (q,((y,r),z))) r u,
    hK,map_add,map_smul]
  simp only [map_smul,smul_eq_mul]
  field_simp [hr]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
