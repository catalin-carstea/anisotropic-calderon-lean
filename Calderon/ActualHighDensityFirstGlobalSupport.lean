import Calderon.ActualHighDensityFirstWeightedConvergence
import Calderon.ActualPhysicalDensityOperatorLocality

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame ActualFiniteHarmonicCore
  ReferenceDensityBounds ConformalDepth WeightedBaseSpectral

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceHighDensityFirstAction referenceHighAdjointMovingBoundaryActionFamily
  referenceHighHorizontalAngularL referenceMetricGramFrame referenceRadialEndpointInvertibleLocus
  referenceFramedNormalizedJacobian

/-- Local regularity of the ORIGINAL first action is global for a compactly
supported source, with geometry required only on its support. -/
theorem contDiff_referenceHighDensityFirstAction_of_support
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (u : R3 → SphereSobolev (3/2:ℝ)) (hu : ContDiff ℝ ∞ u)
    (hGeometry : ∀ y ∈ tsupport u, R y ≠ 0 ∧
      (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      ∀ x : UnitSphere, (referenceFramedNormalizedJacobian
        g L Φ (q,((y,R y),x.val))).IsInvertible) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y => referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i) := by
  let X : R3 → SphereSobolev (1/2:ℝ) := fun y => referenceHighDensityFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i
  have hSupp : tsupport X ⊆ tsupport u := tsupport_referenceHighDensityFirstAction_subset
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u i
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ tsupport u
  · exact contDiffAt_referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R u y i
        hu.contDiffAt hR.contDiffAt (hGeometry y hy).1
        (hGeometry y hy).2.2 (hGeometry y hy).2.1
  · have hZero : X =ᶠ[𝓝 y] (fun _ => (0 : SphereSobolev (1/2:ℝ))) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (hSupp h))
    exact contDiffAt_const.congr_of_eventuallyEq hZero

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
