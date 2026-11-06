import Calderon.ActualHighMovingBoundaryAction
import Calderon.ActualJacobiBoundaryMultiplierFamily
import Calderon.ActualReferenceRadialEndpointInvertibleTopology
import Calderon.ActualLowerMovingBoundaryFamily

/-! Full upfront: day-oct13/actual-moving-boundary-family-author-oct15-v001/
EXPANSION-high-family.md. Literal actual H3/2 to H1/2 family.
Chosen Jacobi jet smoothness is not assumed. No physical P claim. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeFullSharpHalfTrace
  NativeCoefficientBoundaryMultiplier NormalCoordinatesFrame

attribute [local irreducible] referenceSharpRadialTraceFamily
  referenceJacobiBoundaryCoefficientFamily referenceJacobiBoundaryCoefficientJets
  referenceHighCoordinateBoundaryFamily nativeHalfCoefficientMulL

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem contDiffAt_referenceHighCoordinateBoundaryFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => referenceHighCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t i) p := by
  have hRad := contDiffAt_referenceSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hStrong
  unfold referenceHighCoordinateBoundaryFamily
  exact contDiffAt_const.add (contDiffAt_const.clm_comp hRad)

variable (hg : IsAdmissibleMetric g)

def referenceHighJacobiBoundaryCorrectionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  ∑ j : Fin 3, (nativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceJacobiBoundaryCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData i j p)).comp
        (referenceHighCoordinateBoundaryFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p j)

theorem referenceHighJacobiBoundaryCorrectionFamily_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible) :
    referenceHighJacobiBoundaryCorrectionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p i =
    referenceHighJacobiBoundaryCorrection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p.1 p.2.1 p.2.2 i hInv := by
  unfold referenceHighJacobiBoundaryCorrectionFamily referenceHighJacobiBoundaryCorrection
  apply Finset.sum_congr rfl
  intro j hj
  rw [referenceJacobiBoundaryCoefficientFamily_eq
    g hg L y0 Φ B ε C ρ H a w hData i j p hInv]

theorem contDiffAt_referenceHighJacobiBoundaryCorrectionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => referenceHighJacobiBoundaryCorrectionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t i) p := by
  apply ContDiffAt.sum
  intro j hj
  exact (contDiffAt_nativeHalf_referenceJacobiBoundaryCoefficientFamily
    g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hInv).clm_comp
      (contDiffAt_referenceHighCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p j hStrong)

def referenceHighCenterBoundaryActionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  p.2.2⁻¹ • referenceHighCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i +
  p.2.2 • referenceHighJacobiBoundaryCorrectionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p i

theorem referenceHighCenterBoundaryActionFamily_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible) :
    referenceHighCenterBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p i =
    referenceHighCenterBoundaryAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p.1 p.2.1 p.2.2 i hInv := by
  unfold referenceHighCenterBoundaryActionFamily referenceHighCenterBoundaryAction
  rw [referenceHighJacobiBoundaryCorrectionFamily_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p i hInv]

theorem contDiffAt_referenceHighCenterBoundaryActionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3) (hr : p.2.2 ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => referenceHighCenterBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t i) p := by
  have hRadius : ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) => t.2.2) p :=
    contDiffAt_snd.snd
  have hQ := contDiffAt_referenceHighCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i hStrong
  have hJ := contDiffAt_referenceHighJacobiBoundaryCorrectionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p i hInv hStrong
  exact ((hRadius.inv hr).smul hQ).add (hRadius.smul hJ)

def referenceHighMovingBoundaryActionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  referenceHighCenterBoundaryActionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (t.1,(t.2,R t.2)) i +
  referenceRadiusHorizontalLogDerivative g L t.1 R t.2 i •
    referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (t.1,(t.2,R t.2))

theorem referenceHighMovingBoundaryActionFamily_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (t.1,((t.2,R t.2),x.val))).IsInvertible) :
    referenceHighMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R t i =
    referenceHighMovingBoundaryAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t.1 R t.2 i hInv := by
  unfold referenceHighMovingBoundaryActionFamily referenceHighMovingBoundaryAction
  rw [referenceHighCenterBoundaryActionFamily_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (t.1,(t.2,R t.2)) i hInv]

attribute [local irreducible] referenceHighCenterBoundaryActionFamily

theorem contDiffAt_referenceHighMovingBoundaryActionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R t.2) (hr : R t.2 ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (t.1,((t.2,R t.2),x.val))).IsInvertible)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 t.1 (t.2,R t.2)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun s => referenceHighMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R s i) t := by
  let T : ℝ × R3 → ℝ × (R3 × ℝ) := fun s => (s.1,(s.2,R s.2))
  have hT : ContDiffAt ℝ ∞ T t :=
    contDiffAt_fst.prodMk (contDiffAt_snd.prodMk (hR.comp t contDiffAt_snd))
  have hCenter := (contDiffAt_referenceHighCenterBoundaryActionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      (t.1,(t.2,R t.2)) i hr hInv hStrong).comp t hT
  have hRad := (contDiffAt_referenceSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      (t.1,(t.2,R t.2)) hStrong).comp t hT
  have hCoefficient := contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R t i hR hr
  simpa only [referenceHighMovingBoundaryActionFamily,Function.comp_def,Pi.smul_apply',T] using
    hCenter.add (hCoefficient.smul hRad)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighCoordinateBoundaryFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighJacobiBoundaryCorrectionFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighJacobiBoundaryCorrectionFamily_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighJacobiBoundaryCorrectionFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighCenterBoundaryActionFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighCenterBoundaryActionFamily_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighCenterBoundaryActionFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighMovingBoundaryActionFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighMovingBoundaryActionFamily_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighMovingBoundaryActionFamily
