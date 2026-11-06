import Calderon.ActualLowerMovingBoundaryAction
import Calderon.ActualJacobiBoundaryMultiplierFamily
import Calderon.ActualReferenceRadialEndpointInvertibleTopology

/-! Full upfront: EXPANSION-ActualLowerMovingBoundaryFamily-v001.md.
The SAME actual lower action, with operator-norm parameter smoothness on its
original inverse locus. Arbitrary R remains explicit. No moving estimate. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeFullSharpHalfTrace
  NativeCoefficientBoundaryMultiplier NormalCoordinatesFrame

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem contDiffAt_referenceLowerCoordinateBoundaryFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => referenceLowerCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t i) p := by
  have hRad := contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hNormal hWeak
  exact contDiffAt_const.add (contDiffAt_const.clm_comp hRad)

variable (hg : IsAdmissibleMetric g)

def referenceLowerJacobiBoundaryCorrectionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  ∑ j : Fin 3, (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceJacobiBoundaryCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData i j p)).comp
        (referenceLowerCoordinateBoundaryFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p j)

theorem referenceLowerJacobiBoundaryCorrectionFamily_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible) :
    referenceLowerJacobiBoundaryCorrectionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p i =
    referenceLowerJacobiBoundaryCorrection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p.1 p.2.1 p.2.2 i hInv := by
  unfold referenceLowerJacobiBoundaryCorrectionFamily referenceLowerJacobiBoundaryCorrection
  apply Finset.sum_congr rfl
  intro j hj
  rw [referenceJacobiBoundaryCoefficientFamily_eq
    g hg L y0 Φ B ε C ρ H a w hData i j p hInv]

theorem contDiffAt_referenceLowerJacobiBoundaryCorrectionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => referenceLowerJacobiBoundaryCorrectionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t i) p := by
  apply ContDiffAt.sum
  intro j hj
  exact (contDiffAt_nativeNegativeHalf_referenceJacobiBoundaryCoefficientFamily
    g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hInv).clm_comp
      (contDiffAt_referenceLowerCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p j hNormal hWeak)

def referenceLowerCenterBoundaryActionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  p.2.2⁻¹ • referenceLowerCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i +
  p.2.2 • referenceLowerJacobiBoundaryCorrectionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p i

theorem referenceLowerCenterBoundaryActionFamily_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible) :
    referenceLowerCenterBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p i =
    referenceLowerCenterBoundaryAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p.1 p.2.1 p.2.2 i hInv := by
  unfold referenceLowerCenterBoundaryActionFamily referenceLowerCenterBoundaryAction
  rw [referenceLowerJacobiBoundaryCorrectionFamily_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p i hInv]

theorem contDiffAt_referenceLowerCenterBoundaryActionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (i : Fin 3) (hr : p.2.2 ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t => referenceLowerCenterBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t i) p := by
  have hRadius : ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) => t.2.2) p :=
    contDiffAt_snd.snd
  have hQ := contDiffAt_referenceLowerCoordinateBoundaryFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p i hNormal hWeak
  have hJ := contDiffAt_referenceLowerJacobiBoundaryCorrectionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p i hInv hNormal hWeak
  exact ((hRadius.inv hr).smul hQ).add (hRadius.smul hJ)

include hg in
theorem contDiffAt_referenceRadiusHorizontalLogDerivative
    (R : R3 → ℝ) (p : ℝ × R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R p.2) (hr : R p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : ℝ × R3 =>
      referenceRadiusHorizontalLogDerivative g L t.1 R t.2 i) p := by
  have hLog : ContDiffAt ℝ ∞ (fun y => Real.log (R y)) p.2 := hR.log hr
  have hDerivative : ContDiffAt ℝ ∞ (fun t : ℝ × R3 =>
      fderiv ℝ (fun y => Real.log (R y)) t.2) p :=
    (hLog.fderiv_right (m := ∞) (by simp)).comp p contDiffAt_snd
  have hFrame : ContDiffAt ℝ ∞ (fun t : ℝ × R3 =>
      conformalReferenceGramFrameOperatorJoint g L t (coordinateVector i)) p :=
    (contDiff_conformalReferenceGramFrameOperatorJoint g hg L).contDiffAt.clm_apply
      contDiffAt_const
  exact hDerivative.clm_apply hFrame

def referenceLowerMovingBoundaryActionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  referenceLowerCenterBoundaryActionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (t.1,(t.2,R t.2)) i +
  referenceRadiusHorizontalLogDerivative g L t.1 R t.2 i •
    referenceLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (t.1,(t.2,R t.2))

theorem referenceLowerMovingBoundaryActionFamily_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (t.1,((t.2,R t.2),x.val))).IsInvertible) :
    referenceLowerMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R t i =
    referenceLowerMovingBoundaryAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t.1 R t.2 i hInv := by
  unfold referenceLowerMovingBoundaryActionFamily referenceLowerMovingBoundaryAction
  rw [referenceLowerCenterBoundaryActionFamily_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (t.1,(t.2,R t.2)) i hInv]

attribute [local irreducible] referenceLowerCenterBoundaryActionFamily
  referenceLowerRadialEndpointFamily

theorem contDiffAt_referenceLowerMovingBoundaryActionFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (R : R3 → ℝ) (t : ℝ × R3) (i : Fin 3)
    (hR : ContDiffAt ℝ ∞ R t.2) (hr : R t.2 ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (t.1,((t.2,R t.2),x.val))).IsInvertible)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (t.1,(t.2,R t.2))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (t.1,(t.2,R t.2))).IsInvertible) :
    ContDiffAt ℝ ∞ (fun s => referenceLowerMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R s i) t := by
  let T : ℝ × R3 → ℝ × (R3 × ℝ) := fun s => (s.1,(s.2,R s.2))
  have hT : ContDiffAt ℝ ∞ T t :=
    contDiffAt_fst.prodMk (contDiffAt_snd.prodMk (hR.comp t contDiffAt_snd))
  have hCenter := (contDiffAt_referenceLowerCenterBoundaryActionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      (t.1,(t.2,R t.2)) i hr hInv hNormal hWeak).comp t hT
  have hRad := (contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      (t.1,(t.2,R t.2)) hNormal hWeak).comp t hT
  have hCoefficient := contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R t i hR hr
  simpa only [referenceLowerMovingBoundaryActionFamily,Function.comp_def,Pi.smul_apply',T] using
    hCenter.add (hCoefficient.smul hRad)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceLowerCoordinateBoundaryFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerJacobiBoundaryCorrectionFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerJacobiBoundaryCorrectionFamily_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceLowerJacobiBoundaryCorrectionFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerCenterBoundaryActionFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerCenterBoundaryActionFamily_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceLowerCenterBoundaryActionFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRadiusHorizontalLogDerivative
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerMovingBoundaryActionFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerMovingBoundaryActionFamily_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceLowerMovingBoundaryActionFamily
