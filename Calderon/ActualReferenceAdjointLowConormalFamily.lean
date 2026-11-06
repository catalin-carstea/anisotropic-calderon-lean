import Calderon.ActualNativeAdjointWeakHalfLift
import Calderon.NativeCoefficientWeakConormalEndpoint

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceAdjointWeakConormalEndpointFamily (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  nativeWeakConormalEndpoint (fun x => (a (p,x))ᵀ)
    (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
    (fun x => -nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)
    (memLp_referenceAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData p) hF

def referenceAdjointWeakConormalFunctionalFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) : SphereSobolev (1/2:ℝ) →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ)) :=
  sphereSurfaceMass⁻¹ •
    (referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).bilinearComp
      (referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p)
      (harmonicFirstOrderLiftCompletion hF)

lemma referenceAdjointWeakConormalFunctionalFamily_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (f z : SphereSobolev (1/2:ℝ)) :
    referenceAdjointWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f z =
      sphereSurfaceMass⁻¹ * referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
        (referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
        (harmonicFirstOrderLiftCompletion hF z) := by
  rfl

lemma referenceAdjointWeakConormalEndpointFamily_eq_formula
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    referenceAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF p =
      (sphereSobolevDualRieszL (1/2:ℝ)).comp
        (referenceAdjointWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro z
  change sphereSobolevDualPairing (1/2:ℝ) z _ = sphereSobolevDualPairing (1/2:ℝ) z _
  have hNative := sphereSobolevDualPairing_nativeWeakConormalEndpoint (fun x => (a (p,x))ᵀ)
    (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
    (fun x => -nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)
    (memLp_referenceAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData p) hF f z
  have hW := referenceAdjointWeakHalfLiftFamily_eq_native g L y0 Φ B ε C ρ H a w hData
    τ0 hcalc hF p hOriginal f
  have hCo := congrArg (fun u : BallH1 => sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) (fun x => (a (p,x))ᵀ)
    (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
    (fun x => -nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)
    u (harmonicFirstOrderLiftCompletion hF z)) hW.symm
  have hE := congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t)
    (referenceAdjointFullWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p
      (referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
      (harmonicFirstOrderLiftCompletion hF z))
  have hR := (sphereSobolevDualPairing_dualRiesz (1/2:ℝ)
    (referenceAdjointWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) z).trans
      (referenceAdjointWeakConormalFunctionalFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc hF p f z)
  exact (hNative.trans hCo).trans (hE.symm.trans hR.symm)

lemma contDiffOn_referenceAdjointWeakConormalFunctionalFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiffOn ℝ ∞ (referenceAdjointWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  let Q : StrongDual ℝ BallH1 →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ)) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) BallH1 ℝ).flip
      (harmonicFirstOrderLiftCompletion hF)
  have hEW : ContDiffOn ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      (referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).comp
        (referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p))
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    (contDiff_referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc).contDiffOn.clm_comp
      (contDiffOn_referenceAdjointWeakHalfLiftFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0)
  change ContDiffOn ℝ ∞ (fun p : ℝ × (R3 × ℝ) => sphereSurfaceMass⁻¹ •
    Q.comp ((referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).comp
      (referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p))) _
  have hQ : ContDiffOn ℝ ∞ (fun _ : ℝ × (R3 × ℝ) => Q)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    contDiffOn_const
  have hPost : ContDiffOn ℝ ∞ (fun p : ℝ × (R3 × ℝ) => Q.comp
      ((referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).comp
        (referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p)))
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    hQ.clm_comp hEW
  have hMass : ContDiffOn ℝ ∞ (fun _ : ℝ × (R3 × ℝ) => (sphereSurfaceMass⁻¹ : ℝ))
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    contDiffOn_const
  exact hMass.smul hPost

lemma contDiffOn_referenceAdjointWeakConormalEndpointFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiffOn ℝ ∞ (referenceAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  have hRiesz : ContDiffOn ℝ ∞
      (fun _ : ℝ × (R3 × ℝ) => sphereSobolevDualRieszL (1/2:ℝ))
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    contDiffOn_const
  have hFormula : ContDiffOn ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      (sphereSobolevDualRieszL (1/2:ℝ)).comp
        (referenceAdjointWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p))
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    hRiesz.clm_comp
      (contDiffOn_referenceAdjointWeakConormalFunctionalFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0)
  apply hFormula.congr
  intro p hp
  exact referenceAdjointWeakConormalEndpointFamily_eq_formula g L y0 Φ B ε C ρ H a w hData
    τ0 hcalc hF p hp.2.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakConormalEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakConormalFunctionalFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakConormalFunctionalFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakConormalEndpointFamily_eq_formula
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceAdjointWeakConormalFunctionalFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceAdjointWeakConormalEndpointFamily_invertibleLocus
