import Calderon.ActualNativeRotationAdjointWeakHalfLift
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

def referenceRotationAdjointWeakConormalEndpointFamily (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  nativeWeakConormalEndpoint (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
    (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    (fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
    (memLp_referenceRotationAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData i j t) hF

def referenceRotationAdjointWeakConormalFunctionalFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) : SphereSobolev (1/2:ℝ) →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ)) :=
  sphereSurfaceMass⁻¹ •
    (referenceRotationAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).bilinearComp
      (referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t)
      (harmonicFirstOrderLiftCompletion hF)

lemma referenceRotationAdjointWeakConormalFunctionalFamily_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (f z : SphereSobolev (1/2:ℝ)) :
    referenceRotationAdjointWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f z =
      sphereSurfaceMass⁻¹ * referenceRotationAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
        (referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f)
        (harmonicFirstOrderLiftCompletion hF z) := by
  rfl

lemma referenceRotationAdjointWeakConormalEndpointFamily_eq_formula
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible) :
    referenceRotationAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF i j t =
      (sphereSobolevDualRieszL (1/2:ℝ)).comp
        (referenceRotationAdjointWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℝ
  intro z
  change sphereSobolevDualPairing (1/2:ℝ) z _ = sphereSobolevDualPairing (1/2:ℝ) z _
  have hNative := sphereSobolevDualPairing_nativeWeakConormalEndpoint (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
    (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    (fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
    (memLp_referenceRotationAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData i j t) hF f z
  have hW := referenceRotationAdjointWeakHalfLiftFamily_eq_native g L y0 Φ B ε C ρ H a w hData
    τ0 hcalc hF i j t hOriginal f
  have hCo := congrArg (fun u : BallH1 => sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
    (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    (fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
    u (harmonicFirstOrderLiftCompletion hF z)) hW.symm
  have hE := congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t)
    (referenceRotationAdjointFullWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc i j t
      (referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f)
      (harmonicFirstOrderLiftCompletion hF z))
  have hR := (sphereSobolevDualPairing_dualRiesz (1/2:ℝ)
    (referenceRotationAdjointWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f) z).trans
      (referenceRotationAdjointWeakConormalFunctionalFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f z)
  exact (hNative.trans hCo).trans (hE.symm.trans hR.symm)

lemma contDiffOn_referenceRotationAdjointWeakConormalFunctionalFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (referenceRotationAdjointWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j)
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  let Q : StrongDual ℝ BallH1 →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ)) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) BallH1 ℝ).flip
      (harmonicFirstOrderLiftCompletion hF)
  have hEW : ContDiffOn ℝ ∞ (fun t : ℝ × (ℝ × (R3 × ℝ)) =>
      (referenceRotationAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).comp
        (referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t))
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    (contDiff_referenceRotationAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j).contDiffOn.clm_comp
      (contDiffOn_referenceRotationAdjointWeakHalfLiftFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 i j)
  change ContDiffOn ℝ ∞ (fun t : ℝ × (ℝ × (R3 × ℝ)) => sphereSurfaceMass⁻¹ •
    Q.comp ((referenceRotationAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).comp
      (referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t))) _
  have hQ : ContDiffOn ℝ ∞ (fun _ : ℝ × (ℝ × (R3 × ℝ)) => Q)
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    contDiffOn_const
  have hPost : ContDiffOn ℝ ∞ (fun t : ℝ × (ℝ × (R3 × ℝ)) => Q.comp
      ((referenceRotationAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).comp
        (referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t)))
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    hQ.clm_comp hEW
  have hMass : ContDiffOn ℝ ∞ (fun _ : ℝ × (ℝ × (R3 × ℝ)) => (sphereSurfaceMass⁻¹ : ℝ))
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    contDiffOn_const
  exact hMass.smul hPost

lemma contDiffOn_referenceRotationAdjointWeakConormalEndpointFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (referenceRotationAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF i j)
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  have hRiesz : ContDiffOn ℝ ∞
      (fun _ : ℝ × (ℝ × (R3 × ℝ)) => sphereSobolevDualRieszL (1/2:ℝ))
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    contDiffOn_const
  have hFormula : ContDiffOn ℝ ∞ (fun t : ℝ × (ℝ × (R3 × ℝ)) =>
      (sphereSobolevDualRieszL (1/2:ℝ)).comp
        (referenceRotationAdjointWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t))
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    hRiesz.clm_comp
      (contDiffOn_referenceRotationAdjointWeakConormalFunctionalFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 i j)
  apply hFormula.congr
  intro t hp
  exact referenceRotationAdjointWeakConormalEndpointFamily_eq_formula g L y0 Φ B ε C ρ H a w hData
    τ0 hcalc hF i j t hp.2.2.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakConormalEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakConormalFunctionalFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakConormalFunctionalFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakConormalEndpointFamily_eq_formula
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRotationAdjointWeakConormalFunctionalFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRotationAdjointWeakConormalEndpointFamily_invertibleLocus
