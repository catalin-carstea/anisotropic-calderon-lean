import Calderon.ActualReferenceRotationWeakHalfLiftTopology
import Calderon.NativeCoefficientWeakConormalEndpoint

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

/-! Expanded before source in EXPANSION-actual-rotation-native-conormal-assembly-v001.json.
Exactly one surface-mass inverse and literal drift coefficients. -/

def referenceRotationWeakConormalFunctionalFamily (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ)) :=
  sphereSurfaceMass⁻¹ •
    (referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).bilinearComp
      (referenceRotationNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j t)
      (harmonicFirstOrderLiftCompletion hF)

lemma referenceRotationWeakConormalFunctionalFamily_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (f z : SphereSobolev (1/2:ℝ)) :
    referenceRotationWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f z =
      sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => coordinateRotationPrincipalFamily i j a (t,x))
        (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) 0
        (referenceRotationNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j t f)
        (harmonicFirstOrderLiftCompletion hF z) := by
  change sphereSurfaceMass⁻¹ *
    referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
      (referenceRotationNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j t f)
      (harmonicFirstOrderLiftCompletion hF z) = _
  exact congrArg (fun r : ℝ => sphereSurfaceMass⁻¹*r)
    (referenceRotationFullWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc i j t _ _)

lemma referenceRotationWeakConormalFunctionalFamily_eq_nativeWeakConormalEndpointFunctional
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    referenceRotationWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t =
      nativeWeakConormalEndpointFunctional
        (fun x => coordinateRotationPrincipalFamily i j a (t,x))
        (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        0 (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t) hF := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousLinearMap.ext
  intro z
  exact (referenceRotationWeakConormalFunctionalFamily_apply
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f z).trans
      (nativeWeakConormalEndpointFunctional_apply _ _ 0
        (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t) hF f z).symm

def referenceRotationWeakConormalEndpointFamily (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (sphereSobolevDualRieszL (1/2:ℝ)).comp
    (referenceRotationWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t)

lemma referenceRotationWeakConormalEndpointFamily_eq_nativeWeakConormalEndpoint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    referenceRotationWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t =
      nativeWeakConormalEndpoint
        (fun x => coordinateRotationPrincipalFamily i j a (t,x))
        (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        0 (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t) hF := by
  exact congrArg (fun Q => (sphereSobolevDualRieszL (1/2:ℝ)).comp Q)
    (referenceRotationWeakConormalFunctionalFamily_eq_nativeWeakConormalEndpointFunctional
      g L y0 Φ B ε C ρ H a w hData hcalc hF i j t)

lemma sphereSobolevDualPairing_referenceRotationWeakConormalEndpointFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (f z : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) z
      (referenceRotationWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f) =
      sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => coordinateRotationPrincipalFamily i j a (t,x))
        (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) 0
        (referenceRotationNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j t f)
        (harmonicFirstOrderLiftCompletion hF z) :=
  (sphereSobolevDualPairing_dualRiesz (1/2:ℝ)
    (referenceRotationWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f) z).trans
      (referenceRotationWeakConormalFunctionalFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f z)

lemma contDiffAt_referenceRotationWeakConormalFunctionalFamily_of_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (p : ℝ × (ℝ × (R3 × ℝ)))
    (hi : (referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j p).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceRotationWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j) p := by
  have hE := (contDiff_referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j).contDiffAt (x := p)
  have hW := contDiffAt_referenceRotationNativeWeakHalfLiftFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j p hi
  let Q : StrongDual ℝ BallH1 →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ)) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) BallH1 ℝ).flip
      (harmonicFirstOrderLiftCompletion hF)
  have hEW : ContDiffAt ℝ ∞ (fun t =>
      (referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).comp
        (referenceRotationNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j t)) p := hE.clm_comp hW
  have hQEW := (contDiffAt_const (c := Q)).clm_comp hEW
  change ContDiffAt ℝ ∞ (fun t => sphereSurfaceMass⁻¹ • Q.comp
    ((referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).comp
      (referenceRotationNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j t))) p
  exact (contDiffAt_const (c := sphereSurfaceMass⁻¹)).smul hQEW

lemma contDiffAt_referenceRotationWeakConormalEndpointFamily_of_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (p : ℝ × (ℝ × (R3 × ℝ)))
    (hi : (referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j p).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceRotationWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j) p := by
  have hC := contDiffAt_referenceRotationWeakConormalFunctionalFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j p hi
  change ContDiffAt ℝ ∞ (fun t => (sphereSobolevDualRieszL (1/2:ℝ)).comp
    (referenceRotationWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t)) p
  exact (contDiffAt_const (c := sphereSobolevDualRieszL (1/2:ℝ))).clm_comp hC

lemma contDiffOn_referenceRotationWeakConormalEndpointFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (referenceRotationWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j)
      (referenceRotationWeakInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc i j) := by
  intro t ht
  exact (contDiffAt_referenceRotationWeakConormalEndpointFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j t ht).contDiffWithinAt

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakConormalFunctionalFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakConormalFunctionalFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakConormalFunctionalFamily_eq_nativeWeakConormalEndpointFunctional
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakConormalEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakConormalEndpointFamily_eq_nativeWeakConormalEndpoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceRotationWeakConormalEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRotationWeakConormalFunctionalFamily_of_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRotationWeakConormalEndpointFamily_of_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRotationWeakConormalEndpointFamily
