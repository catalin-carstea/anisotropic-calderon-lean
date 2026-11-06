import Calderon.ActualReferenceTwoAngleNativeWeakHalfLiftCore
import Calderon.NativeCoefficientWeakConormalEndpoint

set_option autoImplicit false
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

/-! SAME literal native energy and weak lift. -/

def referenceTwoAngleWeakConormalFunctionalFamily (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ)) :=
  sphereSurfaceMass⁻¹ •
    (referenceTwoAngleFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).bilinearComp
      (referenceTwoAngleNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j k l t)
      (harmonicFirstOrderLiftCompletion hF)

lemma referenceTwoAngleWeakConormalFunctionalFamily_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (f z : SphereSobolev (1/2:ℝ)) :
    referenceTwoAngleWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f z =
      sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
        (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
        (referenceTwoAngleNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j k l t f)
        (harmonicFirstOrderLiftCompletion hF z) := by
  change sphereSurfaceMass⁻¹ *
    referenceTwoAngleFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
      (referenceTwoAngleNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j k l t f)
      (harmonicFirstOrderLiftCompletion hF z) = _
  exact congrArg (fun r : ℝ => sphereSurfaceMass⁻¹*r)
    (referenceTwoAngleFullWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc i j k l t _ _)

lemma referenceTwoAngleWeakConormalFunctionalFamily_eq_nativeWeakConormalEndpointFunctional
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    referenceTwoAngleWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t =
      nativeWeakConormalEndpointFunctional
        (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
        (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
        0 (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t) hF := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousLinearMap.ext
  intro z
  exact (referenceTwoAngleWeakConormalFunctionalFamily_apply
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f z).trans
      (nativeWeakConormalEndpointFunctional_apply _ _ 0
        (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t) hF f z).symm

def referenceTwoAngleWeakConormalEndpointFamily (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (sphereSobolevDualRieszL (1/2:ℝ)).comp
    (referenceTwoAngleWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t)

lemma referenceTwoAngleWeakConormalEndpointFamily_eq_nativeWeakConormalEndpoint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    referenceTwoAngleWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t =
      nativeWeakConormalEndpoint
        (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
        (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
        0 (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t) hF := by
  exact congrArg (fun Q => (sphereSobolevDualRieszL (1/2:ℝ)).comp Q)
    (referenceTwoAngleWeakConormalFunctionalFamily_eq_nativeWeakConormalEndpointFunctional
      g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t)

lemma sphereSobolevDualPairing_referenceTwoAngleWeakConormalEndpointFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (f z : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) z
      (referenceTwoAngleWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f) =
      sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
        (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
        (referenceTwoAngleNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j k l t f)
        (harmonicFirstOrderLiftCompletion hF z) :=
  (sphereSobolevDualPairing_dualRiesz (1/2:ℝ)
    (referenceTwoAngleWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f) z).trans
      (referenceTwoAngleWeakConormalFunctionalFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f z)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleWeakConormalFunctionalFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleWeakConormalFunctionalFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleWeakConormalFunctionalFamily_eq_nativeWeakConormalEndpointFunctional
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleWeakConormalEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleWeakConormalEndpointFamily_eq_nativeWeakConormalEndpoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceTwoAngleWeakConormalEndpointFamily
