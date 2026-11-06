import Calderon.ActualReferenceNativeConormalPairing
import Calderon.NativeCoefficientWeakConormalEndpoint

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceWeakConormalEndpointFunctionalFamily_eq_nativeWeakConormalEndpointFunctional
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ)) :
    referenceWeakConormalEndpointFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p =
    nativeWeakConormalEndpointFunctional (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
      (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p) hF := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousLinearMap.ext
  intro z
  exact (referenceWeakConormalEndpointFunctionalFamily_native_energy
    g L y0 Φ B ε C ρ H a w hData hcalc hF p f z).trans
      (nativeWeakConormalEndpointFunctional_apply (fun x => a (p,x))
        (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
        (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p) hF f z).symm

lemma referenceWeakConormalEndpointFamily_eq_nativeWeakConormalEndpoint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ)) :
    referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p =
    nativeWeakConormalEndpoint (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
      (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p) hF := by
  exact congrArg (fun Q : SphereSobolev (1/2:ℝ) →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ)) =>
    (sphereSobolevDualRieszL (1/2:ℝ)).comp Q)
      (referenceWeakConormalEndpointFunctionalFamily_eq_nativeWeakConormalEndpointFunctional
        g L y0 Φ B ε C ρ H a w hData hcalc hF p)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakConormalEndpointFunctionalFamily_eq_nativeWeakConormalEndpointFunctional
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakConormalEndpointFamily_eq_nativeWeakConormalEndpoint
