import Calderon.ActualReferenceNativeWeakHalfLift
import Calderon.ActualReferenceWeakConormalEndpoint

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-! Expanded before source in EXPANSION-actual-reference-native-weak-identification-v001.json.
Precisely one sphereSurfaceMass inverse is retained for sphereProbability. -/

lemma referenceWeakConormalEndpointFunctionalFamily_native_energy
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (f z : SphereSobolev (1/2 : ℝ)) :
    referenceWeakConormalEndpointFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f z =
      sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
        (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
        (nativeWeakHalfLift (fun x => a (p,x))
          (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
          (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p) hF f)
        (harmonicFirstOrderLiftCompletion hF z) := by
  have hLift := congrArg (fun W : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 => W f)
    (referenceWeakHalfLiftFamily_eq_nativeWeakHalfLift g L y0 Φ B ε C ρ H a w hData hcalc hF p
      (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p))
  have hEnergy := referenceFullWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p
    (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
    (harmonicFirstOrderLiftCompletion hF z)
  exact (referenceWeakConormalEndpointFunctionalFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc hF p f z).trans
    ((congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t) hEnergy).trans
      (congrArg (fun U : BallH1 => sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
        (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
        U (harmonicFirstOrderLiftCompletion hF z)) hLift))

lemma sphereSobolevDualPairing_referenceWeakConormalEndpointFamily_native_energy
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (f z : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) z
      (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) =
      sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
        (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
        (nativeWeakHalfLift (fun x => a (p,x))
          (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
          (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p) hF f)
        (harmonicFirstOrderLiftCompletion hF z) := by
  exact (sphereSobolevDualPairing_referenceWeakConormalEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF p f z).trans
    ((referenceWeakConormalEndpointFunctionalFamily_apply
      g L y0 Φ B ε C ρ H a w hData hcalc hF p f z).symm.trans
      (referenceWeakConormalEndpointFunctionalFamily_native_energy
        g L y0 Φ B ε C ρ H a w hData hcalc hF p f z))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakConormalEndpointFunctionalFamily_native_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceWeakConormalEndpointFamily_native_energy
