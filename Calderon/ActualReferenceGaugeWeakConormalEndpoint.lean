import Calderon.ActualReferenceGaugeWeakPairing
import Calderon.ActualReferenceWeakConormalEndpoint

/-! Weak conormal endpoint of the gauge, with the same original weak lifts. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError NativeHarmonicH1LiftCompletion SphereHarmonic NativePolynomialBulkMoments

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceGaugeWeakConormalFunctionalFamily
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] StrongDual ℝ (SphereSobolev (1/2 : ℝ)) :=
  sphereSurfaceMass⁻¹ •
    (((ContinuousLinearMap.compL ℝ (SphereSobolev (1/2 : ℝ)) BallH1 ℝ).flip
      (harmonicFirstOrderLiftCompletion hF)).comp
      ((TauCeti.PDE.energyFormH1L
        (referenceGaugeNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData hg p)).comp
          (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p)))

def referenceGaugeWeakConormalEndpointFamily
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  (sphereSobolevDualRieszL (1/2 : ℝ)).comp
    (referenceGaugeWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF p)

theorem sphereSobolevDualPairing_referenceGaugeWeakConormalEndpoint_energy
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (f z : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) z
      (referenceGaugeWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF p f) =
    sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceExponentialGauge g L Φ p x • a (p,x)) 0 0
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
      (harmonicFirstOrderLiftCompletion hF z) := by
  have hR := sphereSobolevDualPairing_dualRiesz (1/2 : ℝ)
    (referenceGaugeWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF p f) z
  have hE := TauCeti.PDE.energyFormH1L_apply
    (referenceGaugeNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData hg p)
    (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
    (harmonicFirstOrderLiftCompletion hF z)
  exact hR.trans (congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t) hE)

theorem sphereSobolevDualPairing_referenceGaugeWeakConormalEndpoint_comm
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ))
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f z : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) z
      (referenceGaugeWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF p f) =
    sphereSobolevDualPairing (1/2 : ℝ) f
      (referenceGaugeWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF p z) :=
  (sphereSobolevDualPairing_referenceGaugeWeakConormalEndpoint_energy
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF p f z).trans
      ((congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t)
        (referenceGaugeNativeEnergy_boundary_pairing_comm
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF p hWeak f z)).trans
        (sphereSobolevDualPairing_referenceGaugeWeakConormalEndpoint_energy
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF p z f).symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeWeakConormalFunctionalFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeWeakConormalEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceGaugeWeakConormalEndpoint_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceGaugeWeakConormalEndpoint_comm
