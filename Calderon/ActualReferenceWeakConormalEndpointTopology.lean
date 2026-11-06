import Calderon.ActualReferenceWeakConormalEndpoint
import Calderon.ActualReferenceFullWeakEnergyTopology
import Calderon.ActualReferenceWeakHalfLiftTopology

/-! Full upfront argument: EXPANSION-actual-reference-weak-endpoint-joint-topology-v001.json.
Actual joint families, author draft awaiting checks. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


theorem contDiffAt_referenceWeakConormalEndpointFunctionalFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (lam : ℝ)
    (hs : UnitBallSmallDriftData (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) lam) :
    ContDiffAt ℝ ∞
      (referenceWeakConormalEndpointFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF) p := by
  have hE := (contDiff_referenceFullWeakEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc).contDiffAt (x := p)
  have hW := contDiffAt_referenceWeakHalfLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF p lam hs
  let Q : StrongDual ℝ BallH1 →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ)) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) BallH1 ℝ).flip
      (harmonicFirstOrderLiftCompletion hF)
  have hQ : ContDiffAt ℝ ∞ (fun _ : ℝ × (R3 × ℝ) => Q) p := contDiffAt_const
  let EW : (ℝ × (R3 × ℝ)) →
      (SphereSobolev (1/2:ℝ) →L[ℝ] StrongDual ℝ BallH1) := fun q =>
    (referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc q).comp
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF q)
  have hEW : ContDiffAt ℝ ∞ EW p := hE.clm_comp hW
  have hQEW : ContDiffAt ℝ ∞
      (fun q : ℝ × (R3 × ℝ) => Q.comp
        ((referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc q).comp
          (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF q))) p :=
    hQ.clm_comp hEW
  have hm : ContDiffAt ℝ ∞ (fun _ : ℝ × (R3 × ℝ) => sphereSurfaceMass⁻¹) p :=
    contDiffAt_const
  change ContDiffAt ℝ ∞ (fun q : ℝ × (R3 × ℝ) => sphereSurfaceMass⁻¹ •
    Q.comp ((referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc q).comp
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF q))) p
  exact hm.smul hQEW

theorem contDiffAt_referenceWeakConormalEndpointFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (lam : ℝ)
    (hs : UnitBallSmallDriftData (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) lam) :
    ContDiffAt ℝ ∞
      (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF) p := by
  have hR : ContDiffAt ℝ ∞ (fun _ : ℝ × (R3 × ℝ) =>
      (sphereSobolevDualRieszL (1/2:ℝ) :
        StrongDual ℝ (SphereSobolev (1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))) p :=
    contDiffAt_const
  have hC := contDiffAt_referenceWeakConormalEndpointFunctionalFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF p lam hs
  change ContDiffAt ℝ ∞ (fun q : ℝ × (R3 × ℝ) =>
    (sphereSobolevDualRieszL (1/2:ℝ)).comp
      (referenceWeakConormalEndpointFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF q)) p
  exact hR.clm_comp hC

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceWeakConormalEndpointFunctionalFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceWeakConormalEndpointFamily
