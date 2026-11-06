import Calderon.ActualReferenceTwoAngleWeakConormalCore
import Calderon.ActualReferenceTwoAngleNativeWeakHalfLift
import Calderon.ActualReferenceTwoAngleFullWeakEnergyTopology

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
local instance : NormedAddCommGroup (StrongDual ℝ BallH1) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (StrongDual ℝ BallH1) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup (StrongDual ℝ (SphereSobolev (1/2:ℝ))) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (StrongDual ℝ (SphereSobolev (1/2:ℝ))) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup (BallH1 →L[ℝ] StrongDual ℝ BallH1) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (BallH1 →L[ℝ] StrongDual ℝ BallH1) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup (SphereSobolev (1/2:ℝ) →L[ℝ] StrongDual ℝ BallH1) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (SphereSobolev (1/2:ℝ) →L[ℝ] StrongDual ℝ BallH1) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup (SphereSobolev (1/2:ℝ) →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ))) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (SphereSobolev (1/2:ℝ) →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ))) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup (StrongDual ℝ (SphereSobolev (1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (StrongDual ℝ (SphereSobolev (1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
  ContinuousLinearMap.toNormedSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

/-! SAME literal native energy and weak lift. -/

lemma contDiffAt_referenceTwoAngleWeakConormalFunctionalFamily_of_original
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j k l : Fin 3) (p : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hi : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p.2.2).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceTwoAngleWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l) p := by
  have hE := (contDiff_referenceTwoAngleFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l).contDiffAt (x := p)
  have hW := contDiffAt_referenceTwoAngleNativeWeakHalfLiftFamily_of_original
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l p hi
  let Q : StrongDual ℝ BallH1 →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ)) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) BallH1 ℝ).flip
      (harmonicFirstOrderLiftCompletion hF)
  have hEW : ContDiffAt ℝ ∞ (fun t =>
      (referenceTwoAngleFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).comp
        (referenceTwoAngleNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j k l t)) p := hE.clm_comp hW
  have hQEW := (contDiffAt_const (c := Q)).clm_comp hEW
  change ContDiffAt ℝ ∞ (fun t => sphereSurfaceMass⁻¹ • Q.comp
    ((referenceTwoAngleFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).comp
      (referenceTwoAngleNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j k l t))) p
  exact (contDiffAt_const (c := sphereSurfaceMass⁻¹)).smul hQEW

lemma contDiffAt_referenceTwoAngleWeakConormalEndpointFamily_of_original
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j k l : Fin 3) (p : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hi : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p.2.2).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceTwoAngleWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l) p := by
  have hC := contDiffAt_referenceTwoAngleWeakConormalFunctionalFamily_of_original
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l p hi
  change ContDiffAt ℝ ∞ (fun t => (sphereSobolevDualRieszL (1/2:ℝ)).comp
    (referenceTwoAngleWeakConormalFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t)) p
  exact (contDiffAt_const (c := sphereSobolevDualRieszL (1/2:ℝ))).clm_comp hC

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAngleWeakConormalFunctionalFamily_of_original
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAngleWeakConormalEndpointFamily_of_original
