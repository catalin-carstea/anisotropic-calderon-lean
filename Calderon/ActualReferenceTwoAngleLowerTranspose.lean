import Calderon.ActualReferenceTwoAngleHighRadialAdjunction
import Calderon.ActualReferenceTwoAngleEndpointCompatibility
import Calderon.NativeLowerTransposeDerivative
import Mathlib.Topology.DenseEmbedding

/-! The actual low DN transpose. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (i j k l : Fin 3)

def referenceTwoAngleAdjointHalfRadialFamily (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  sphereLowerDistributionalTranspose (referenceTwoAngleLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t)

lemma sphereSobolevDualPairing_referenceTwoAngleLowerRadial_adjoint
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (u v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) v
      (referenceTwoAngleLowerRadialEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t u) =
    sphereSobolevDualPairing (1/2:ℝ) u
      (referenceTwoAngleAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t v) :=
  sphereSobolevDualPairing_lower_distributionalTranspose _ u v

attribute [local irreducible] referenceTwoAngleLowerRadialEndpointFamily
  referenceTwoAngleAdjointHalfRadialFamily referenceTwoAngleAdjointThreeHalfRadialFamily
  referenceTwoAngleSharpRadialTraceFamily

lemma referenceTwoAngleAdjointRadial_high_half_compatibility
    (hreg : FixedDirichletRegularity) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible)
    (hStrong : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (referenceTwoAngleAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t) =
    (referenceTwoAngleAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let A := referenceTwoAngleLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
  let D := referenceTwoAngleAdjointHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
  let DH := referenceTwoAngleAdjointThreeHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
  let S := referenceTwoAngleSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
  have hNormal := referenceNormalBoundaryMultiplierFamily_isInvertible_of_referenceData
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t.2.2
  have hCompatibility : J.comp S=A.comp I :=
    referenceTwoAngleSharpRadialTraceFamily_lower_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t hNormal hOriginal hStrong
  apply ContinuousLinearMap.ext
  intro v
  have hPoint (f : SphereSobolev (3/2:ℝ)) :
      ⟪I f,J (DH v)⟫_ℝ=⟪I f,D (I v)⟫_ℝ := by
    have hHigh := sphereSobolevDualPairing_referenceTwoAngleHighRadial_adjoint
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 i j k l t hOriginal hStrong f v
    have hLow : J (S f)=A (I f) := congrArg
      (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T f) hCompatibility
    have hNative := sphereSobolevDualPairing_referenceTwoAngleLowerRadial_adjoint
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t (I f) (I v)
    exact hHigh.symm.trans ((congrArg (fun y : SphereSobolev (-(1/2:ℝ)) =>
      sphereSobolevDualPairing (1/2:ℝ) (I v) y) hLow).trans hNative)
  have hFunctions : (fun u : SphereSobolev (1/2:ℝ) => ⟪u,J (DH v)⟫_ℝ)=
      (fun u : SphereSobolev (1/2:ℝ) => ⟪u,D (I v)⟫_ℝ) :=
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).equalizer
      (continuous_id.inner continuous_const) (continuous_id.inner continuous_const) (funext hPoint)
  exact ext_inner_left ℝ (fun u => congrFun hFunctions u)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointHalfRadialFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceTwoAngleLowerRadial_adjoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointRadial_high_half_compatibility
