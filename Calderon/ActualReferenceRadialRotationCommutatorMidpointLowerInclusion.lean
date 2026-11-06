import Calderon.ActualReferenceRadialRotationCommutatorMidpointFamily

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

/-! Lower physical identity of the existing actual Cmid family, by the midpoint
construction and typed value transports. -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceRadialRotationCommutatorMidpointFamily
  referenceLowerRadialRotationCommutatorL referenceSharpRadialRotationCommutatorL
  referenceRadialEndpointInvertibleLocus

lemma referenceRadialRotationCommutatorMidpointFamily_lower_inclusion
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (referenceRadialRotationCommutatorMidpointFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p) =
    (referenceLowerRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p).comp
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  let T0 : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
    referenceLowerRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
  let T1 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
  have hc : (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp T1 =
      T0.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
    referenceRadialRotationCommutatorEndpointPairFamily_mem_compatible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hp
  let D : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := sphereSobolevMidpointL T0 T1 hc
  have hFamily := referenceRadialRotationCommutatorMidpointFamily_of_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hp
  have hInc := sphereSobolevInclusionL_negative_half_notation_eq (0:ℝ)
    (by norm_num) (by norm_num)
  apply ContinuousLinearMap.ext
  intro f
  have hValue := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (A f)) hFamily
  have hNotation := congrArg
    (fun A : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A (D f)) hInc.symm
  have hMidpoint := congrArg
    (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A f)
      (sphereSobolevInclusionL_midpoint T0 T1 hc)
  exact hValue.trans (hNotation.trans hMidpoint)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialRotationCommutatorMidpointFamily_lower_inclusion
