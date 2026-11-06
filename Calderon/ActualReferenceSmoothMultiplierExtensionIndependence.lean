import Calderon.ActualReferenceSmoothMultiplierBoundaryCommutator
import Calderon.NativeThreeHalfBoundaryMultiplierLocalSmoothness
import Calderon.SphereSobolevDenseEndpointCovariance

/-! Boundary value alone determines the sum of strong-defect trace and normal multiplier. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier

attribute [local irreducible] referenceSmoothMultiplierBoundaryCommutatorFamily
  referenceSharpRadialTraceFamily nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL

lemma nativeHalfCoefficientMulL_lower_eq_of_sphereValue_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q G : SmoothCoefficientJets 3)
    (hSphere : smoothSphereValue (nativeH2CoefficientSmoothData Q) =
      smoothSphereValue (nativeH2CoefficientSmoothData G)) :
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) =
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets G) := by
  apply ContinuousLinearMap.ext
  intro f
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  have hQ := sphereSobolevInclusionL_nativeHalfCoefficientMulL_sameValue
    hcalc hF hO hD τ0 Q (smoothMultiplierLowerJets Q)
    (coefficientValue_smoothMultiplierLowerJets Q).symm f
  have hG := sphereSobolevInclusionL_nativeHalfCoefficientMulL_sameValue
    hcalc hF hO hD τ0 G (smoothMultiplierLowerJets G)
    (coefficientValue_smoothMultiplierLowerJets G).symm f
  have hsame := congrArg (fun m : C(UnitSphere, ℝ) => sphereSobolevZeroEquiv hO hD
    (sphereContinuousScalarMulL m ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) f)))) hSphere
  exact hQ.trans (hsame.trans hG.symm)

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceSmoothMultiplierBoundaryCommutatorFamily_eq_of_sphereValue_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0) (Q G : SmoothCoefficientJets 3)
    (hSphere : smoothSphereValue (nativeH2CoefficientSmoothData Q) =
      smoothSphereValue (nativeH2CoefficientSmoothData G))
    (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    referenceSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 Q p =
    referenceSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 G p := by
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let D : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let BQ : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := referenceSmoothMultiplierBoundaryCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q p
  let BG : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := referenceSmoothMultiplierBoundaryCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 G p
  have h3 := nativeThreeHalfCoefficientMulL_eq_of_sphereValue_eq hcalc hF hO hD τ0 Q G hSphere
  have h1 := nativeHalfCoefficientMulL_lower_eq_of_sphereValue_eq hcalc hF hO hD τ0 Q G hSphere
  have hDense (u : SphereSobolev (3/2 : ℝ)) : BQ (I u) = BG (I u) := by
    have hQ : BQ (I u) =
        D (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q u) -
        nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) (D u) :=
      referenceSmoothMultiplierBoundaryCommutatorFamily_inclusion
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q p hStrong hWeak u
    have hG : BG (I u) =
        D (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G u) -
        nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets G) (D u) :=
      referenceSmoothMultiplierBoundaryCommutatorFamily_inclusion
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel G p hStrong hWeak u
    have hin := congrArg (fun M : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) =>
      D (M u)) h3
    have hout := congrArg (fun M : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      M (D u)) h1
    exact hQ.trans ((congrArg₂ (fun x y : SphereSobolev (1/2 : ℝ) => x-y) hin hout).trans hG.symm)
  apply ContinuousLinearMap.ext
  intro f
  exact denseRange_clm_apply_eq I
    (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) BQ BG hDense f

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfCoefficientMulL_lower_eq_of_sphereValue_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSmoothMultiplierBoundaryCommutatorFamily_eq_of_sphereValue_eq
