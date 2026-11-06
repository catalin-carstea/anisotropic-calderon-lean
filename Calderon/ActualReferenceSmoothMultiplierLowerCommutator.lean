import Calderon.ActualReferenceSmoothMultiplierBoundaryCommutator
import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.SphereSobolevTangentialEndpointCompatibility
import Calderon.SphereSobolevDenseEndpointCovariance

/-! Actual lower graph for the bounded half commutator, obtained through dense upper inputs. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
attribute [local irreducible] nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  nativeThreeHalfCoefficientMulL referenceSmoothMultiplierBoundaryCommutatorFamily
  referenceSharpRadialTraceFamily referenceLowerRadialEndpointFamily

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceSmoothMultiplierBoundaryCommutatorFamily_lower_agreement
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0) (Q : SmoothCoefficientJets 3)
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (f : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 Q p f) =
    referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) f) -
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let A := referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let D := referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let G := referenceSmoothMultiplierBoundaryCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q p
  let M3 := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let M1 := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  let Mn := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  have hA (u : SphereSobolev (3/2 : ℝ)) : A (I u) = J (D u) :=
    (congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T u)
      (referenceSharpRadialTraceFamily_lower_compatibility_on_locus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp)).symm
  have hI (u : SphereSobolev (3/2 : ℝ)) : I (M3 u) = M1 (I u) :=
    congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T u)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 Q
        (smoothMultiplierLowerJets Q) (coefficientValue_smoothMultiplierLowerJets Q).symm)
  have hJ (v : SphereSobolev (1/2 : ℝ)) : J (M1 v) = Mn (J v) :=
    congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T v)
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q))
  change J (G f) = A (M1 f)-Mn (A f)
  apply denseRange_clm_apply_eq I
    (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))
    (J.comp G) ((A.comp M1)-(Mn.comp A))
  intro u
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply]
  have hG : G (I u) = D (M3 u)-M1 (D u) :=
    referenceSmoothMultiplierBoundaryCommutatorFamily_inclusion
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q p hp.1 hp.2.1 u
  have hFirst : J (D (M3 u)) = A (M1 (I u)) :=
    (hA (M3 u)).symm.trans (congrArg A (hI u))
  have hSecond : J (M1 (D u)) = Mn (A (I u)) :=
    (hJ (D u)).trans (congrArg Mn (hA u).symm)
  exact (congrArg J hG).trans ((J.map_sub _ _).trans
    (congrArg₂ (fun x y : SphereSobolev (-(1/2 : ℝ)) => x-y) hFirst hSecond))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSmoothMultiplierBoundaryCommutatorFamily_lower_agreement
