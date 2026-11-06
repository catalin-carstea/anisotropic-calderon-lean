import Calderon.ActualHighSmoothMultiplierStrongDefect
import Calderon.NativeH3ThreeHalfRadialTrace
import Calderon.NativeHighStrongOutwardTrace
import Calderon.NativeHighStrongOutwardTraceNorm
import Calderon.NativeThreeHalfNormalDerivativeMultiplier
import Calderon.ActualReferenceSmoothMultiplierBoundaryCommutator

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-HIGH-SMOOTH-MULTIPLIER-GAIN-EXPANSION-v001.md. Concrete SAME H3/2 commutator gain. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeH3ThreeHalfRadialTrace NativeFullHalfRadialTrace
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceHighSmoothMultiplierStrongDefectFamily
  referenceSmoothMultiplierStrongDefectFamily nativeThreeHalfOutwardTraceL nativeHalfOutwardTraceL
  nativeThreeHalfNormalDerivativeMulL nativeHalfNormalDerivativeMulL referenceStrongDriftFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily sphereSobolevInclusionL


attribute [local instance_reducible] highStrongNativeH3Group
attribute [local instance_reducible] highStrongNativeH3Space
attribute [local instance] highStrongNativeH3Group
attribute [local instance] highStrongNativeH3Space
attribute [local irreducible] TauCeti.SobolevStage.instNormedAddCommGroup
attribute [local irreducible] TauCeti.SobolevStage.instNormedSpace
attribute [local instance] nativeOutwardStageCanonicalNorm

def referenceHighSmoothMultiplierBoundaryCommutatorFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  let O : BallSobolev 3 →L[ℝ] SphereSobolev (3/2 : ℝ) :=
    nativeHighStrongOutwardTraceL hcalc hF hO hD τ0
  let V : SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 3 :=
    referenceHighSmoothMultiplierStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF Q p
  let M : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
    nativeThreeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q
  O.comp V + M


lemma referenceHighSmoothMultiplierBoundaryCommutatorFamily_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2 : ℝ)) :
    referenceHighSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 Q p f =
    nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0
      (referenceHighSmoothMultiplierStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF Q p f) +
    nativeThreeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q f := by
  have hGraph := nativeHighStrongOutwardTraceL_apply hcalc hF hO hD τ0
    (referenceHighSmoothMultiplierStrongDefectFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF Q p f)
  have hAdd := congrArg
    (fun z : SphereSobolev (3/2 : ℝ) =>
      z + nativeThreeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q f) hGraph
  simpa only [referenceHighSmoothMultiplierBoundaryCommutatorFamily,
    add_apply, ContinuousLinearMap.comp_apply] using hAdd

lemma norm_referenceHighSmoothMultiplierBoundaryCommutatorFamily_le
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    ‖referenceHighSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 Q p‖ ≤
    ‖nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0‖ *
      ‖referenceHighSmoothMultiplierStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF Q p‖ +
    ‖nativeThreeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q‖ := by
  let O := nativeHighStrongOutwardTraceL hcalc hF hO hD τ0
  let V := referenceHighSmoothMultiplierStrongDefectFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF Q p
  let M := nativeThreeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q
  have hComp : ‖O.comp V‖ ≤ ContinuousLinearMap.opNorm O * ‖V‖ :=
    ContinuousLinearMap.opNorm_comp_le O V
  have hNorm := opNorm_nativeHighStrongOutwardTraceL_eq_original hcalc hF hO hD τ0
  calc
    ‖referenceHighSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q p‖ =
        ‖O.comp V + M‖ := rfl
    _ ≤ ContinuousLinearMap.opNorm O * ‖V‖ + ‖M‖ :=
      (norm_add_le _ _).trans (add_le_add hComp le_rfl)
    _ = ‖nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0‖ * ‖V‖ + ‖M‖ :=
      congrArg (fun c : ℝ => c * ‖V‖ + ‖M‖) hNorm


lemma referenceHighSmoothMultiplierBoundaryCommutatorFamily_lower
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (Q : SmoothCoefficientJets 3)
    (p : ℝ × (R3 × ℝ)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w (p,z)‖ ≤ lam/4)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceHighSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 Q p f) =
    referenceSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 Q p
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let V := referenceHighSmoothMultiplierStrongDefectFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF Q p f
  let O := nativeHalfOutwardTraceL hF hO hD hcalc τ0
  have hRadial := sphereSobolevInclusionL_nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0 V
  have hSame := lowerOrder_referenceHighSmoothMultiplierStrongDefectFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 Q p lam Lam hUE hsmall hWeak f
  have hTerm := hRadial.trans (congrArg O hSame)
  have hNormal := sphereSobolevInclusionL_nativeThreeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q f
  have hPoint := congrArg I (referenceHighSmoothMultiplierBoundaryCommutatorFamily_apply
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q p f)
  have hAdd := I.map_add
    (nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0 V)
    (nativeThreeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q f)
  exact hPoint.trans (hAdd.trans ((congrArg₂ (fun x y : SphereSobolev (1/2 : ℝ) => x+y)
    hTerm hNormal).trans (referenceSmoothMultiplierBoundaryCommutatorFamily_apply
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q p (I f)).symm))

lemma referenceHighSmoothMultiplierBoundaryCommutatorFamily_inclusion
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0) (Q : SmoothCoefficientJets 3)
    (p : ℝ × (R3 × ℝ)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w (p,z)‖ ≤ lam/4)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceHighSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 Q p f) =
    referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q f) -
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f) := by
  have hStrong := referenceStrongDriftFamily_isInvertible_of_smallDrift
    g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 p.1 p.2 lam Lam hUE hsmall
  exact (referenceHighSmoothMultiplierBoundaryCommutatorFamily_lower
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 Q p lam Lam hUE hsmall hWeak f).trans
      (referenceSmoothMultiplierBoundaryCommutatorFamily_inclusion
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q p hStrong hWeak f)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighSmoothMultiplierBoundaryCommutatorFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighSmoothMultiplierBoundaryCommutatorFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_referenceHighSmoothMultiplierBoundaryCommutatorFamily_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighSmoothMultiplierBoundaryCommutatorFamily_lower
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighSmoothMultiplierBoundaryCommutatorFamily_inclusion

