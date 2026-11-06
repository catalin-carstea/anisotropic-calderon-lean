import Calderon.NativeFiniteHarmonicProductH3Extension
import Calderon.ActualFiniteHarmonicHighRadialGraph
import Calderon.ActualReferenceSameBoundaryCorrection

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-FINITE-PRODUCT-HIGH-RADIAL-EXPANSION-v001.md. SAME DN on untruncated product of finite input. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeH3ThreeHalfRadialTrace NativeFullHalfRadialTrace NativeH2ThreeHalfValueTrace
  NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceHarmonicLiftFamily referenceStrongDriftFamily
  nativeThreeHalfOutwardTraceL nativeHalfOutwardTraceL nativeFiniteHarmonicProductLiftL
  referenceSharpRadialTraceFamily harmonicLiftCompletion coefficientMultiplier
  nativeThreeHalfValueTraceL nativeThreeHalfCoefficientMulL

def referenceFiniteHarmonicProductHighRadialFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  (nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0).comp
    ((referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).comp
      (nativeFiniteHarmonicProductLiftL hcalc hF n Q))

lemma sphereSobolevInclusionL_referenceFiniteHarmonicProductHighRadialFamily
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (n : ℕ) (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w (p,z)‖ ≤ lam/4)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceFiniteHarmonicProductHighRadialFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 n Q p f) =
      referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q (sphereSobolevPartialSum (3/2 : ℝ) n f)) := by
  let E := nativeFiniteHarmonicProductLiftL hcalc hF n Q f
  let E2 := coefficientMultiplier hcalc 2 Q
    (harmonicLiftCompletion hF (sphereSobolevPartialSum (3/2 : ℝ) n f))
  let V := referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2 E
  let O := nativeHalfOutwardTraceL hF hO hD hcalc τ0
  let T := nativeThreeHalfValueTraceL hcalc hF hO hD τ0
  let S := referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  have hInput : TauCeti.Wkp.lowerOrder 2 E = E2 :=
    lowerOrder_nativeFiniteHarmonicProductLiftL hcalc hF hO n Q f
  have hSame := (lowerOrder_referenceHarmonicLiftFamily_one
    g L y0 Φ B ε C ρ H a w hData hcalc hreg p lam Lam hUE hsmall E).trans
      (congrArg (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2) hInput)
  have hRadial := (sphereSobolevInclusionL_nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0 V).trans
    (congrArg O hSame)
  have hStrong := referenceStrongDriftFamily_isInvertible_of_smallDrift
    g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 p.1 p.2 lam Lam hUE hsmall
  have hBoundary := referenceHarmonicLiftFamily_eq_harmonicLiftCompletion_nativeThreeHalfTrace
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel p.1 p.2 hStrong hWeak E2
  have hPoint : O (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
      (harmonicLiftCompletion hF (T E2))) = S (T E2) := by
    unfold S referenceSharpRadialTraceFamily
    rfl
  have hTraceInput := (congrArg T hInput).symm.trans
    (nativeThreeHalfValueTraceL_lowerOrder_nativeFiniteHarmonicProductLiftL hcalc hF hO hD τ0 n Q f)
  exact hRadial.trans ((congrArg O hBoundary).trans (hPoint.trans (congrArg S hTraceInput)))

lemma contDiffAt_referenceFiniteHarmonicProductHighRadialFamily_of_value_graph
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (n : ℕ)
    (m : (ℝ × (R3 × ℝ)) × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → m (p,x)=0)
    (Q : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 3)
    (hQ : ∀ p, coefficientValue 3 (Q p) = fun x => m (p,x)) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z => referenceFiniteHarmonicProductHighRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (Q z) z) p := by
  have hInput := (contDiff_nativeFiniteHarmonicProductLiftL_of_value_graph hcalc hF n m hm K hK hz Q hQ).contDiffAt (x := p)
  have hLift := contDiffAt_joint_referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p hi
  exact contDiffAt_const.clm_comp (hLift.clm_comp hInput)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFiniteHarmonicProductHighRadialFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_referenceFiniteHarmonicProductHighRadialFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteHarmonicProductHighRadialFamily_of_value_graph
