import Calderon.NativeFiniteHarmonicH3Extension
import Calderon.ActualSmoothDatumHighRadialGraph
import Calderon.ActualReferenceSharpUpperTrace

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-FINITE-HARMONIC-HIGH-RADIAL-EXPANSION-v001.md. Same actual finite cutoff radial graph. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeH3ThreeHalfRadialTrace NativeFullHalfRadialTrace
  NativeHarmonicLiftCompletion

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceHarmonicLiftFamily referenceStrongDriftFamily
  nativeThreeHalfOutwardTraceL nativeHalfOutwardTraceL harmonicNativeH3PartialLiftL
  referenceSharpRadialTraceFamily harmonicLiftCompletion

lemma lowerOrder_referenceHarmonicLiftFamily_one
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (p : ℝ × (R3 × ℝ)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w (p,z)‖ ≤ lam/4)
    (E : BallSobolev 3) :
    TauCeti.Wkp.lowerOrder 2
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2 E) =
      referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
        (TauCeti.Wkp.lowerOrder 2 E) := by
  let U : BallSobolev 3 := referenceHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2 E
  have hInput : TauCeti.Wkp.firstOrder 2 E =
      TauCeti.Wkp.firstOrder 1 (TauCeti.Wkp.lowerOrder 2 E) := rfl
  have hFirst := referenceHarmonicLiftFamily_firstOrder_eq
    g L y0 Φ B ε C ρ H a w hData hcalc hreg 1 0 p.1 p.2 lam Lam hUE hsmall
      E (TauCeti.Wkp.lowerOrder 2 E) hInput
  have hValue := congrArg TauCeti.W1p.value hFirst
  simp only [TauCeti.Wkp.value_firstOrder] at hValue
  apply TauCeti.Wkp.ext 2
  exact (TauCeti.Wkp.value_succ 2 U).symm.trans hValue

def referenceFiniteHarmonicHighRadialFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  (nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0).comp
    ((referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).comp
      (harmonicNativeH3PartialLiftL hF n))

lemma sphereSobolevInclusionL_referenceFiniteHarmonicHighRadialFamily
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (n : ℕ) (p : ℝ × (R3 × ℝ)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w (p,z)‖ ≤ lam/4)
    (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceFiniteHarmonicHighRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n p f) =
      referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (sphereSobolevPartialSum (3/2 : ℝ) n f) := by
  let E := harmonicNativeH3PartialLiftL hF n f
  let V := referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2 E
  let O := nativeHalfOutwardTraceL hF hO hD hcalc τ0
  have hSame := lowerOrder_referenceHarmonicLiftFamily_one
    g L y0 Φ B ε C ρ H a w hData hcalc hreg p lam Lam hUE hsmall E
  have hInput := lowerOrder_harmonicNativeH3PartialLiftL hF hO n f
  have hLow := hSame.trans (congrArg
    (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2) hInput)
  have hGraph := (sphereSobolevInclusionL_nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0 V).trans
    (congrArg O hLow)
  have hPoint : O (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
      (harmonicLiftCompletion hF (sphereSobolevPartialSum (3/2 : ℝ) n f))) =
      referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (sphereSobolevPartialSum (3/2 : ℝ) n f) := by
    unfold referenceSharpRadialTraceFamily
    rfl
  exact hGraph.trans hPoint

lemma contDiffAt_referenceFiniteHarmonicHighRadialFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceFiniteHarmonicHighRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n) p := by
  have hLift := contDiffAt_joint_referenceHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 1 p hi
  exact contDiffAt_const.clm_comp (hLift.clm_comp contDiffAt_const)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.lowerOrder_referenceHarmonicLiftFamily_one
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFiniteHarmonicHighRadialFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_referenceFiniteHarmonicHighRadialFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteHarmonicHighRadialFamily
