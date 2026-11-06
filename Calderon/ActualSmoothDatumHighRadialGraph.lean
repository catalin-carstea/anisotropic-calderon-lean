import Calderon.ActualHarmonicLiftConsistency
import Calderon.ActualJointNativeTraceOperatorFamily
import Calderon.NativeH3ThreeHalfRadialTrace

/-! The smooth-datum solution and its finite native H3 graph. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeH3ThreeHalfRadialTrace NativeFullHalfRadialTrace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceSmoothDatumHighRadialSection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (v : SmoothData) (p : ℝ × (R3 × ℝ)) : SphereSobolev (3/2 : ℝ) :=
  nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0
    (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2
      (smoothBallSobolev 3 v))

attribute [local irreducible] referenceHarmonicLiftFamily referenceStrongDriftFamily
  nativeThreeHalfOutwardTraceL nativeHalfOutwardTraceL smoothBallSobolev

lemma lowerOrder_referenceHarmonicLiftFamily_smoothDatum_one
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (p : ℝ × (R3 × ℝ)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w (p,z)‖ ≤ lam/4)
    (v : SmoothData) :
    TauCeti.Wkp.lowerOrder 2
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2
        (smoothBallSobolev 3 v)) =
    referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
      (smoothBallSobolev 2 v) := by
  let U : BallSobolev 3 := referenceHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2 (smoothBallSobolev 3 v)
  let V : BallSobolev 2 := referenceHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 (smoothBallSobolev 2 v)
  have hInput : TauCeti.Wkp.firstOrder 2 (smoothBallSobolev 3 v) =
      TauCeti.Wkp.firstOrder 1 (smoothBallSobolev 2 v) :=
    (firstOrder_smoothBallSobolev 2 v).trans (firstOrder_smoothBallSobolev 1 v).symm
  have hFirst := referenceHarmonicLiftFamily_firstOrder_eq
    g L y0 Φ B ε C ρ H a w hData hcalc hreg 1 0 p.1 p.2 lam Lam hUE hsmall
      (smoothBallSobolev 3 v) (smoothBallSobolev 2 v) hInput
  have hValue := congrArg TauCeti.W1p.value hFirst
  simp only [TauCeti.Wkp.value_firstOrder] at hValue
  apply TauCeti.Wkp.ext 2
  exact (TauCeti.Wkp.value_succ 2 U).symm.trans hValue

lemma sphereSobolevInclusionL_referenceSmoothDatumHighRadialSection
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w (p,z)‖ ≤ lam/4)
    (v : SmoothData) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceSmoothDatumHighRadialSection g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 v p) =
    nativeHalfOutwardTraceL hF hO hD hcalc τ0
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
        (smoothBallSobolev 2 v)) := by
  exact (sphereSobolevInclusionL_nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0
    (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2
      (smoothBallSobolev 3 v))).trans
        (congrArg (nativeHalfOutwardTraceL hF hO hD hcalc τ0)
          (lowerOrder_referenceHarmonicLiftFamily_smoothDatum_one
            g L y0 Φ B ε C ρ H a w hData hcalc hreg p lam Lam hUE hsmall v))

lemma contDiffAt_referenceSmoothDatumHighRadialSection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (v : SmoothData) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞
      (referenceSmoothDatumHighRadialSection g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 v) p := by
  have hLift := (contDiffAt_joint_referenceHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 1 p hi).clm_apply
      (contDiffAt_const (c := smoothBallSobolev 3 v))
  exact (nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0).contDiff.contDiffAt.comp p hLift

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSmoothDatumHighRadialSection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.lowerOrder_referenceHarmonicLiftFamily_smoothDatum_one
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_referenceSmoothDatumHighRadialSection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceSmoothDatumHighRadialSection

