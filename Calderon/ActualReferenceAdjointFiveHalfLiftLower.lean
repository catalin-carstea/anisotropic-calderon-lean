import Calderon.ActualReferenceAdjointFiveHalfLift
import Calderon.ActualReferenceAdjointH2LiftFamily
import Calderon.ActualAdjointHarmonicProjectionOrderCoherence
import Calderon.NativeFiveHalfHarmonicCoherence
import Calderon.ActualReferenceAdjointH3LowerCoherence

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeFiveHalfHarmonicLift NativeHarmonicLiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceAdjointH2LiftFamily_eq_projection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2:ℝ)) :
    referenceAdjointH2LiftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF p f =
      strongHarmonicProjectionL 0
        (referenceAdjointOrdinaryStrongFamily
          g L y0 Φ B ε C ρ H a w hData hcalc p)
        (harmonicLiftCompletion hF f) := rfl

lemma lowerOrder_referenceAdjointStrongHarmonicProjectionOne
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus)
    (hreg : FixedDirichletRegularity) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (U : BallSobolev 3) :
    nativeLowerOrderL 2
      (strongHarmonicProjectionL 1
        (referenceAdjointOrdinaryStrongFamilyOne
          g L y0 Φ B ε C ρ H a w hData hcalc p) U) =
    strongHarmonicProjectionL 0
      (referenceAdjointOrdinaryStrongFamily
        g L y0 Φ B ε C ρ H a w hData hcalc p)
      (nativeLowerOrderL 2 U) := by
  exact lowerOrder_strongHarmonicProjectionL_one
    (referenceAdjointOrdinaryStrongFamilyOne
      g L y0 Φ B ε C ρ H a w hData hcalc p)
    (referenceAdjointOrdinaryStrongFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p)
    (value_referenceAdjointOrdinaryStrongFamilyOne_eq_zero
      g L y0 Φ B ε C ρ H a w hData hcalc p)
    (referenceAdjointStrongDirichletFamilyOne_isInvertible
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hreg p hOriginal)
    (referenceAdjointStrongDirichletFamily_isInvertible
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hreg p hOriginal) U

/-- The SAME H³ full-adjoint solution lowers to the established H² solution
for included H5/2 boundary data. -/
theorem lowerOrder_referenceAdjointFiveHalfLiftFamily
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus)
    (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (5/2:ℝ)) :
    nativeLowerOrderL 2
      (referenceAdjointFiveHalfLiftFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF p f) =
    referenceAdjointH2LiftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF p
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f) := by
  calc
    _ = strongHarmonicProjectionL 0
        (referenceAdjointOrdinaryStrongFamily
          g L y0 Φ B ε C ρ H a w hData hcalc p)
          (nativeLowerOrderL 2 (harmonicLiftCompletion hF f)) :=
      lowerOrder_referenceAdjointStrongHarmonicProjectionOne
        g L y0 Φ B ε C ρ H a w hData τ0 hcalc hreg p hOriginal
          (harmonicLiftCompletion hF f)
    _ = strongHarmonicProjectionL 0
        (referenceAdjointOrdinaryStrongFamily
          g L y0 Φ B ε C ρ H a w hData hcalc p)
          (NativeHarmonicLiftCompletion.harmonicLiftCompletion hF
            (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f)) := by
      rw [nativeLowerOrderL_apply,
        lowerOrder_harmonicLiftCompletion hF hO]
    _ = _ := (referenceAdjointH2LiftFamily_eq_projection
      g L y0 Φ B ε C ρ H a w hData hcalc hF p _).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
