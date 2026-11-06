import Calderon.ActualReferenceTwoAngleStrongOriginalRoom
import Calderon.ActualReferenceRotationHarmonicLiftTopology
import Calderon.ActualReferenceSharpUpperTrace
import Calderon.GuardedHarmonicLift

/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-strong-lift-v010.md. Literal SAME strong lift and trace. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion NativeFullHalfRadialTrace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


def referenceTwoAngleHarmonicLiftFamily (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) :
    (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) → BallSobolev 2 →L[ℝ] BallSobolev 2 :=
  guardedHarmonicLiftFamily (strongDirichletSubmodule 0).toSubmodule.subtypeL
    (referenceTwoAngleStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l)
    (referenceTwoAngleOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l)

lemma referenceTwoAngleHarmonicLiftFamily_zero_outer_angle
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (φ : ℝ) (p : ℝ × (R3 × ℝ)) :
    referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l (0,(φ,p)) =
      referenceRotationHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p) := by
  unfold referenceTwoAngleHarmonicLiftFamily referenceRotationHarmonicLiftFamily guardedHarmonicLiftFamily
  rw [referenceTwoAngleStrongDirichletFamily_zero_outer_angle,
    referenceTwoAngleOrdinaryStrongFamily_zero_outer_angle]

lemma referenceTwoAngleHarmonicLiftFamily_kernel
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hi : (referenceTwoAngleStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible)
    (E : BallSobolev 2) :
    referenceTwoAngleOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
      (referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t E) = 0 :=
  guardedHarmonicLiftFamily_kernel _ _ _ t hi rfl E

lemma contDiffAt_referenceTwoAngleHarmonicLiftFamily
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hi : (referenceTwoAngleStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l) t := by
  letI : CompleteSpace (StrongDirichletSpace 0) := instCompleteSpaceStrongDirichletSpace 0
  exact contDiffAt_guardedHarmonicLiftFamily (strongDirichletSubmodule 0).toSubmodule.subtypeL
    (referenceTwoAngleStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l)
    (contDiff_referenceTwoAngleStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l)
    (referenceTwoAngleOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l)
    (contDiff_referenceTwoAngleOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l) t hi

def referenceTwoAngleSharpRadialTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (nativeHalfOutwardTraceL hF hO hD hcalc τ0).comp
    ((referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).comp
      (harmonicLiftCompletion hF))

lemma referenceTwoAngleSharpRadialTraceFamily_zero_outer_angle
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (φ : ℝ) (p : ℝ × (R3 × ℝ)) :
    referenceTwoAngleSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (0,(φ,p)) =
      referenceRotationSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l (φ,p) := by
  exact congrArg (fun T : BallSobolev 2 →L[ℝ] BallSobolev 2 =>
    (nativeHalfOutwardTraceL hF hO hD hcalc τ0).comp (T.comp (harmonicLiftCompletion hF)))
    (referenceTwoAngleHarmonicLiftFamily_zero_outer_angle
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l φ p)

lemma contDiffAt_referenceTwoAngleSharpRadialTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hi : (referenceTwoAngleStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceTwoAngleSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) t := by
  have hLift := contDiffAt_referenceTwoAngleHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t hi
  have hComp := hLift.clm_comp (contDiffAt_const (c := harmonicLiftCompletion hF))
  exact (contDiffAt_const (c := nativeHalfOutwardTraceL hF hO hD hcalc τ0)).clm_comp hComp

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleHarmonicLiftFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleHarmonicLiftFamily_zero_outer_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleHarmonicLiftFamily_kernel
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAngleHarmonicLiftFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleSharpRadialTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleSharpRadialTraceFamily_zero_outer_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAngleSharpRadialTraceFamily
