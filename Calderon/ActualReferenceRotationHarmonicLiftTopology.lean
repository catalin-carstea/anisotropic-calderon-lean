import Calderon.ActualReferenceRotationStrongRoom
import Calderon.ActualReferenceSharpUpperTrace
import Calderon.GuardedHarmonicLift

/-! Expanded first in EXPANSION-actual-rotation-strong-zero-room-lift-author-v001.json. -/
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


def referenceRotationHarmonicLiftFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    (ℝ × (ℝ × (R3 × ℝ))) → BallSobolev 2 →L[ℝ] BallSobolev 2 :=
  guardedHarmonicLiftFamily (strongDirichletSubmodule 0).toSubmodule.subtypeL
    (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j)
    (referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j)

lemma referenceRotationHarmonicLiftFamily_zero_angle
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    referenceRotationHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j (0,p) =
      referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 := by
  unfold referenceRotationHarmonicLiftFamily referenceHarmonicLiftFamily guardedHarmonicLiftFamily
  rw [referenceRotationStrongDirichletFamily_zero_angle,referenceRotationOrdinaryStrongFamily_zero_angle]

lemma referenceRotationHarmonicLiftFamily_kernel
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hi : (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).IsInvertible)
    (E : BallSobolev 2) :
    referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
      (referenceRotationHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t E) = 0 :=
  guardedHarmonicLiftFamily_kernel _ _ _ t hi rfl E

lemma contDiffAt_referenceRotationHarmonicLiftFamily
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hi : (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceRotationHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) t := by
  letI : CompleteSpace (StrongDirichletSpace 0) := instCompleteSpaceStrongDirichletSpace 0
  exact contDiffAt_guardedHarmonicLiftFamily (strongDirichletSubmodule 0).toSubmodule.subtypeL
    (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j)
    (contDiff_referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j)
    (referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j)
    (contDiff_referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) t hi

def referenceRotationSharpRadialTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (nativeHalfOutwardTraceL hF hO hD hcalc τ0).comp
    ((referenceRotationHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).comp
      (harmonicLiftCompletion hF))

lemma referenceRotationSharpRadialTraceFamily_zero_angle
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    referenceRotationSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (0,p) =
      referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p := by
  exact congrArg (fun T : BallSobolev 2 →L[ℝ] BallSobolev 2 =>
    (nativeHalfOutwardTraceL hF hO hD hcalc τ0).comp (T.comp (harmonicLiftCompletion hF)))
    (referenceRotationHarmonicLiftFamily_zero_angle g L y0 Φ B ε C ρ H a w hData hcalc i j p)

lemma contDiffAt_referenceRotationSharpRadialTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hi : (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceRotationSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) t := by
  have hLift := contDiffAt_referenceRotationHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j t hi
  have hComp := hLift.clm_comp (contDiffAt_const (c := harmonicLiftCompletion hF))
  exact (contDiffAt_const (c := nativeHalfOutwardTraceL hF hO hD hcalc τ0)).clm_comp hComp

lemma contDiffOn_referenceRotationSharpRadialTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (referenceRotationSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j)
      (referenceRotationStrongInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc i j) := by
  intro t ht
  exact (contDiffAt_referenceRotationSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t ht).contDiffWithinAt

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationHarmonicLiftFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationHarmonicLiftFamily_zero_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationHarmonicLiftFamily_kernel
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRotationHarmonicLiftFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationSharpRadialTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationSharpRadialTraceFamily_zero_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRotationSharpRadialTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRotationSharpRadialTraceFamily
