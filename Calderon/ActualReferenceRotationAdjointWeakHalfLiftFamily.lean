import Calderon.ActualReferenceRotationAdjointWeakEnergyRestriction
import Calderon.NativeParameterWeakLiftTopology
import Calderon.NativeCoefficientWeakHalfLift
import Calderon.ActualReferenceRadialEndpointOpenLocus

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceRotationAdjointWeakHalfLiftFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 :=
  ((ContinuousLinearMap.id ℝ BallH1)-
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
      ((nativeZeroFunctionalInverse
        (referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t)).comp
        (referenceRotationAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t))).comp
      (harmonicFirstOrderLiftCompletion hF)

lemma referenceRotationAdjointWeakHalfLiftFamily_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (f : SphereSobolev (1/2:ℝ)) :
    referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f =
      harmonicFirstOrderLiftCompletion hF f-
        (nativeZeroFunctionalInverse
          (referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t)
          (referenceRotationAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
            (harmonicFirstOrderLiftCompletion hF f)) : BallH1) :=
  nativeWeakAffineLiftAssembly_apply
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    (nativeZeroFunctionalInverse
      (referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t))
    (referenceRotationAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t)
    (harmonicFirstOrderLiftCompletion hF) f

lemma contDiffAt_referenceRotationAdjointWeakHalfLiftFamily_of_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j) t := by
  have hi := referenceRotationAdjointWeakZeroEnergyFamily_isInvertible_of_original g L y0 Φ B ε C ρ H a w hData hcalc i j t.1 t.2 hOriginal
  have hI := contDiffAt_nativeParameterNativeZeroFunctionalInverse
    (referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) t
    (contDiff_referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j).contDiffAt hi
  exact contDiffAt_nativeParameterHalfAffineLiftFormula
    (fun q => nativeZeroFunctionalInverse
      (referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j q))
    (referenceRotationAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) hF t hI
    (contDiff_referenceRotationAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j).contDiffAt

lemma contDiffOn_referenceRotationAdjointWeakHalfLiftFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j)
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  intro t ht
  exact (contDiffAt_referenceRotationAdjointWeakHalfLiftFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j t ht.2.2.1).contDiffWithinAt

lemma referenceRotationAdjointWeakHalfLiftFamily_affine_difference
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (f : SphereSobolev (1/2:ℝ)) :
    harmonicFirstOrderLiftCompletion hF f-
      referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f ∈
      TauCeti.w1p0Submodule volume ballOpens 2 := by
  let P : BallH1 := harmonicFirstOrderLiftCompletion hF f
  let z : BallH1Zero := nativeZeroFunctionalInverse
    (referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t)
    (referenceRotationAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t P)
  have hEval : referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f =
      P-(z : BallH1) :=
    referenceRotationAdjointWeakHalfLiftFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f
  have hDifference : P-referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f =
      (z : BallH1) :=
    (congrArg (fun u : BallH1 => P-u) hEval).trans (sub_sub_cancel P (z : BallH1))
  exact Eq.mp (congrArg (fun u : BallH1 => u ∈ TauCeti.w1p0Submodule volume ballOpens 2)
    hDifference.symm) z.property

lemma referenceRotationAdjointWeakHalfLiftFamily_weak_solution
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible)
    (f : SphereSobolev (1/2:ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ) (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      (fun x => -nativeSupportedDriftDivergence
        (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
      (referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f) (v : BallH1) = 0 := by
  let A := referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
  let R := referenceRotationAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
  let I := nativeZeroFunctionalInverse A
  let J := (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
  have hi := referenceRotationAdjointWeakZeroEnergyFamily_isInvertible_of_original g L y0 Φ B ε C ρ H a w hData hcalc i j t.1 t.2 hOriginal
  have hRestrict := referenceRotationAdjointWeakEnergyFamily_restriction g L y0 Φ B ε C ρ H a w hData τ0 hcalc i j t
  have hCancel (ell : StrongDual ℝ BallH1Zero) (z : BallH1Zero) : R (J (I ell)) z=ell z :=
    (congrArg (fun T : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => T (I ell) z) hRestrict).trans
      (nativeZeroFunctionalInverse_self A hi ell z)
  have hKernel := nativeWeakAffineLiftAssembly_kernel J I R (harmonicFirstOrderLiftCompletion hF) hCancel f v
  exact (referenceRotationAdjointWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc i j t
    (referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f) v).symm.trans hKernel

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakHalfLiftFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakHalfLiftFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRotationAdjointWeakHalfLiftFamily_of_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRotationAdjointWeakHalfLiftFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakHalfLiftFamily_affine_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakHalfLiftFamily_weak_solution
