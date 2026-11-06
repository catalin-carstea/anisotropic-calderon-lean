import Calderon.ActualReferenceAdjointWeakEnergyRestriction
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

def referenceAdjointWeakHalfLiftFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 :=
  ((ContinuousLinearMap.id ℝ BallH1)-
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
      ((nativeZeroFunctionalInverse
        (referenceAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)).comp
        (referenceAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p))).comp
      (harmonicFirstOrderLiftCompletion hF)

lemma referenceAdjointWeakHalfLiftFamily_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (1/2:ℝ)) :
    referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f =
      harmonicFirstOrderLiftCompletion hF f-
        (nativeZeroFunctionalInverse
          (referenceAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)
          (referenceAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
            (harmonicFirstOrderLiftCompletion hF f)) : BallH1) :=
  nativeWeakAffineLiftAssembly_apply
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    (nativeZeroFunctionalInverse
      (referenceAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p))
    (referenceAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)
    (harmonicFirstOrderLiftCompletion hF) f

lemma contDiffAt_referenceAdjointWeakHalfLiftFamily_of_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF) p := by
  have hi := referenceAdjointWeakZeroEnergyFamily_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc p hOriginal
  have hI := contDiffAt_nativeParameterNativeZeroFunctionalInverse
    (referenceAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc) p
    (contDiff_referenceAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc).contDiffAt hi
  exact contDiffAt_nativeParameterHalfAffineLiftFormula
    (fun q => nativeZeroFunctionalInverse
      (referenceAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc q))
    (referenceAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc) hF p hI
    (contDiff_referenceAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc).contDiffAt

lemma contDiffOn_referenceAdjointWeakHalfLiftFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiffOn ℝ ∞ (referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  intro p hp
  exact (contDiffAt_referenceAdjointWeakHalfLiftFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF p hp.2.1).contDiffWithinAt

lemma referenceAdjointWeakHalfLiftFamily_affine_difference
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (1/2:ℝ)) :
    harmonicFirstOrderLiftCompletion hF f-
      referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f ∈
      TauCeti.w1p0Submodule volume ballOpens 2 := by
  let P : BallH1 := harmonicFirstOrderLiftCompletion hF f
  let z : BallH1Zero := nativeZeroFunctionalInverse
    (referenceAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)
    (referenceAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p P)
  have hEval : referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f =
      P-(z : BallH1) :=
    referenceAdjointWeakHalfLiftFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc hF p f
  have hDifference : P-referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f =
      (z : BallH1) :=
    (congrArg (fun u : BallH1 => P-u) hEval).trans (sub_sub_cancel P (z : BallH1))
  exact Eq.mp (congrArg (fun u : BallH1 => u ∈ TauCeti.w1p0Submodule volume ballOpens 2)
    hDifference.symm) z.property

lemma referenceAdjointWeakHalfLiftFamily_weak_solution
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (1/2:ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (a (p,x))ᵀ) (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
      (fun x => -nativeSupportedDriftDivergence
        (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)
      (referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) (v : BallH1) = 0 := by
  let A := referenceAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
  let R := referenceAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
  let I := nativeZeroFunctionalInverse A
  let J := (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
  have hi := referenceAdjointWeakZeroEnergyFamily_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc p hOriginal
  have hRestrict := referenceAdjointWeakEnergyFamily_restriction g L y0 Φ B ε C ρ H a w hData τ0 hcalc p
  have hCancel (ell : StrongDual ℝ BallH1Zero) (z : BallH1Zero) : R (J (I ell)) z=ell z :=
    (congrArg (fun T : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => T (I ell) z) hRestrict).trans
      (nativeZeroFunctionalInverse_self A hi ell z)
  have hKernel := nativeWeakAffineLiftAssembly_kernel J I R (harmonicFirstOrderLiftCompletion hF) hCancel f v
  exact (referenceAdjointWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p
    (referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) v).symm.trans hKernel

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakHalfLiftFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakHalfLiftFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceAdjointWeakHalfLiftFamily_of_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceAdjointWeakHalfLiftFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakHalfLiftFamily_affine_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakHalfLiftFamily_weak_solution
