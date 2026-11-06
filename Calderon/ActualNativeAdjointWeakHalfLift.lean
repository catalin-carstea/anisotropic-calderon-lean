import Calderon.ActualReferenceAdjointWeakHalfLiftFamily
import Calderon.NativeCoefficientWeakHalfLiftUniqueness
import Calderon.NativeSupportedAdjointWeakSolution

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
include hData

lemma memLp_referenceAdjointEnergyIntegrand (p : ℝ × (R3 × ℝ)) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand ((a (p,x))ᵀ)
      (-conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
      (-nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  have ha : Continuous (fun x => (a (p,x))ᵀ) :=
    (SpatialJetFields.contDiff_spatial_slice a
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 p).continuous.matrix_transpose
  have hb : Continuous (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) :=
    (SpatialJetFields.contDiff_spatial_slice _
      (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1 p).continuous.neg
  have hm : Continuous (fun x => referenceAdjointMassFunction g L Φ H w (p,x)) :=
    (SpatialJetFields.contDiff_spatial_slice _
      (contDiff_referenceAdjointMassFunction g L y0 Φ B ε C ρ H a w hData) p).continuous
  have hLiteral (x : R3) : referenceAdjointMassFunction g L Φ H w (p,x) =
      -nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x :=
    congrArg (fun t : ℝ => -t)
      (referenceWeightedDriftDivergence_eq_native g L y0 Φ B ε C ρ H a w hData p x)
  exact memLp_nativeEnergyIntegrand_of_continuous (fun x => (a (p,x))ᵀ)
    (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
    (fun x => -nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)
    ha hb (hm.congr hLiteral)

lemma referenceAdjointWeakZeroEnergyFamily_eq_native
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ)) :
    referenceAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p =
      nativeZeroCoefficientEnergyL (fun x => (a (p,x))ᵀ)
        (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
        (fun x => -nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)
        (memLp_referenceAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData p) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact (referenceAdjointWeakZeroEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData τ0 hcalc p u v).trans
    (nativeZeroCoefficientEnergyL_eval_to_H1 (fun x => (a (p,x))ᵀ)
      (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
      (fun x => -nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)
      (memLp_referenceAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData p) u v).symm

lemma referenceAdjointRawZeroEnergy_isInvertible
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := fun x => (a (p,x))ᵀ)
      (b := fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
      (c := fun x => -nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)
      (memLp_referenceAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData p)).IsInvertible := by
  have hAdj := referenceAdjointWeakZeroEnergyFamily_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc p hOriginal
  have he := referenceAdjointWeakZeroEnergyFamily_eq_native g L y0 Φ B ε C ρ H a w hData τ0 hcalc p
  have hNative := Eq.mp (congrArg
    (fun A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => A.IsInvertible) he) hAdj
  exact (nativeZeroCoefficientEnergyL_isInvertible_iff (fun x => (a (p,x))ᵀ)
    (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
    (fun x => -nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)
    (memLp_referenceAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData p)).mp hNative

lemma referenceAdjointWeakHalfLiftFamily_eq_native
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (1/2:ℝ)) :
    referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f =
      nativeWeakHalfLift (fun x => (a (p,x))ᵀ)
        (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
        (fun x => -nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)
        (memLp_referenceAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData p) hF f := by
  exact (nativeWeakHalfLift_unique (fun x => (a (p,x))ᵀ)
    (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
    (fun x => -nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)
    (memLp_referenceAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData p) hF
    (referenceAdjointRawZeroEnergy_isInvertible g L y0 Φ B ε C ρ H a w hData τ0 hcalc p hOriginal) f
    (referenceAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
    (referenceAdjointWeakHalfLiftFamily_affine_difference g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
    (referenceAdjointWeakHalfLiftFamily_weak_solution g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF p hOriginal f)).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.memLp_referenceAdjointEnergyIntegrand
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakZeroEnergyFamily_eq_native
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointRawZeroEnergy_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakHalfLiftFamily_eq_native
