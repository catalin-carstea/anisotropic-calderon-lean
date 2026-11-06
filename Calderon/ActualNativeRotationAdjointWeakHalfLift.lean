import Calderon.ActualReferenceRotationAdjointWeakHalfLiftFamily
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

lemma memLp_referenceRotationAdjointEnergyIntegrand (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand ((coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
      (-coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      (-nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  have ha : Continuous (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ) :=
    (SpatialJetFields.contDiff_spatial_slice _
      (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1 t).continuous.matrix_transpose
  have hb : Continuous (fun x => -coordinateRotationDriftFamily i j
      (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) :=
    (SpatialJetFields.contDiff_spatial_slice _
      (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1 t).continuous.neg
  have hm : Continuous (coefficientValue 1
      (referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j t)) :=
    (contDiff_coefficientValue 1 _).continuous
  exact memLp_nativeEnergyIntegrand_of_continuous _ _ _ ha hb
    (hm.congr (coefficientValue_referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j t))

lemma referenceRotationAdjointWeakZeroEnergyFamily_eq_native
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t =
      nativeZeroCoefficientEnergyL (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
        (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        (fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
        (memLp_referenceRotationAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData i j t) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have hRestriction := congrArg
    (fun T : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => T u v)
    (referenceRotationAdjointWeakEnergyFamily_restriction g L y0 Φ B ε C ρ H a w hData τ0 hcalc i j t)
  have hActual := referenceRotationAdjointWeakEnergyFamily_apply
    g L y0 Φ B ε C ρ H a w hData hcalc i j t (u : BallH1) v
  exact (hRestriction.symm.trans hActual).trans
    (nativeZeroCoefficientEnergyL_eval_to_H1 (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
      (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      (fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j
        (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
      (memLp_referenceRotationAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData i j t) u v).symm

lemma referenceRotationAdjointRawZeroEnergy_isInvertible
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible) :
    (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
      (b := fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      (c := fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
      (memLp_referenceRotationAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData i j t)).IsInvertible := by
  have hAdj := referenceRotationAdjointWeakZeroEnergyFamily_isInvertible_of_original g L y0 Φ B ε C ρ H a w hData hcalc i j t.1 t.2 hOriginal
  have he := referenceRotationAdjointWeakZeroEnergyFamily_eq_native g L y0 Φ B ε C ρ H a w hData τ0 hcalc i j t
  have hNative := Eq.mp (congrArg
    (fun A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => A.IsInvertible) he) hAdj
  exact (nativeZeroCoefficientEnergyL_isInvertible_iff (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
    (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    (fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
    (memLp_referenceRotationAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData i j t)).mp hNative

lemma referenceRotationAdjointWeakHalfLiftFamily_eq_native
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible)
    (f : SphereSobolev (1/2:ℝ)) :
    referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f =
      nativeWeakHalfLift (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
        (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        (fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
        (memLp_referenceRotationAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData i j t) hF f := by
  exact (nativeWeakHalfLift_unique (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
    (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    (fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
    (memLp_referenceRotationAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData i j t) hF
    (referenceRotationAdjointRawZeroEnergy_isInvertible g L y0 Φ B ε C ρ H a w hData τ0 hcalc i j t hOriginal) f
    (referenceRotationAdjointWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f)
    (referenceRotationAdjointWeakHalfLiftFamily_affine_difference g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f)
    (referenceRotationAdjointWeakHalfLiftFamily_weak_solution g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF i j t hOriginal f)).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.memLp_referenceRotationAdjointEnergyIntegrand
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakZeroEnergyFamily_eq_native
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointRawZeroEnergy_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakHalfLiftFamily_eq_native
