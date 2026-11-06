import Calderon.ActualReferenceRotationAdjointFullWeakEnergy
import Calderon.ActualReferenceRotationSupportedZeroEnergyIdentity
import Calderon.NativeH1DualTestPostcompositionTopology
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma contDiff_nativeH1_dual_test_postcomposition_angle
    (Q : StrongDual ℝ BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (E : (ℝ × (ℝ × (R3 × ℝ))) → BallH1 →L[ℝ] StrongDual ℝ BallH1)
    (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × (R3 × ℝ)) => Q.comp (E p)) := by
  have hGeneric := contDiff_fixed_postcomposition
    (P := ℝ × (ℝ × (R3 × ℝ))) (U := BallH1)
    (V := StrongDual ℝ BallH1) (W := StrongDual ℝ BallH1Zero)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hGeneric
  exact hGeneric Q E hE


variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceRotationAdjointWeakEnergyFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
  nativeH1ZeroDualRestrictionL.comp
    (referenceRotationAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t)

lemma referenceRotationAdjointWeakEnergyFamily_apply (hcalc : FixedSobolevCalculus) (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) (u : BallH1) (v : BallH1Zero) :
    referenceRotationAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
        (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        (fun x => -nativeSupportedDriftDivergence
          (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x) u (v : BallH1) :=
  referenceRotationAdjointFullWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc i j t u (v : BallH1)

lemma contDiff_referenceRotationAdjointWeakEnergyFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) :=
  contDiff_nativeH1_dual_test_postcomposition_angle nativeH1ZeroDualRestrictionL
    (referenceRotationAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j)
    (contDiff_referenceRotationAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j)

lemma referenceRotationAdjointWeakEnergyFamily_restriction_eq_native (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    (referenceRotationAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).comp
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL =
      nativeSupportedAdjointZeroEnergyL
        (coefficientMatrixField 2 (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t))
        (memLp_coefficientMatrixEnergyIntegrand_of_smooth
          (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t)) 0
        (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        (SpatialJetFields.contDiff_spatial_slice _
          (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1 t) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  let F := referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t
  let beta : R3 → R3 := fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)
  have hbeta : ContDiff ℝ ∞ beta := SpatialJetFields.contDiff_spatial_slice _
    (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1 t
  let c : R3 → ℝ := fun x => coefficientValue 1 (0 : SmoothCoefficientJets 1) x-nativeSupportedDriftDivergence beta x
  have hNative := nativeZeroCoefficientEnergyL_eval_to_H1 (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta) c
    (nativeSupportedAdjointEnergyMemLp (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) 0 beta hbeta) u v
  have hField := congrArg (fun A : MatrixField => fun x => (A x)ᵀ)
    (coefficientMatrixField_referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t)
  have hNeg : (-beta : R3 → R3) =
      (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) := rfl
  have hMass : c = (fun x => -nativeSupportedDriftDivergence beta x) := by
    funext x
    change (0:ℝ)-nativeSupportedDriftDivergence beta x = _
    exact zero_sub _
  have hF := congrArg (fun A : MatrixField => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A (-beta) c (u : BallH1) (v : BallH1)) hField
  have hB := congrArg (fun b : R3 → R3 => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ) b c (u : BallH1) (v : BallH1)) hNeg
  have hC := congrArg (fun c : R3 → ℝ => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
    (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) c
    (u : BallH1) (v : BallH1)) hMass
  exact (referenceRotationAdjointWeakEnergyFamily_apply
    g L y0 Φ B ε C ρ H a w hData hcalc i j t (u : BallH1) v).trans
      (hNative.trans (hF.trans (hB.trans hC))).symm

lemma referenceRotationAdjointWeakEnergyFamily_restriction (τ0 : UnitBallValueTrace)
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    (referenceRotationAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).comp
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL =
    referenceRotationAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t := by
  let F := referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t
  let beta : R3 → R3 := fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)
  have hbeta : ContDiff ℝ ∞ beta := SpatialJetFields.contDiff_spatial_slice _
    (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1 t
  have hFlip := nativeSupportedAdjointZeroEnergyL_flip τ0 (coefficientMatrixField 2 F)
    (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) 0 beta hbeta
  have hOrig := referenceRotationWeakDirichletEnergyFamily_eq_nativeSupportedOriginalZeroEnergyL
    g L y0 Φ B ε C ρ H a w hData hcalc i j t
  have hFlipOrig := congrArg (fun A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => A.flip) hOrig.symm
  exact (referenceRotationAdjointWeakEnergyFamily_restriction_eq_native
    g L y0 Φ B ε C ρ H a w hData hcalc i j t).trans (hFlip.trans hFlipOrig)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_nativeH1_dual_test_postcomposition_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakEnergyFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationAdjointWeakEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakEnergyFamily_restriction_eq_native
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakEnergyFamily_restriction
