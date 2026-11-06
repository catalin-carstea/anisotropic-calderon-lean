import Calderon.ActualReferenceRotationAdjointWeakZeroInverse
import Calderon.NativeSupportedAdjointWeakSolution
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceRotationWeakDirichletEnergyFamily_apply (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (u v : BallH1Zero) :
    referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => coordinateRotationPrincipalFamily i j a (t,x))
        (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        0 (u : BallH1) (v : BallH1) := by
  unfold referenceRotationWeakDirichletEnergyFamily referenceRotationWeakEnergyFamily
  simp only [ContinuousLinearMap.comp_apply,nativeH1ZeroDualRestrictionL_apply,Submodule.subtypeL_apply]
  exact referenceRotationFullWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc i j t (u : BallH1) (v : BallH1)

lemma referenceRotationWeakDirichletEnergyFamily_eq_nativeSupportedOriginalZeroEnergyL
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    referenceRotationWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t =
      nativeSupportedOriginalZeroEnergyL
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
  have hNative := nativeZeroCoefficientEnergyL_eval_to_H1 (coefficientMatrixField 2 F) beta
    (coefficientValue 1 (0 : SmoothCoefficientJets 1))
    (nativeSupportedOriginalEnergyMemLp (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) 0 beta hbeta) u v
  have hField := coefficientMatrixField_referenceRotationPrincipalJetsFamily
    g L y0 Φ B ε C ρ H a w hData 2 i j t
  have hZero : coefficientValue 1 (0 : SmoothCoefficientJets 1) = (0 : R3 → ℝ) := rfl
  have hNormalize := congrArg (fun A : MatrixField => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A beta
    (coefficientValue 1 (0 : SmoothCoefficientJets 1)) (u : BallH1) (v : BallH1)) hField
  have hMass := congrArg (fun c : R3 → ℝ => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun x => coordinateRotationPrincipalFamily i j a (t,x)) beta c (u : BallH1) (v : BallH1)) hZero
  exact (referenceRotationWeakDirichletEnergyFamily_apply
    g L y0 Φ B ε C ρ H a w hData hcalc i j t u v).trans
      (hNative.trans (hNormalize.trans hMass)).symm

lemma referenceRotationSupportedOriginalZeroEnergyL_isInvertible_of_original
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (nativeSupportedOriginalZeroEnergyL
      (coefficientMatrixField 2 (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j (θ,p)))
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth
        (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j (θ,p))) 0
      (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) ((θ,p),x))
      (SpatialJetFields.contDiff_spatial_slice _
        (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1 (θ,p))).IsInvertible :=
  Eq.mp (congrArg (fun A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => A.IsInvertible)
    (referenceRotationWeakDirichletEnergyFamily_eq_nativeSupportedOriginalZeroEnergyL
      g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p)))
    (referenceRotationWeakDirichletEnergyFamily_isInvertible_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc i j θ p hOriginal)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakDirichletEnergyFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakDirichletEnergyFamily_eq_nativeSupportedOriginalZeroEnergyL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationSupportedOriginalZeroEnergyL_isInvertible_of_original
