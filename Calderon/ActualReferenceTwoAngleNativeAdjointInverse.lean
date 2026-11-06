import Calderon.ActualReferenceTwoAngleNativeEnergyIdentification
import Calderon.ActualReferenceTwoAngleWeakCovariance
import Calderon.ActualReferenceRotationPrincipalEllipticity
import Calderon.NativeSupportedAdjointStrongInvertibility

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SmoothSphereRotation
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

include hData in
lemma exists_referenceTwoAnglePrincipal_uniformlyElliptic_on_compact
    (Kp : Set (ℝ × (R3 × ℝ))) (hKp : IsCompact Kp) :
    ∃ lam Lam : ℝ, ∀ i j k l : Fin 3, ∀ θ φ : ℝ, ∀ p ∈ Kp,
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
        (fun x => referenceTwoAnglePrincipalFamily a i j k l ((θ,(φ,p)),x)) lam Lam := by
  obtain ⟨lam,Lam,hUE⟩ := exists_referenceRotationPrincipal_uniformlyElliptic_on_compact
    g L y0 Φ B ε C ρ H a w hData Kp hKp
  refine ⟨lam,Lam,?_⟩
  intro i j k l θ φ p hp
  have hRot := uniformlyEllipticOn_orthogonalPrincipalCoefficient
    (coordinateRotationIsometry i j θ)
    (fun x => coordinateRotationPrincipalFamily k l a ((φ,p),x)) lam Lam (hUE k l φ p hp)
  have hField : (fun x => referenceTwoAnglePrincipalFamily a i j k l ((θ,(φ,p)),x)) =
      orthogonalPrincipalCoefficient (coordinateRotationIsometry i j θ)
        (fun x => coordinateRotationPrincipalFamily k l a ((φ,p),x)) :=
    funext (coordinateRotationPrincipalFamily_eq_orthogonal i j (coordinateRotationPrincipalFamily k l a) θ (φ,p))
  exact Eq.mp (congrArg (fun A : MatrixField =>
    TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) A lam Lam) hField.symm) hRot

lemma referenceTwoAngleWeakDirichletEnergyFamily_eq_nativeSupportedOriginalZeroEnergyL
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    referenceTwoAngleWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t =
      nativeSupportedOriginalZeroEnergyL
        (coefficientMatrixField 2 (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t))
        (memLp_coefficientMatrixEnergyIntegrand_of_smooth
          (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)) 0
        (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
        (SpatialJetFields.contDiff_spatial_slice _
          (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1 t) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  let F := referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t
  let beta : R3 → R3 := fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)
  have hbeta : ContDiff ℝ ∞ beta := SpatialJetFields.contDiff_spatial_slice _
    (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1 t
  have hNative := nativeZeroCoefficientEnergyL_eval_to_H1 (coefficientMatrixField 2 F) beta
    (coefficientValue 1 (0 : SmoothCoefficientJets 1))
    (nativeSupportedOriginalEnergyMemLp (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) 0 beta hbeta) u v
  have hField := coefficientMatrixField_referenceTwoAnglePrincipalJetsFamily
    g L y0 Φ B ε C ρ H a w hData 2 i j k l t
  have hZero : coefficientValue 1 (0 : SmoothCoefficientJets 1) = (0 : R3 → ℝ) := rfl
  have hNormalize := congrArg (fun A : MatrixField => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A beta
    (coefficientValue 1 (0 : SmoothCoefficientJets 1)) (u : BallH1) (v : BallH1)) hField
  have hMass := congrArg (fun c : R3 → ℝ => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x)) beta c (u : BallH1) (v : BallH1)) hZero
  have hActual : referenceTwoAngleWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x)) beta 0 (u : BallH1) (v : BallH1) := by
    simpa only [referenceTwoAngleWeakDirichletEnergyFamily,referenceTwoAngleWeakEnergyFamily,
      ContinuousLinearMap.comp_apply,nativeH1ZeroDualRestrictionL_apply,Submodule.subtypeL_apply] using
      referenceTwoAngleFullWeakEnergyFamily_apply
        g L y0 Φ B ε C ρ H a w hData hcalc i j k l t (u : BallH1) (v : BallH1)
  exact hActual.trans (hNative.trans (hNormalize.trans hMass)).symm

lemma referenceTwoAngleSupportedOriginalZeroEnergyL_isInvertible_of_original
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (θ φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (nativeSupportedOriginalZeroEnergyL
      (coefficientMatrixField 2 (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l (θ,(φ,p))))
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l (θ,(φ,p)))) 0
      (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l ((θ,(φ,p)),x))
      (SpatialJetFields.contDiff_spatial_slice _
        (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1 (θ,(φ,p)))).IsInvertible :=
  Eq.mp (congrArg (fun A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => A.IsInvertible)
    (referenceTwoAngleWeakDirichletEnergyFamily_eq_nativeSupportedOriginalZeroEnergyL
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l (θ,(φ,p))))
    (referenceTwoAngleWeakDirichletEnergyFamily_isInvertible_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l θ φ p hOriginal)


lemma nativeReferenceTwoAngleSupportedAdjointZeroEnergyL_isInvertible
    (τ0 : UnitBallValueTrace)
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible) :
    (nativeSupportedAdjointZeroEnergyL
      (coefficientMatrixField 2 (referenceTwoAnglePrincipalJetsFamily
        g L y0 Φ B ε C ρ H a w hData 2 i j k l t))
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth (referenceTwoAnglePrincipalJetsFamily
        g L y0 Φ B ε C ρ H a w hData 2 i j k l t)) 0
      (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
      (SpatialJetFields.contDiff_spatial_slice _
        (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1 t)).IsInvertible := by
  let F := referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t
  let beta : R3 → R3 := fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)
  have hbeta : ContDiff ℝ ∞ beta := SpatialJetFields.contDiff_spatial_slice _
    (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1 t
  have hA : (nativeSupportedOriginalZeroEnergyL (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) 0 beta hbeta).IsInvertible :=
    referenceTwoAngleSupportedOriginalZeroEnergyL_isInvertible_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t.1 t.2.1 t.2.2 hOriginal
  exact nativeSupportedAdjointZeroEnergyL_isInvertible τ0 (coefficientMatrixField 2 F)
    (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) 0 beta hbeta hA

lemma nativeReferenceTwoAngleSupportedAdjointStrongDirichletL_isInvertible
    (τ0 : UnitBallValueTrace) (hreg : FixedDirichletRegularity)
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible) :
    (nativeSupportedAdjointStrongDirichletL hcalc
      (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t) 0
      (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
      (SpatialJetFields.contDiff_spatial_slice _
        (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1 t)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      ((referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).2 t)).IsInvertible := by
  let F := referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t
  let beta : R3 → R3 := fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)
  have hbeta : ContDiff ℝ ∞ beta := SpatialJetFields.contDiff_spatial_slice _
    (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1 t
  have hz : ∀ x, x ∉ closedBall (0 : R3) 3 → beta x = 0 :=
    (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).2 t
  obtain ⟨lam,Lam,hUE⟩ := exists_referenceTwoAnglePrincipal_uniformlyElliptic_on_compact
    g L y0 Φ B ε C ρ H a w hData {t.2.2} isCompact_singleton
  have hUEm := hUE i j k l t.1 t.2.1 t.2.2 (mem_singleton t.2.2)
  have hField := coefficientMatrixField_referenceTwoAnglePrincipalJetsFamily
    g L y0 Φ B ε C ρ H a w hData 2 i j k l t
  have hUEF : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField 2 F) lam Lam :=
    Eq.mp (congrArg (fun A : MatrixField => TauCeti.PDE.UniformlyEllipticOn
      (ballOpens : Set R3) A lam Lam) hField.symm) hUEm
  have hA : (nativeSupportedOriginalZeroEnergyL (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) 0 beta hbeta).IsInvertible :=
    referenceTwoAngleSupportedOriginalZeroEnergyL_isInvertible_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t.1 t.2.1 t.2.2 hOriginal
  exact nativeSupportedAdjointStrongDirichletL_isInvertible τ0 hcalc hreg F lam Lam hUEF
    0 beta hbeta (closedBall (0 : R3) 3) (isCompact_closedBall _ _) hz hA

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceTwoAnglePrincipal_uniformlyElliptic_on_compact
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleWeakDirichletEnergyFamily_eq_nativeSupportedOriginalZeroEnergyL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleSupportedOriginalZeroEnergyL_isInvertible_of_original
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeReferenceTwoAngleSupportedAdjointZeroEnergyL_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeReferenceTwoAngleSupportedAdjointStrongDirichletL_isInvertible
