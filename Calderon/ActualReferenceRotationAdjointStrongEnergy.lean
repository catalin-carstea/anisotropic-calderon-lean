import Calderon.ActualReferenceRotationAdjointLowerEnergy
import Calderon.ActualReferenceRotationPrincipalForcingEnergy
import Calderon.NativeAdjointEnergyScalarAssembly
import Calderon.DirichletForcingInjectivity
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
variable (iA jA : Fin 3)
include hData

lemma referenceRotationAdjointMassForcingFamily_apply (hcalc : FixedSobolevCalculus)
    (t : ℝ × (ℝ × (R3 × ℝ))) (U : BallSobolev 2) :
    referenceRotationAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc iA jA t U =
      nativeCoefficientMassL hcalc (referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA t)
        (TauCeti.Wkp.firstOrder 1 U) :=
  congrArg (nativeCoefficientMassL hcalc
    (referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA t)) (nativeH2FirstOrderL_apply U)

lemma dirichletForcing_referenceRotationAdjointOrdinaryStrongFamily_sum
    (hcalc : FixedSobolevCalculus) (t : ℝ × (ℝ × (R3 × ℝ))) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (referenceRotationAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc iA jA t U) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (ordinaryPrincipalL hcalc 0 (nativePrincipalTransposeJets
          (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA t)) U) v +
      (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (ordinaryPrincipalL hcalc 0 (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA t) U) v -
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc iA jA t U) v) +
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (referenceRotationAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc iA jA t U) v := by
  simp only [referenceRotationAdjointOrdinaryStrongFamily,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,TauCeti.PDE.dirichletForcing_apply,inner_add_left,inner_sub_left]

lemma referenceRotationAdjointOrdinaryStrongFamily_energy (hcalc : FixedSobolevCalculus)
    (t : ℝ × (ℝ × (R3 × ℝ))) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (referenceRotationAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc iA jA t U) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (coordinateRotationPrincipalFamily iA jA a (t,x))ᵀ)
        (fun x => -coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        (fun x => -nativeSupportedDriftDivergence
          (fun y => coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
        (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  let u : BallH1 := TauCeti.Wkp.firstOrder 1 U
  have hP := referenceRotationOrdinaryPrincipalForcing_energy g L y0 Φ B ε C ρ H a w hData hcalc iA jA t U v
  have hPT := referenceRotationTransposePrincipalForcing_energy g L y0 Φ B ε C ρ H a w hData hcalc iA jA t U v
  have hO := referenceRotationOrdinaryStrongFamily_zero_forcing_energy g L y0 Φ B ε C ρ H a w hData hcalc iA jA t U v
  have hOrig := referenceRotationOriginalLowerEnergy_decomposition g L y0 Φ B ε C ρ H a w hData iA jA hcalc t u v
  have hAdj := referenceRotationAdjointLowerEnergy_decomposition g L y0 Φ B ε C ρ H a w hData iA jA hcalc t u v
  have hSum := dirichletForcing_referenceRotationAdjointOrdinaryStrongFamily_sum g L y0 Φ B ε C ρ H a w hData iA jA hcalc t U v
  have hMass := referenceRotationAdjointMassForcingFamily_apply g L y0 Φ B ε C ρ H a w hData iA jA hcalc t U
  have hSumMass := hSum.trans (congrArg (fun m : BallSobolev 0 =>
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0 (nativePrincipalTransposeJets
        (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA t)) U) v +
    (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0 (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA t) U) v -
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc iA jA t U) v) +
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) m v) hMass)
  exact eq_adjoint_energy_of_principal_drift_mass _ _ _ _ _ _ _ _ _ _
    hSumMass hP hPT hO hOrig hAdj

lemma referenceRotationAdjointOrdinaryStrongFamily_eq_nativeSupportedAdjointStrongL
    (hcalc : FixedSobolevCalculus) (t : ℝ × (ℝ × (R3 × ℝ))) :
    referenceRotationAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc iA jA t =
      nativeSupportedAdjointStrongL hcalc
        (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA t) 0
        (fun x => coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        (SpatialJetFields.contDiff_spatial_slice _
          (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData iA jA).1 t)
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
        ((referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData iA jA).2 t) := by
  apply ContinuousLinearMap.ext
  intro U
  apply unitBallDirichletForcing_eq_of_forall
  intro v
  have hNative := nativeSupportedAdjointStrongL_energy hcalc
    (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA t) 0
    (fun x => coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    (SpatialJetFields.contDiff_spatial_slice _
      (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData iA jA).1 t)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    ((referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData iA jA).2 t) U v
  have hzero : coefficientValue 1 (0 : SmoothCoefficientJets 1) = (0 : R3 → ℝ) := rfl
  have hNativeLiteral := hNative
  simp only [coefficientMatrixField_referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA t,
    hzero,Pi.zero_apply,zero_sub] at hNativeLiteral
  exact (referenceRotationAdjointOrdinaryStrongFamily_energy g L y0 Φ B ε C ρ H a w hData iA jA hcalc t U v).trans
    hNativeLiteral.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointMassForcingFamily_apply

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.dirichletForcing_referenceRotationAdjointOrdinaryStrongFamily_sum

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointOrdinaryStrongFamily_energy

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointOrdinaryStrongFamily_eq_nativeSupportedAdjointStrongL
