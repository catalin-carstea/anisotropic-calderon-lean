import Calderon.ActualReferenceAdjointLowerEnergy
import Calderon.ActualReferencePrincipalForcingEnergy
import Calderon.NativeAdjointEnergyScalarAssembly
import Calderon.ActualReferenceAdjointStrongOperator
import Calderon.ActualReferencePrincipalGlobalEllipticity
import Calderon.ActualReferenceStrongWeakHalfCoherence
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
include hData

lemma referenceAdjointMassForcingFamily_apply (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (U : BallSobolev 2) :
    referenceAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc p U =
      nativeCoefficientMassL hcalc (referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p)
        (TauCeti.Wkp.firstOrder 1 U) :=
  congrArg (nativeCoefficientMassL hcalc
    (referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p)) (nativeH2FirstOrderL_apply U)

lemma dirichletForcing_referenceAdjointOrdinaryStrongFamily_sum
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ)) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (referenceAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc p U) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (ordinaryPrincipalL hcalc 0 (nativePrincipalTransposeJets
          (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p)) U) v +
      (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (ordinaryPrincipalL hcalc 0 (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p) U) v -
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 U) v) +
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (referenceAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc p U) v := by
  simp only [referenceAdjointOrdinaryStrongFamily,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,TauCeti.PDE.dirichletForcing_apply,inner_add_left,inner_sub_left]

lemma referenceAdjointOrdinaryStrongFamily_energy (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (referenceAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc p U) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (a (p,x))ᵀ)
        (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
        (fun x => -nativeSupportedDriftDivergence
          (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)
        (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  let u : BallH1 := TauCeti.Wkp.firstOrder 1 U
  have hP := referenceOrdinaryPrincipalForcing_energy g L y0 Φ B ε C ρ H a w hData hcalc p U v
  have hPT := referenceTransposePrincipalForcing_energy g L y0 Φ B ε C ρ H a w hData hcalc p U v
  have hO := referenceOrdinaryStrongDriftFamily_zero_forcing_energy g L y0 Φ B ε C ρ H a w hData hcalc p U v
  have hOrig := referenceOriginalLowerEnergy_decomposition g L y0 Φ B ε C ρ H a w hData hcalc p u v
  have hAdj := referenceAdjointLowerEnergy_decomposition g L y0 Φ B ε C ρ H a w hData hcalc p u v
  have hSum := dirichletForcing_referenceAdjointOrdinaryStrongFamily_sum g L y0 Φ B ε C ρ H a w hData hcalc p U v
  have hMass := referenceAdjointMassForcingFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p U
  have hSumMass := hSum.trans (congrArg (fun m : BallSobolev 0 =>
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0 (nativePrincipalTransposeJets
        (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p)) U) v +
    (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0 (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p) U) v -
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 U) v) +
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) m v) hMass)
  exact eq_adjoint_energy_of_principal_drift_mass _ _ _ _ _ _ _ _ _ _
    hSumMass hP hPT hO hOrig hAdj

lemma referenceAdjointOrdinaryStrongFamily_eq_nativeSupportedAdjointStrongL
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ)) :
    referenceAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc p =
      nativeSupportedAdjointStrongL hcalc
        (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p) 0
        (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
        (SpatialJetFields.contDiff_spatial_slice _
          (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1 p)
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
        ((jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).2 p) := by
  apply ContinuousLinearMap.ext
  intro U
  apply unitBallDirichletForcing_eq_of_forall
  intro v
  have hNative := nativeSupportedAdjointStrongL_energy hcalc
    (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p) 0
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
    (SpatialJetFields.contDiff_spatial_slice _
      (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1 p)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    ((jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).2 p) U v
  have hzero : coefficientValue 1 (0 : SmoothCoefficientJets 1) = (0 : R3 → ℝ) := rfl
  have hNativeLiteral := hNative
  simp only [coefficientMatrixField_referenceJointPrincipalJetsFamily,hzero,Pi.zero_apply,zero_sub] at hNativeLiteral
  exact (referenceAdjointOrdinaryStrongFamily_energy g L y0 Φ B ε C ρ H a w hData hcalc p U v).trans
    hNativeLiteral.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMassForcingFamily_apply

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.dirichletForcing_referenceAdjointOrdinaryStrongFamily_sum

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointOrdinaryStrongFamily_energy

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointOrdinaryStrongFamily_eq_nativeSupportedAdjointStrongL
