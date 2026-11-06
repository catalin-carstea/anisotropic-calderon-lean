import Calderon.ActualReferenceTwoAngleAdjointLowerEnergy
import Calderon.ActualReferenceTwoAnglePrincipalForcingEnergy
import Calderon.NativeAdjointEnergyScalarAssembly
import Calderon.DirichletForcingInjectivity
/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-adjoint-strong-energy-v039.md. -/
set_option autoImplicit false
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
variable (iA jA kA lA : Fin 3)
include hData

lemma referenceTwoAngleAdjointMassForcingFamily_apply (hcalc : FixedSobolevCalculus)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (U : BallSobolev 2) :
    referenceTwoAngleAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc iA jA kA lA t U =
      nativeCoefficientMassL hcalc (referenceTwoAngleAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA t)
        (TauCeti.Wkp.firstOrder 1 U) :=
  congrArg (nativeCoefficientMassL hcalc
    (referenceTwoAngleAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA t)) (nativeH2FirstOrderL_apply U)

lemma dirichletForcing_referenceTwoAngleAdjointOrdinaryStrongFamily_sum
    (hcalc : FixedSobolevCalculus) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (referenceTwoAngleAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc iA jA kA lA t U) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (ordinaryPrincipalL hcalc 0 (nativePrincipalTransposeJets
          (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA kA lA t)) U) v +
      (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (ordinaryPrincipalL hcalc 0 (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA kA lA t) U) v -
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (referenceTwoAngleOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc iA jA kA lA t U) v) +
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (referenceTwoAngleAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc iA jA kA lA t U) v := by
  simp only [referenceTwoAngleAdjointOrdinaryStrongFamily,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,TauCeti.PDE.dirichletForcing_apply,inner_add_left,inner_sub_left]

lemma referenceTwoAngleAdjointOrdinaryStrongFamily_energy (hcalc : FixedSobolevCalculus)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (referenceTwoAngleAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc iA jA kA lA t U) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (referenceTwoAnglePrincipalFamily a iA jA kA lA (t,x))ᵀ)
        (fun x => -referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x))
        (fun x => -nativeSupportedDriftDivergence
          (fun y => referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,y)) x)
        (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  let u : BallH1 := TauCeti.Wkp.firstOrder 1 U
  have hP := referenceTwoAngleOrdinaryPrincipalForcing_energy g L y0 Φ B ε C ρ H a w hData hcalc iA jA kA lA t U v
  have hPT := referenceTwoAngleTransposePrincipalForcing_energy g L y0 Φ B ε C ρ H a w hData hcalc iA jA kA lA t U v
  have hO := referenceTwoAngleOrdinaryStrongFamily_zero_forcing_energy g L y0 Φ B ε C ρ H a w hData hcalc iA jA kA lA t U v
  have hOrig := referenceTwoAngleOriginalLowerEnergy_decomposition g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t u v
  have hAdj := referenceTwoAngleAdjointLowerEnergy_decomposition g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t u v
  have hSum := dirichletForcing_referenceTwoAngleAdjointOrdinaryStrongFamily_sum g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t U v
  have hMass := referenceTwoAngleAdjointMassForcingFamily_apply g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t U
  have hSumMass := hSum.trans (congrArg (fun m : BallSobolev 0 =>
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0 (nativePrincipalTransposeJets
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA kA lA t)) U) v +
    (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0 (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA kA lA t) U) v -
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (referenceTwoAngleOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc iA jA kA lA t U) v) +
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) m v) hMass)
  exact eq_adjoint_energy_of_principal_drift_mass _ _ _ _ _ _ _ _ _ _
    hSumMass hP hPT hO hOrig hAdj

lemma referenceTwoAngleAdjointOrdinaryStrongFamily_eq_nativeSupportedAdjointStrongL
    (hcalc : FixedSobolevCalculus) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    referenceTwoAngleAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc iA jA kA lA t =
      nativeSupportedAdjointStrongL hcalc
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA kA lA t) 0
        (fun x => referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x))
        (SpatialJetFields.contDiff_spatial_slice _
          (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).1 t)
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
        ((referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).2 t) := by
  apply ContinuousLinearMap.ext
  intro U
  apply unitBallDirichletForcing_eq_of_forall
  intro v
  have hNative := nativeSupportedAdjointStrongL_energy hcalc
    (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA kA lA t) 0
    (fun x => referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x))
    (SpatialJetFields.contDiff_spatial_slice _
      (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).1 t)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    ((referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).2 t) U v
  have hzero : coefficientValue 1 (0 : SmoothCoefficientJets 1) = (0 : R3 → ℝ) := rfl
  have hNativeLiteral := hNative
  simp only [coefficientMatrixField_referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA kA lA t,
    hzero,Pi.zero_apply,zero_sub] at hNativeLiteral
  exact (referenceTwoAngleAdjointOrdinaryStrongFamily_energy g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t U v).trans
    hNativeLiteral.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointMassForcingFamily_apply

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.dirichletForcing_referenceTwoAngleAdjointOrdinaryStrongFamily_sum

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointOrdinaryStrongFamily_energy

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointOrdinaryStrongFamily_eq_nativeSupportedAdjointStrongL
