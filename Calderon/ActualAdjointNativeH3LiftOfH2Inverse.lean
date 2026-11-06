import Calderon.ActualAdjointMassH3Regularity
import Calderon.ActualAdjointNativeH2InverseWeak
import Calderon.NativeSupportedAdjointH2Regularity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Upgrade the SAME full supported adjoint H² inverse solution to H³.
The mass jets at orders one and two represent the same actual mass. -/
theorem exists_nativeAdjoint_H3_lift_of_H2_inverse
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (F : SmoothCoefficientMatrix 2) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField 2 F) lam Lam)
    (C M1 : SmoothCoefficientJets 1) (M2 : SmoothCoefficientJets 2)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0)
    (hM1 : coefficientValue 1 M1 =
      fun x => coefficientValue 1 C x - nativeSupportedDriftDivergence beta x)
    (hM2 : coefficientValue 2 M2 = coefficientValue 1 M1)
    (hA0 : (nativeSupportedAdjointStrongDirichletL
      hcalc F C beta hbeta K hK hz).IsInvertible)
    (f : BallSobolev 1) :
    ∃ U : BallSobolev 3,
      TauCeti.Wkp.firstOrder 2 U =
        ((strongDirichletProjectionL 0
          ((nativeSupportedAdjointStrongDirichletL
            hcalc F C beta hbeta K hK hz).inverse
              (nativeLowerOrderL 0 f))) : BallH1) := by
  let U0 : StrongDirichletSpace 0 :=
    (nativeSupportedAdjointStrongDirichletL hcalc F C beta hbeta K hK hz).inverse
      (nativeLowerOrderL 0 f)
  let u : BallH1Zero := strongDirichletProjectionL 0 U0
  let V : BallSobolev 2 := (U0 : BallSobolev 2)
  have hV : TauCeti.Wkp.firstOrder 1 V = (u : BallH1) :=
    (strongDirichletProjectionL_apply 0 U0).symm
  have huNative := nativeSupportedAdjointH2Inverse_weakSolution_highForcing
    hcalc F C beta hbeta K hK hz hA0 f
  have hu : TauCeti.PDE.IsWeakSolutionDirichlet
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
      (coefficientValue 1 M1) (TauCeti.Wkp.value 1 f) u := by
    rw [hM1]
    exact huNative
  have hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand
      ((coefficientMatrixField 2 F x)ᵀ) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
    memLp_nativePrincipalTransposeIntegrand _
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F)
  obtain ⟨U,hU⟩ := exists_adjointMass_H3_regularity_lift hcalc hreg
    (fun x => (coefficientMatrixField 2 F x)ᵀ) lam Lam
    (contDiffOn_nativePrincipalTranspose _
      (contDiffOn_coefficientMatrixField_closedBall 2 F)) hUE.transpose
    hcoeff (-beta) hbeta.neg K hK (nativeSupportedNegativeDrift_zeroOutside beta K hz)
    M1 M2 hM2 f u V hV hu
  exact ⟨U,hU⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
