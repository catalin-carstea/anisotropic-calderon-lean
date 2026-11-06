import Calderon.NativeStrongH2SolutionConstruction
import Calderon.NativeSupportedAdjointWeakSolution
import Calderon.StrongDirichletDomain
import Calderon.ParametricWeightedForcing

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! The strong space is the existing actual H2 domain with precisely first-order zero boundary. -/

attribute [local irreducible] nativeZeroCoefficientEnergyL nativeDirichletForcingL nativeStrongH2Representative

lemma exists_nativeSupportedAdjoint_H2_inverse
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (a : MatrixField) (lam Lam : ℝ)
    (hsmooth : ContDiffOn ℝ ∞ a (Metric.closedBall 0 2))
    (hell : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hprincipal : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0)
    (hA : (nativeSupportedOriginalZeroEnergyL a hprincipal C beta hbeta).IsInvertible) :
    ∃ R : BallSobolev 0 →L[ℝ] StrongDirichletSpace 0, ∀ f : BallSobolev 0,
      TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (a x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x) f
        (strongDirichletProjectionL 0 (R f)) := by
  let A := nativeSupportedAdjointZeroEnergyL a hprincipal C beta hbeta
  have hAdj : A.IsInvertible := nativeSupportedAdjointZeroEnergyL_isInvertible
    τ0 a hprincipal C beta hbeta hA
  have hSolve := exists_nativeSupportedAdjoint_H2_solution τ0 hcalc hreg
    a lam Lam hsmooth hell hprincipal C beta hbeta K hK hz hA
  exact exists_nativeStrong_solutionCLM_of_bounded_solve A hAdj
    (TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (a x)ᵀ) (-beta)
      (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x))
    (fun f u => nativeZeroCoefficientEnergyL_isWeakSolution_iff (fun x => (a x)ᵀ) (-beta)
      (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
      (nativeSupportedAdjointEnergyMemLp a hprincipal C beta hbeta) f u) hSolve

def nativeStrongH2InclusionL : StrongDirichletSpace 0 →L[ℝ] BallSobolev 2 :=
  (strongDirichletSubmodule 0).toSubmodule.subtypeL

lemma nativeStrongH2InclusionL_apply (U : StrongDirichletSpace 0) :
    nativeStrongH2InclusionL U = (U : BallSobolev 2) := rfl

lemma exists_nativeSupportedAdjoint_L2_to_H2
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (a : MatrixField) (lam Lam : ℝ)
    (hsmooth : ContDiffOn ℝ ∞ a (Metric.closedBall 0 2))
    (hell : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hprincipal : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0)
    (hA : (nativeSupportedOriginalZeroEnergyL a hprincipal C beta hbeta).IsInvertible) :
    ∃ R : BallSobolev 0 →L[ℝ] BallSobolev 2, ∀ f : BallSobolev 0, ∃ u : BallH1Zero,
      TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) 1 (R f) = (u : BallH1) ∧
      TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (a x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x) f u := by
  obtain ⟨R,hR⟩ := exists_nativeSupportedAdjoint_H2_inverse τ0 hcalc hreg
    a lam Lam hsmooth hell hprincipal C beta hbeta K hK hz hA
  refine ⟨nativeStrongH2InclusionL.comp R,?_⟩
  intro f
  refine ⟨strongDirichletProjectionL 0 (R f),?_,hR f⟩
  exact (strongDirichletProjectionL_apply 0 (R f)).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeSupportedAdjoint_H2_inverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeStrongH2InclusionL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeStrongH2InclusionL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeSupportedAdjoint_L2_to_H2
