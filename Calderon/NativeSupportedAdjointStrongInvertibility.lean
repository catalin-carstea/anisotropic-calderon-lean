import Calderon.NativeSupportedAdjointStrongForcing
import Calderon.NativeSupportedAdjointH2Inverse
import Calderon.DirichletForcingInjectivity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Upfront: native-supported-adjoint-strong-invertibility-author-oct14-v001/EXPANSION-v001.json. -/

def nativeSupportedAdjointStrongDirichletL (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (C : SmoothCoefficientJets 1)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0) : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 :=
  (nativeSupportedAdjointStrongL hcalc F C beta hbeta K hK hz).comp nativeStrongH2InclusionL

attribute [local irreducible] nativeSupportedAdjointStrongDirichletL nativeSupportedAdjointStrongL
  nativeStrongH2InclusionL nativeZeroCoefficientEnergyL

lemma nativeSupportedAdjointStrongDirichletL_energy (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (C : SmoothCoefficientJets 1)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0) (U : StrongDirichletSpace 0) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (nativeSupportedAdjointStrongDirichletL hcalc F C beta hbeta K hK hz U) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
        (strongDirichletProjectionL 0 U : BallH1) (v : BallH1) := by
  unfold nativeSupportedAdjointStrongDirichletL
  have hJ : TauCeti.Wkp.firstOrder 1 (nativeStrongH2InclusionL U) =
      (strongDirichletProjectionL 0 U : BallH1) :=
    (congrArg (fun W : BallSobolev 2 => TauCeti.Wkp.firstOrder 1 W)
      (nativeStrongH2InclusionL_apply U)).trans (strongDirichletProjectionL_apply 0 U).symm
  exact (nativeSupportedAdjointStrongL_energy hcalc F C beta hbeta K hK hz
    (nativeStrongH2InclusionL U) v).trans
    (congrArg (fun u : BallH1 => TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
      (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x) u (v : BallH1)) hJ)

lemma nativeSupportedAdjointStrongDirichletL_zeroEnergy (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (C : SmoothCoefficientJets 1)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0) (U : StrongDirichletSpace 0) (v : BallH1Zero) :
    nativeSupportedAdjointZeroEnergyL (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta
      (strongDirichletProjectionL 0 U) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (nativeSupportedAdjointStrongDirichletL hcalc F C beta hbeta K hK hz U) v := by
  unfold nativeSupportedAdjointZeroEnergyL
  exact (nativeZeroCoefficientEnergyL_eval_to_H1 (fun x => (coefficientMatrixField 2 F x)ᵀ)
    (-beta) (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
    (nativeSupportedAdjointEnergyMemLp (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta)
    (strongDirichletProjectionL 0 U) v).trans
    (nativeSupportedAdjointStrongDirichletL_energy hcalc F C beta hbeta K hK hz U v).symm

attribute [local irreducible] nativeSupportedAdjointZeroEnergyL

lemma nativeSupportedAdjointStrongDirichletL_injective (τ0 : UnitBallValueTrace)
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2) (C : SmoothCoefficientJets 1)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0)
    (hA : (nativeSupportedOriginalZeroEnergyL (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta).IsInvertible) :
    Function.Injective (nativeSupportedAdjointStrongDirichletL hcalc F C beta hbeta K hK hz) := by
  have hAdj := nativeSupportedAdjointZeroEnergyL_isInvertible τ0 (coefficientMatrixField 2 F)
    (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta hA
  intro U V h
  apply strongDirichletProjectionL_injective 0
  apply hAdj.injective
  apply ContinuousLinearMap.ext
  intro v
  exact (nativeSupportedAdjointStrongDirichletL_zeroEnergy hcalc F C beta hbeta K hK hz U v).trans
    ((congrArg (fun f : BallSobolev 0 => TauCeti.PDE.dirichletForcing
      (mu := (volume : Measure R3)) (Omega := ballOpens) f v) h).trans
      (nativeSupportedAdjointStrongDirichletL_zeroEnergy hcalc F C beta hbeta K hK hz V v).symm)

lemma nativeSupportedAdjointStrongDirichletL_isInvertible (τ0 : UnitBallValueTrace)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (F : SmoothCoefficientMatrix 2) (lam Lam : ℝ)
    (hell : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam)
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0)
    (hA : (nativeSupportedOriginalZeroEnergyL (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta).IsInvertible) :
    (nativeSupportedAdjointStrongDirichletL hcalc F C beta hbeta K hK hz).IsInvertible := by
  obtain ⟨R,hR⟩ := exists_nativeSupportedAdjoint_H2_inverse τ0 hcalc hreg (coefficientMatrixField 2 F)
    lam Lam (contDiffOn_coefficientMatrixField_closedBall 2 F) hell
    (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta K hK hz hA
  let S := nativeSupportedAdjointStrongDirichletL hcalc F C beta hbeta K hK hz
  have hSR : ∀ f : BallSobolev 0, S (R f) = f := by
    intro f
    apply unitBallDirichletForcing_eq_of_forall
    intro v
    exact (nativeSupportedAdjointStrongDirichletL_energy hcalc F C beta hbeta K hK hz (R f) v).trans
      (hR f v)
  have hf : S.comp R = ContinuousLinearMap.id ℝ (BallSobolev 0) := by
    apply ContinuousLinearMap.ext
    exact hSR
  have hInj : Function.Injective S := nativeSupportedAdjointStrongDirichletL_injective
    τ0 hcalc F C beta hbeta K hK hz hA
  have hg : R.comp S = ContinuousLinearMap.id ℝ (StrongDirichletSpace 0) := by
    apply ContinuousLinearMap.ext
    intro U
    exact hInj (hSR (S U))
  exact ContinuousLinearMap.IsInvertible.of_inverse hf hg

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointStrongDirichletL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointStrongDirichletL_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointStrongDirichletL_zeroEnergy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointStrongDirichletL_injective
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointStrongDirichletL_isInvertible
