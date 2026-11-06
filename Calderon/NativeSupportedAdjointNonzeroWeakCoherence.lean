import Calderon.NativeSupportedAdjointNonzeroH2Lift
import Calderon.NativeCoefficientWeakHalfLiftUniqueness

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Fully expanded before source in native-supported-adjoint-weak-coherence-author-oct14-v001/EXPANSION-v001.json.
Actual high/half coherence is derived from genuine energy uniqueness. -/

attribute [local irreducible] nativeZeroCoefficientEnergyL nativeWeakHalfLift
  harmonicFirstOrderLiftCompletion

lemma nativeSupportedAdjointRawZeroEnergy_isInvertible
    (τ0 : UnitBallValueTrace) (a : MatrixField)
    (hp : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (hA : (nativeSupportedOriginalZeroEnergyL a hp C beta hbeta).IsInvertible) :
    (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := fun x => (a x)ᵀ) (b := -beta)
      (c := fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
      (nativeSupportedAdjointEnergyMemLp a hp C beta hbeta)).IsInvertible := by
  have hAdj := nativeSupportedAdjointZeroEnergyL_isInvertible τ0 a hp C beta hbeta hA
  exact (nativeZeroCoefficientEnergyL_isInvertible_iff (fun x => (a x)ᵀ) (-beta)
    (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
    (nativeSupportedAdjointEnergyMemLp a hp C beta hbeta)).mp hAdj

lemma nativeSupportedAdjoint_highWeakCoherence
    (τ0 : UnitBallValueTrace) (a : MatrixField)
    (hp : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (hA : (nativeSupportedOriginalZeroEnergyL a hp C beta hbeta).IsInvertible)
    (hF : SphereFischerInner) (f : SphereSobolev (3/2:ℝ)) (U : BallH1)
    (hZero : harmonicFirstOrderLiftCompletion hF
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)-U ∈
        TauCeti.w1p0Submodule volume ballOpens 2)
    (hWeak : ∀ v : BallH1Zero,
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (a x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x) U (v : BallH1) = 0) :
    nativeWeakHalfLift (fun x => (a x)ᵀ) (-beta)
      (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
      (nativeSupportedAdjointEnergyMemLp a hp C beta hbeta) hF
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) = U := by
  exact nativeWeakHalfLift_unique (fun x => (a x)ᵀ) (-beta)
    (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
    (nativeSupportedAdjointEnergyMemLp a hp C beta hbeta) hF
    (nativeSupportedAdjointRawZeroEnergy_isInvertible τ0 a hp C beta hbeta hA)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) U hZero hWeak

lemma exists_nativeSupportedAdjoint_coherent_nonzero_H2_lift
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (F : SmoothCoefficientMatrix 2) (lam Lam : ℝ)
    (hell : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam)
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0)
    (hA : (nativeSupportedOriginalZeroEnergyL (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta).IsInvertible)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) :
    ∃ W : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2, ∀ f : SphereSobolev (3/2:ℝ),
      TauCeti.Wkp.firstOrder 1 (W f) = nativeWeakHalfLift
        (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
        (nativeSupportedAdjointEnergyMemLp (coefficientMatrixField 2 F)
          (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta) hF
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) := by
  obtain ⟨W,hW⟩ := exists_nativeSupportedAdjoint_nonzero_H2_lift τ0 hcalc hreg
    F lam Lam hell C beta hbeta K hK hz hA hF hO
  refine ⟨W,?_⟩
  intro f
  exact (nativeSupportedAdjoint_highWeakCoherence τ0 (coefficientMatrixField 2 F)
    (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta hA hF f
    (TauCeti.Wkp.firstOrder 1 (W f)) (hW f).1 (hW f).2).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointRawZeroEnergy_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjoint_highWeakCoherence
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeSupportedAdjoint_coherent_nonzero_H2_lift
