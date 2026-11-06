import Calderon.NativeSmoothSharpTraceCompletion
import Calderon.NativeSupportedAdjointNonzeroWeakCoherence
import Calderon.NativeCoefficientWeakConormalEndpoint
import Calderon.NativeScalarMassFullGreen
import Calderon.NativeHalfCoefficientConormalTrace
import Calderon.NativeHarmonicHalfCoarseDualPairing

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicH1LiftCompletion
  NativeHalfCoefficientConormalTrace NativeHarmonicHalfCoarseDualPairing
  NativePolynomialBulkMoments NativeSmoothSharpTraceCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Upfront: native-supported-adjoint-conormal-compatibility-author-oct14-v001/EXPANSION-v001.json. -/

lemma nativeNormalizedGreenPairing (sigma e t : ℝ) (hSigma : 0 < sigma)
    (hGreen : e = sigma*t) : sigma⁻¹*e = t := by
  rw [hGreen, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hSigma), one_mul]

def nativeSupportedAdjointWeakConormalEndpoint (a : MatrixField)
    (hp : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (hF : SphereFischerInner) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  nativeWeakConormalEndpoint (fun x => (a x)ᵀ) (-beta)
    (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
    (nativeSupportedAdjointEnergyMemLp a hp C beta hbeta) hF

attribute [local irreducible] nativeWeakHalfLift nativeWeakConormalEndpoint
  nativeSupportedAdjointWeakConormalEndpoint nativeHalfCoefficientConormalTraceL

lemma sphereSobolevDualPairing_nativeSupportedAdjointWeakConormal_of_coherent_H2
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (C : SmoothCoefficientJets 1)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0)
    (hA : (nativeSupportedOriginalZeroEnergyL (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta).IsInvertible)
    (hF : SphereFischerInner)
    (f : SphereSobolev (3/2:ℝ)) (U : BallSobolev 2)
    (hU : TauCeti.Wkp.firstOrder 1 U = nativeWeakHalfLift (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
        (nativeSupportedAdjointEnergyMemLp (coefficientMatrixField 2 F)
          (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta) hF (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)) (z : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) z
      (nativeSupportedAdjointWeakConormalEndpoint (coefficientMatrixField 2 F)
        (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta hF (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)) =
      ⟪ordinaryConormalTraceL hcalc τ0 (fun i j => F j i) U, τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF z)⟫_ℝ := by
  unfold nativeSupportedAdjointWeakConormalEndpoint
  have hi := nativeSupportedAdjointRawZeroEnergy_isInvertible τ0 (coefficientMatrixField 2 F)
    (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta hA
  have hWeak : ∀ v : BallH1Zero,
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
        (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) = 0 := by
    intro v
    exact (congrArg (fun u : BallH1 => TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
      (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
      u (v : BallH1)) hU).trans
      (nativeWeakHalfLift_weak_solution (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
        (nativeSupportedAdjointEnergyMemLp (coefficientMatrixField 2 F)
          (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta) hF hi _ v)
  have hPair := sphereSobolevDualPairing_nativeWeakConormalEndpoint
    (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
    (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
    (nativeSupportedAdjointEnergyMemLp (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta) hF
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) z
  have hCo := congrArg (fun u : BallH1 => sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
    (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
    u (harmonicFirstOrderLiftCompletion hF z)) hU.symm
  exact (hPair.trans hCo).trans
    (nativeNormalizedGreenPairing sphereSurfaceMass _ _ sphereSurfaceMass_pos
      (nativeSupportedAdjoint_homogeneous_full_test_energy hcalc τ0 F C beta hbeta
        K hK hz U hWeak (harmonicFirstOrderLiftCompletion hF z)))

lemma nativeSupportedAdjointWeakConormal_eq_coarse_of_coherent_H2
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (C : SmoothCoefficientJets 1)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0)
    (hA : (nativeSupportedOriginalZeroEnergyL (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta).IsInvertible)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (f : SphereSobolev (3/2:ℝ)) (U : BallSobolev 2)
    (hU : TauCeti.Wkp.firstOrder 1 U = nativeWeakHalfLift (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
        (nativeSupportedAdjointEnergyMemLp (coefficientMatrixField 2 F)
          (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta) hF (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)) :
    nativeSupportedAdjointWeakConormalEndpoint (coefficientMatrixField 2 F)
        (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta hF (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0 (fun i j => F j i) U)) := by
  apply ext_inner_left ℝ
  intro z
  change sphereSobolevDualPairing (1/2:ℝ) z _ = sphereSobolevDualPairing (1/2:ℝ) z _
  rw [sphereSobolevDualPairing_nativeSupportedAdjointWeakConormal_of_coherent_H2
    τ0 hcalc F C beta hbeta K hK hz hA hF f U hU z]
  exact (sphereSobolevDualPairing_coarse_eq_halfLift_trace hF hO hD τ0 z _).symm

lemma nativeSupportedAdjointWeakConormal_eq_sharp_of_coherent_H2
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (C : SmoothCoefficientJets 1)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0)
    (hA : (nativeSupportedOriginalZeroEnergyL (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta).IsInvertible)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (f : SphereSobolev (3/2:ℝ)) (U : BallSobolev 2)
    (hU : TauCeti.Wkp.firstOrder 1 U = nativeWeakHalfLift (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
        (nativeSupportedAdjointEnergyMemLp (coefficientMatrixField 2 F)
          (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta) hF (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)) :
    nativeSupportedAdjointWeakConormalEndpoint (coefficientMatrixField 2 F)
        (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta hF (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0 (fun i j => F j i) U) := by
  have hZero := sphereSobolevInclusionL_nativeHalfCoefficientConormalTraceL
    hF hO hD hcalc τ0 (fun i j => F j i) U
  have hIncl := congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)) hZero
  have hTrans := congrArg (fun L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    L (nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0 (fun i j => F j i) U))
      (sphereSobolevInclusionL_trans (1/2:ℝ) 0 (-(1/2:ℝ)) (by norm_num) (by norm_num))
  exact (nativeSupportedAdjointWeakConormal_eq_coarse_of_coherent_H2
    τ0 hcalc F C beta hbeta K hK hz hA hF hO hD f U hU).trans (hIncl.symm.trans hTrans)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeNormalizedGreenPairing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointWeakConormalEndpoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_nativeSupportedAdjointWeakConormal_of_coherent_H2
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointWeakConormal_eq_coarse_of_coherent_H2
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointWeakConormal_eq_sharp_of_coherent_H2
