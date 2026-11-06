import Calderon.NativeScalarMassPrincipalRegularity
import TauCeti.Analysis.PDE.SymmetricEnergy
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Gradient Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Fully expanded before source in
work/day-oct13/native-supported-adjoint-H2-author-oct14-v001/EXPANSION-v001.json.
The formal adjoint uses the literal aᵀ, negative original supported drift and
actual c-div beta mass. The existing principal hreg is the only regularity interface. -/

lemma contDiffOn_nativePrincipalTranspose (a : MatrixField)
    (ha : ContDiffOn ℝ ∞ a (Metric.closedBall 0 2)) :
    ContDiffOn ℝ ∞ (fun x => (a x)ᵀ) (Metric.closedBall 0 2) := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact contDiffOn_pi.mp (contDiffOn_pi.mp ha j) i

lemma nativePrincipalIntegrand_transpose_eq_flip (A : Matrix (Fin 3) (Fin 3) ℝ) :
    TauCeti.PDE.energyIntegrand Aᵀ 0 0 = (TauCeti.PDE.energyIntegrand A 0 0).flip := by
  apply ContinuousLinearMap.ext
  intro U
  apply ContinuousLinearMap.ext
  intro V
  exact TauCeti.PDE.energyIntegrand_zero_drift_transpose_apply A 0 U V

lemma memLp_nativePrincipalTransposeIntegrand (a : MatrixField)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)ᵀ 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  let F : ((ℝ × R3) →L[ℝ] (ℝ × R3) →L[ℝ] ℝ) →L[ℝ]
      ((ℝ × R3) →L[ℝ] (ℝ × R3) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (ℝ × R3) (ℝ × R3) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hf := hcoeff.continuousLinearMap_comp F
  change MemLp (fun x => (TauCeti.PDE.energyIntegrand (a x) 0 0).flip) ⊤
    ((volume : Measure R3).restrict ballOpens) at hf
  simpa only [← nativePrincipalIntegrand_transpose_eq_flip] using hf

def nativeSupportedDriftDivergence (beta : R3 → R3) : R3 → ℝ :=
  fun x => ∑ i : Fin 3, fderiv ℝ (fun y => beta y i) x (coordinateVector i)

lemma nativeSupportedDriftDivergence_eq_sum_gradient (beta : R3 → R3) (x : R3) :
    nativeSupportedDriftDivergence beta x =
      ∑ i : Fin 3, (gradient (fun y => beta y i) x) i := by
  simp only [nativeSupportedDriftDivergence,gradient_coordinate]

lemma nativeSupportedNegativeDrift_zeroOutside
    (beta : R3 → R3) (K : Set R3) (hz : ∀ x, x ∉ K → beta x = 0) :
    ∀ x, x ∉ K → (-beta) x = 0 := by
  intro x hx
  simp only [Pi.neg_apply,hz x hx,neg_zero]

def nativeSupportedAdjointMassCoefficient (C : SmoothCoefficientJets 1)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0) : SmoothCoefficientJets 1 :=
  nativeAdjointMassCoefficient C (fun i => supportedDriftCoefficient 1 beta hbeta K hK hz i)

lemma coefficientValue_nativeSupportedAdjointMassCoefficient (C : SmoothCoefficientJets 1)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0) :
    coefficientValue 1 (nativeSupportedAdjointMassCoefficient C beta hbeta K hK hz) =
      (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x) := by
  unfold nativeSupportedAdjointMassCoefficient
  rw [coefficientValue_nativeAdjointMassCoefficient]
  funext x
  unfold nativeAdjointMassValue nativeSupportedDriftDivergence
  apply congrArg (fun t : ℝ => coefficientValue 1 C x-t)
  apply Finset.sum_congr rfl
  intro i hi
  have he : coefficientValue 2 (supportedDriftCoefficient 1 beta hbeta K hK hz i) =
      (fun y => beta y i) :=
    funext (fun y => supportedDriftCoefficient_value 1 beta hbeta K hK hz i y)
  exact congrArg (fun f : R3 → ℝ => fderiv ℝ f x (coordinateVector i)) he

lemma coefficientValue_nativeSupportedAdjointMassCoefficient_zero
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0) :
    coefficientValue 1 (nativeSupportedAdjointMassCoefficient 0 beta hbeta K hK hz) =
      (fun x => -nativeSupportedDriftDivergence beta x) := by
  have he := coefficientValue_nativeSupportedAdjointMassCoefficient 0 beta hbeta K hK hz
  have hzero : coefficientValue 1 (0 : SmoothCoefficientJets 1) = (0 : R3 → ℝ) := rfl
  simpa only [hzero,Pi.zero_apply,zero_sub] using he

lemma exists_nativeSupportedAdjoint_H2_regularity_lift
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (a : MatrixField) (lam Lam : ℝ)
    (hsmooth : ContDiffOn ℝ ∞ a (Metric.closedBall 0 2))
    (hell : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : BallSobolev 0) (u : BallH1Zero),
      TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (a x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x) f u →
      ∃ U : BallSobolev 2,
        TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) 1 U = (u : BallH1) ∧
        ‖U‖ ≤ D * (‖u‖ + ‖f-
          nativeCoefficientMassL hcalc (nativeSupportedAdjointMassCoefficient C beta hbeta K hK hz)
            (u : BallH1)-
          supportedDriftL hcalc 0 (-beta) hbeta.neg K hK
            (nativeSupportedNegativeDrift_zeroOutside beta K hz) (u : BallH1)‖) := by
  let M : SmoothCoefficientJets 1 := nativeSupportedAdjointMassCoefficient C beta hbeta K hK hz
  have hmass : coefficientValue 1 M =
      (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x) :=
    coefficientValue_nativeSupportedAdjointMassCoefficient C beta hbeta K hK hz
  obtain ⟨D,hD,hLift⟩ := exists_supportedDriftMass_H2_regularity_lift hcalc hreg
    (fun x => (a x)ᵀ) lam Lam (contDiffOn_nativePrincipalTranspose a hsmooth) hell.transpose
    (memLp_nativePrincipalTransposeIntegrand a hcoeff) (-beta) hbeta.neg K hK
    (nativeSupportedNegativeDrift_zeroOutside beta K hz) M
  refine ⟨D,hD,?_⟩
  intro f u hu
  have huM : TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (a x)ᵀ) (-beta) (coefficientValue 1 M) f u := hmass.symm ▸ hu
  exact hLift f u huM

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_nativePrincipalTranspose
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativePrincipalIntegrand_transpose_eq_flip
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.memLp_nativePrincipalTransposeIntegrand
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedDriftDivergence
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedDriftDivergence_eq_sum_gradient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedNegativeDrift_zeroOutside
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjointMassCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_nativeSupportedAdjointMassCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_nativeSupportedAdjointMassCoefficient_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeSupportedAdjoint_H2_regularity_lift
