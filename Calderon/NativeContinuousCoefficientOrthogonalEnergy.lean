import Calderon.NativeH1OrthogonalEnergyCovariance
import Calderon.NativeWeightedDriftFluxGreen

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Gradient Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricOperator

lemma continuous_orthogonalPrincipalCoefficient (e : R3 ≃ₗᵢ[ℝ] R3)
    (a : MatrixField) (ha : Continuous a) : Continuous (orthogonalPrincipalCoefficient e a) := by
  have he : orthogonalPrincipalCoefficient e a = fun x =>
      (operatorMatrixMap e.toContinuousLinearEquiv.toContinuousLinearMap)ᵀ * a (e x) *
        operatorMatrixMap e.toContinuousLinearEquiv.toContinuousLinearMap :=
    funext (orthogonalPrincipalCoefficient_eq_matrix_conjugation e a)
  rw [he]
  exact (continuous_const.mul (ha.comp e.continuous)).mul continuous_const

lemma memLp_nativeEnergyIntegrand_of_continuous
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    MemLp (fun x : R3 => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  have ht := memLp_unitBall_of_continuous_normed
    (fun x : R3 => TauCeti.PDE.energyIntegrand (a x) (b x) (c x))
  have hbridge : Continuous (fun x : R3 => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) →
      MemLp (fun x : R3 => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
        ((volume : Measure R3).restrict ballOpens) := by
    simpa only [real_nontriviallyNormedField_normedField_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] using ht
  exact hbridge (TauCeti.PDE.Continuous.energyIntegrand ha hb hc)

lemma energyFormH1_orthogonal_covariance
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e)
      (nativeH1OrthogonalPullback e u) (nativeH1OrthogonalPullback e v) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b c u v := by
  apply energyFormH1_orthogonal_covariance_of_memLp e a b c
    (memLp_nativeEnergyIntegrand_of_continuous a b c ha hb hc)
  exact memLp_nativeEnergyIntegrand_of_continuous
    (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e)
    (continuous_orthogonalPrincipalCoefficient e a ha)
    (e.symm.continuous.comp (hb.comp e.continuous)) (hc.comp e.continuous)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_orthogonalPrincipalCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.memLp_nativeEnergyIntegrand_of_continuous
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1_orthogonal_covariance
