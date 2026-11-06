import Calderon.NativeOrthogonalSmoothPullback

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Gradient InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator

/-! This is the full bilinear energy, including the actual nonsymmetric drift. -/

def orthogonalPrincipalCoefficient (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) : MatrixField :=
  fun x => operatorMatrixMap (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((matrixOperatorMap (a (e x))).comp e.toContinuousLinearEquiv.toContinuousLinearMap))

def orthogonalDriftCoefficient (e : R3 ≃ₗᵢ[ℝ] R3) (b : R3 → R3) : R3 → R3 :=
  fun x => e.symm (b (e x))

lemma operatorMatrixMap_matrixOperatorMap (A : Matrix (Fin 3) (Fin 3) ℝ) :
    operatorMatrixMap (matrixOperatorMap A) = A :=
  matrixOperatorAlgEquiv.symm_apply_apply A

lemma orthogonalPrincipalCoefficient_eq_matrix_conjugation
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (x : R3) :
    orthogonalPrincipalCoefficient e a x =
      (operatorMatrixMap e.toContinuousLinearEquiv.toContinuousLinearMap)ᵀ * a (e x) *
        operatorMatrixMap e.toContinuousLinearEquiv.toContinuousLinearMap := by
  unfold orthogonalPrincipalCoefficient
  rw [operatorMatrixMap_comp,operatorMatrixMap_comp,operatorMatrixMap_matrixOperatorMap]
  have hTranspose : operatorMatrixMap e.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      (operatorMatrixMap e.toContinuousLinearEquiv.toContinuousLinearMap)ᵀ := by
    rw [← e.adjoint_eq_symm]
    exact operatorMatrixMap_adjoint _
  rw [hTranspose,Matrix.mul_assoc]

lemma matrixBilinearForm_eq_matrixOperator_inner
    (A : Matrix (Fin 3) (Fin 3) ℝ) (ξ η : R3) :
    TauCeti.PDE.matrixBilinearForm A η ξ = ⟪matrixOperatorMap A ξ,η⟫_ℝ := by
  rw [TauCeti.PDE.matrixBilinearForm_apply]
  rfl

lemma energyIntegrand_orthogonal_covariance
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (x : R3) (U V : ℝ × R3) :
    TauCeti.PDE.energyIntegrand (orthogonalPrincipalCoefficient e a x)
      (orthogonalDriftCoefficient e b x) (c (e x)) (U.1,e.symm U.2) (V.1,e.symm V.2) =
    TauCeti.PDE.energyIntegrand (a (e x)) (b (e x)) (c (e x)) U V := by
  have hMap : matrixOperatorMap (orthogonalPrincipalCoefficient e a x) (e.symm U.2) =
      e.symm (matrixOperatorMap (a (e x)) U.2) := by
    change (operatorMatrixMap _).toEuclideanLin (e.symm U.2) = _
    rw [operatorMatrixMap_apply]
    change e.symm (matrixOperatorMap (a (e x)) (e (e.symm U.2))) =
      e.symm (matrixOperatorMap (a (e x)) U.2)
    rw [e.apply_symm_apply]
  simp only [TauCeti.PDE.energyIntegrand_apply,matrixBilinearForm_eq_matrixOperator_inner,
    TauCeti.PDE.driftForm_apply,TauCeti.PDE.massForm_apply,orthogonalDriftCoefficient,hMap,
    e.symm.inner_map_map]

lemma energyJet_orthogonalSmoothPullback
    (e : R3 ≃ₗᵢ[ℝ] R3) (f : SmoothData) (x : R3) :
    energyJet (orthogonalSmoothPullback e f).1 x =
      ((energyJet f.1 (e x)).1,e.symm (energyJet f.1 (e x)).2) := by
  apply Prod.ext
  · rfl
  · change energyGradient (f.1 ∘ e) x = e.symm (energyGradient f.1 (e x))
    rw [energyGradient_eq_gradient,energyGradient_eq_gradient]
    exact gradient_comp_orthogonal e f.1 f.2 x

lemma energyIntegrand_smooth_orthogonal_covariance
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (u v : SmoothData) (x : R3) :
    TauCeti.PDE.energyIntegrand (orthogonalPrincipalCoefficient e a x)
      (orthogonalDriftCoefficient e b x) (c (e x))
      (energyJet (orthogonalSmoothPullback e u).1 x) (energyJet (orthogonalSmoothPullback e v).1 x) =
    TauCeti.PDE.energyIntegrand (a (e x)) (b (e x)) (c (e x)) (energyJet u.1 (e x)) (energyJet v.1 (e x)) := by
  have hu := energyJet_orthogonalSmoothPullback e u x
  have hv := energyJet_orthogonalSmoothPullback e v x
  have hpair := congrArg₂ (fun X Y : ℝ × R3 =>
    TauCeti.PDE.energyIntegrand (orthogonalPrincipalCoefficient e a x)
      (orthogonalDriftCoefficient e b x) (c (e x)) X Y) hu hv
  exact hpair.trans (energyIntegrand_orthogonal_covariance e a b c x
    (energyJet u.1 (e x)) (energyJet v.1 (e x)))

lemma energyFormH1_smooth_eq_integral_jets
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ) (u v : SmoothData) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a b c (smoothSobolev u) (smoothSobolev v) =
      ∫ x in (ballOpens : Set R3), TauCeti.PDE.energyIntegrand (a x) (b x) (c x)
        (energyJet u.1 x) (energyJet v.1 x) := by
  rw [TauCeti.PDE.energyFormH1_def]
  apply integral_congr_ae
  filter_upwards [jetField_smoothSobolev_ae u,jetField_smoothSobolev_ae v] with x hu hv
  rw [hu,hv]

lemma energyFormH1_smooth_orthogonal_covariance
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (u v : SmoothData) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (orthogonalPrincipalCoefficient e a) (orthogonalDriftCoefficient e b) (c ∘ e)
      (smoothSobolev (orthogonalSmoothPullback e u)) (smoothSobolev (orthogonalSmoothPullback e v)) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a b c (smoothSobolev u) (smoothSobolev v) := by
  rw [energyFormH1_smooth_eq_integral_jets,energyFormH1_smooth_eq_integral_jets]
  calc
    _ = ∫ x in (ballOpens : Set R3), TauCeti.PDE.energyIntegrand (a (e x)) (b (e x)) (c (e x))
        (energyJet u.1 (e x)) (energyJet v.1 (e x)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (energyIntegrand_smooth_orthogonal_covariance e a b c u v)
    _ = _ := integral_comp_orthogonal_unitBall e (fun z : R3 =>
      TauCeti.PDE.energyIntegrand (a z) (b z) (c z) (energyJet u.1 z) (energyJet v.1 z))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.orthogonalPrincipalCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.orthogonalDriftCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.operatorMatrixMap_matrixOperatorMap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.orthogonalPrincipalCoefficient_eq_matrix_conjugation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.matrixBilinearForm_eq_matrixOperator_inner
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyIntegrand_orthogonal_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyIntegrand_smooth_orthogonal_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1_smooth_eq_integral_jets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1_smooth_orthogonal_covariance

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyJet_orthogonalSmoothPullback
