import TaskInterface
import Calderon.ActualMixedKernelMovingFixedFlux
import Calderon.ActualMixedKernelGlobalSurfaceExtension
import Calderon.FixedSurfaceFluxIntegration
import Calderon.FixedSurfaceTransferIntegration
import Calderon.ActualNormalizedSecondMetricDrift

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint
  MetricOperator MetricVolume ReferenceDensityBounds ActualNormalizedSecondMetricDrift

/-! Ordinary helpers. Nothing here is a premise of the target theorem. -/

/-- Principal coefficients `a_ij = s * (g2_lam)^(-1)_ij` of the normalized second operator. -/
def fixedFluxSecondA (S : KnownSideSourceData) (L lam : ℝ) : FixedSurfaceFlux.Coefficients :=
  fun x i j => normalizedSecondLaplacianScalarJoint S.g1 S.g2 L (lam,x) *
    (dilatedMetric S.g2 lam x)⁻¹ i j

/-- Drift coefficients `b_k = - Σ_ij a_ij Γ2(i,j,k)` of the normalized second operator. -/
def fixedFluxSecondB (S : KnownSideSourceData) (L lam : ℝ) : R3 → Fin 3 → ℝ :=
  fun x k => -∑ i : Fin 3, ∑ j : Fin 3, fixedFluxSecondA S L lam x i j *
    referenceConnectionFamily S.g2 0 (lam,x) (coordinateDirection i) (coordinateDirection j) k

/-- For a globally smooth function the literal normalized second operator is the
generic parameter second-order operator with the coefficients above and `c = 0`. -/
theorem fixedFlux_normalized_eq_secondOrder (S : KnownSideSourceData) (L lam : ℝ)
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (x : R3) :
    normalizedSecondLaplacian S.g1 S.g2 L lam f x =
      FixedSurfaceFlux.secondOrderOperator (fixedFluxSecondA S L lam)
        (fixedFluxSecondB S L lam) (fun _ => 0) f x := by
  classical
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have hH (i j : Fin 3) :
      RadiusProfile.coordinateHessian f
        (fun X Y => referenceConnectionFamily S.g2 0 (lam,x) X Y)
        x (coordinateDirection i) (coordinateDirection j) =
      fderiv ℝ (fun z => fderiv ℝ f z (FixedSurfaceFlux.coordinateVector j)) x
          (FixedSurfaceFlux.coordinateVector i) -
        ∑ k : Fin 3, referenceConnectionFamily S.g2 0 (lam,x)
            (coordinateDirection i) (coordinateDirection j) k *
          fderiv ℝ f x (FixedSurfaceFlux.coordinateVector k) := by
    unfold RadiusProfile.coordinateHessian
    rw [covector_coordinate_sum (fderiv ℝ f x)]
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp [coordinateDirection, coordinateVector, FixedSurfaceFlux.coordinateVector]
  rw [normalizedSecondLaplacian_eq_hessian_trace S.g1 S.g2 S.g2_admissible L lam f hf x]
  simp_rw [hH]
  unfold FixedSurfaceFlux.secondOrderOperator
  simp only [fixedFluxSecondA, fixedFluxSecondB, Fin.sum_univ_three]
  ring

/-- Germ congruence of the literal normalized second operator. -/
theorem fixedFlux_normalized_congr (S : KnownSideSourceData) (L lam : ℝ)
    (f g : R3 → ℝ) (x : R3) (h : f =ᶠ[𝓝 x] g) :
    normalizedSecondLaplacian S.g1 S.g2 L lam f x =
      normalizedSecondLaplacian S.g1 S.g2 L lam g x := by
  have hgrad : (fun y => gradient f y) =ᶠ[𝓝 x] (fun y => gradient g y) := by
    filter_upwards [h.eventuallyEq_nhds] with z hz
    unfold gradient
    rw [hz.fderiv_eq]
  have hF : (fun y => MetricOperator.matrixOperatorMap ((dilatedMetric S.g2 lam y)⁻¹)
        (gradient f y)) =ᶠ[𝓝 x]
      (fun y => MetricOperator.matrixOperatorMap ((dilatedMetric S.g2 lam y)⁻¹)
        (gradient g y)) := by
    filter_upwards [hgrad] with z hz
    rw [hz]
  have hx : (fun y => MetricOperator.matrixOperatorMap ((dilatedMetric S.g2 lam y)⁻¹)
        (gradient f y)) x =
      (fun y => MetricOperator.matrixOperatorMap ((dilatedMetric S.g2 lam y)⁻¹)
        (gradient g y)) x := hF.eq_of_nhds
  unfold normalizedSecondLaplacian AngularPolynomial.densityWeightedDivergence
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hF] with z hz
  simp only [hz]

/-- Coordinate expansion of the gradient. -/
theorem fixedFlux_gradient_eq_sum (v : R3 → ℝ) (x : R3) :
    gradient v x = ∑ j : Fin 3, fderiv ℝ v x (FixedSurfaceFlux.coordinateVector j) •
      FixedSurfaceFlux.coordinateVector j := by
  have hm : ∀ m : Fin 3, gradient v x m = fderiv ℝ v x (EuclideanSpace.single m 1) := by
    intro m
    rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
    simp
  ext m
  rw [hm m]
  simp [FixedSurfaceFlux.coordinateVector, Pi.single_apply, eq_comm]

/-- Physical metric flux of a slice: fixed physical columns times physical partials. -/
theorem fixedFlux_metricDivergenceFlux_eq_sum (g : MatrixField) (v : R3 → ℝ) (x : R3) :
    metricDivergenceFlux g v x = ∑ j : Fin 3,
      fderiv ℝ v x (FixedSurfaceFlux.coordinateVector j) •
        matrixOperatorMap (principalCoefficient g x) (FixedSurfaceFlux.coordinateVector j) := by
  unfold metricDivergenceFlux
  rw [fixedFlux_gradient_eq_sum v x, map_sum]
  simp only [map_smul]

theorem fixedFlux_wronskian_germ
    (g : MatrixField) (u v w : R3 → ℝ) (x : R3) (h : v =ᶠ[𝓝 x] w) :
    metricWronskianFlux g u v x = metricWronskianFlux g u w x := by
  have hGrad : gradient v x = gradient w x := by
    apply ext_inner_right ℝ
    intro W
    rw [inner_gradient_left,inner_gradient_left,h.fderiv_eq]
  unfold metricWronskianFlux metricDivergenceFlux
  rw [h.eq_of_nhds,hGrad]

/-- Fixed adjugate contraction in coordinates. -/
theorem fixedFlux_inner_signedPiola_eq (X W : R3 → R3) (z : R3) :
    ⟪z, signedPiolaFlux X W z⟫_ℝ = ∑ k : Fin 3, z k * ∑ m : Fin 3,
      (coordinateJacobianMatrix X z).adjugate k m * W (X z) m := by
  unfold signedPiolaFlux
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, matrixOperator_coordinate]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem fixedFlux_contDiff_inner_signedPiola (X W : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (fun z => ⟪z, signedPiolaFlux X W z⟫_ℝ) := by
  have h : (fun z => ⟪z, signedPiolaFlux X W z⟫_ℝ) = fun z => ∑ k : Fin 3, z k *
      ∑ m : Fin 3, (coordinateJacobianMatrix X z).adjugate k m * W (X z) m :=
    funext fun z => fixedFlux_inner_signedPiola_eq X W z
  rw [h]
  refine ContDiff.sum fun k _ => ?_
  refine ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp contDiff_id).mul ?_
  refine ContDiff.sum fun m _ => ?_
  exact (contDiff_matrix_adjugate_entry (coordinateJacobianMatrix X)
      (fun a b => contDiff_coordinateJacobianMatrix_entry X hX a b) k m).mul
    ((EuclideanSpace.proj (𝕜 := ℝ) m).contDiff.comp (hW.comp hX))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
