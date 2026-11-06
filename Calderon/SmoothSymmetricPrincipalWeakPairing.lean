import Calderon.ActualMetricWronskianDivergence
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricVolume MetricOperator

theorem integral_smooth_mul_fderiv_eq_neg_fderiv_mul_of_compact
    (f g : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport f ∨ HasCompactSupport g) (v : R3) :
    (∫ x : R3, f x * fderiv ℝ g x v) =
      -(∫ x : R3, fderiv ℝ f x v * g x) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hdg : Continuous (fun x => fderiv ℝ g x v) :=
    ((hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hDerivativeCompact (h : R3 → ℝ) (hh : HasCompactSupport h) :
      HasCompactSupport (fun x => fderiv ℝ h x v) :=
    (hh.fderiv ℝ).comp_left (g := fun D : R3 →L[ℝ] ℝ => D v) rfl
  have hFirst : HasCompactSupport (fun x => fderiv ℝ f x v * g x) := by
    rcases hc with hc | hc
    · exact (hDerivativeCompact f hc).mul_right
    · exact hc.mul_left
  have hSecond : HasCompactSupport (fun x => f x * fderiv ℝ g x v) := by
    rcases hc with hc | hc
    · exact hc.mul_right
    · exact (hDerivativeCompact g hc).mul_left
  have hProduct : HasCompactSupport (fun x => f x*g x) := by
    rcases hc with hc | hc
    · exact hc.mul_right
    · exact hc.mul_left
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hdf.mul hg.continuous).integrable_of_hasCompactSupport hFirst)
    ((hf.continuous.mul hdg).integrable_of_hasCompactSupport hSecond)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hProduct)
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => hg.differentiable (by simp) x)

theorem integrable_smooth_mul_fderiv_of_compact
    (f g : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport f ∨ HasCompactSupport g) (v : R3) :
    Integrable (fun x : R3 => f x * fderiv ℝ g x v) := by
  have hdg : Continuous (fun x => fderiv ℝ g x v) :=
    ((hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hDgCompact (hcg : HasCompactSupport g) : HasCompactSupport (fun x => fderiv ℝ g x v) :=
    (hcg.fderiv ℝ).comp_left (g := fun D : R3 →L[ℝ] ℝ => D v) rfl
  apply (hf.continuous.mul hdg).integrable_of_hasCompactSupport
  rcases hc with hc | hc
  · exact hc.mul_right
  · exact (hDgCompact hc).mul_left

theorem integral_smooth_mul_neg_coordinate_derivative_sum
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (J : Fin 3 → R3 → ℝ)
    (hJ : ∀ i : Fin 3, ContDiff ℝ ∞ (J i))
    (hc : HasCompactSupport f ∨ ∀ i : Fin 3, HasCompactSupport (J i)) :
    (∫ x : R3, f x * (-(∑ i : Fin 3,
      fderiv ℝ (J i) x (MetricVolume.coordinateVector i)))) =
    ∫ x : R3, ∑ i : Fin 3,
      fderiv ℝ f x (MetricVolume.coordinateVector i) * J i x := by
  have hcEach (i : Fin 3) : HasCompactSupport f ∨ HasCompactSupport (J i) :=
    hc.elim Or.inl (fun h => Or.inr (h i))
  have hL (i : Fin 3) : Integrable
      (fun x => f x * fderiv ℝ (J i) x (MetricVolume.coordinateVector i)) :=
    integrable_smooth_mul_fderiv_of_compact f (J i) hf (hJ i) (hcEach i) _
  have hR (i : Fin 3) : Integrable
      (fun x => fderiv ℝ f x (MetricVolume.coordinateVector i) * J i x) := by
    have h := integrable_smooth_mul_fderiv_of_compact (J i) f (hJ i) hf (hcEach i).symm
      (MetricVolume.coordinateVector i)
    exact h.congr (Filter.Eventually.of_forall (fun x => mul_comm _ _))
  calc
    _ = -(∫ x : R3, ∑ i : Fin 3, f x * fderiv ℝ (J i) x (MetricVolume.coordinateVector i)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by simp only [Finset.mul_sum,mul_neg])
    _ = -(∑ i : Fin 3, ∫ x : R3, f x * fderiv ℝ (J i) x (MetricVolume.coordinateVector i)) := by
      rw [integral_finsetSum Finset.univ (fun i _ => hL i)]
    _ = ∑ i : Fin 3, ∫ x : R3, fderiv ℝ f x (MetricVolume.coordinateVector i) * J i x := by
      simp_rw [integral_smooth_mul_fderiv_eq_neg_fderiv_mul_of_compact f (J _) hf (hJ _) (hcEach _) _]
      rw [Finset.sum_neg_distrib,neg_neg]
    _ = _ := (integral_finsetSum Finset.univ (fun i _ => hR i)).symm

theorem integral_smooth_mul_neg_matrixGradient_divergence_symm
    (a : MatrixField) (ha : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun x => a x i j))
    (hSym : ∀ x : R3, ∀ i j : Fin 3, a x i j = a x j i)
    (u φ : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (hφ : ContDiff ℝ ∞ φ)
    (hCompact : HasCompactSupport φ) :
    (∫ x : R3, u x * (-coordinateFluxDivergence
      (fun z => matrixOperatorMap (a z) (gradient φ z)) x)) =
    ∫ x : R3, φ x * (-coordinateFluxDivergence
      (fun z => matrixOperatorMap (a z) (gradient u z)) x) := by
  let D (f : R3 → ℝ) (j : Fin 3) (x : R3) := fderiv ℝ f x (MetricVolume.coordinateVector j)
  let J (f : R3 → ℝ) (i : Fin 3) (x : R3) := ∑ j : Fin 3, a x i j * D f j x
  have hD (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (j : Fin 3) : ContDiff ℝ ∞ (D f j) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hJ (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin 3) : ContDiff ℝ ∞ (J f i) :=
    ContDiff.sum (fun j _ => (ha i j).mul (hD f hf j))
  have hDCompact (j : Fin 3) : HasCompactSupport (D φ j) :=
    (hCompact.fderiv ℝ).comp_left
      (g := fun L : R3 →L[ℝ] ℝ => L (MetricVolume.coordinateVector j)) rfl
  have hJCompact (i : Fin 3) : HasCompactSupport (J φ i) := by
    let F : Fin 3 → R3 → ℝ := fun j x => a x i j * D φ j x
    have hF (j : Fin 3) : HasCompactSupport (F j) := (hDCompact j).mul_left
    have hSum : HasCompactSupport (∑ j : Fin 3, F j) :=
      HasCompactSupport.finset_sum (s := Finset.univ) (f := F) (fun j _ => hF j)
    have hEq : (∑ j : Fin 3, F j) = J φ i := by
      funext x
      exact Finset.sum_apply x Finset.univ F
    exact hEq ▸ hSum
  have hFlux (f : R3 → ℝ) (i : Fin 3) :
      (fun x => matrixOperatorMap (a x) (gradient f x) i) = J f i := by
    funext x
    simp only [matrixOperator_coordinate,gradient_coordinate,J,D]
  have hEnergy (x : R3) : (∑ i : Fin 3, D u i x * J φ i x) =
      ∑ i : Fin 3, D φ i x * J u i x := by
    simp only [J,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hSym x j i]
    ring
  unfold coordinateFluxDivergence
  simp_rw [hFlux]
  have hCoord (i : Fin 3) : NormalCoordinatesFrame.coordinateVector i = MetricVolume.coordinateVector i := by
    ext j
    simp [NormalCoordinatesFrame.coordinateVector,MetricVolume.coordinateVector]
  simp_rw [hCoord]
  rw [integral_smooth_mul_neg_coordinate_derivative_sum u hu (J φ) (hJ φ hφ) (Or.inr hJCompact),
    integral_smooth_mul_neg_coordinate_derivative_sum φ hφ (J u) (hJ u hu) (Or.inl hCompact)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall hEnergy

end OAI.AnisotropicCalderon.ConnectionError
