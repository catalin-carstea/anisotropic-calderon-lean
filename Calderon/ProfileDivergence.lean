import Calderon.MetricHessianQuadratic
import Calderon.DilatedProfileUniform

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ContDiff InnerProductSpace Gradient Topology Matrix.Norms.Operator
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile MetricVolume

lemma contDiff_softplus_comp (δ : ℝ) (t : R3 → ℝ) (ht : ContDiff ℝ ∞ t) :
    ContDiff ℝ ∞ (fun x => softplus δ (t x)) := by
  have he : ContDiff ℝ ∞ (fun x => 1 + Real.exp (t x / δ)) :=
    contDiff_const.add ((ht.div_const δ).exp)
  exact contDiff_const.mul (he.log (fun x => by positivity))

lemma contDiff_logProfile (δ c : ℝ) (p : ℕ) (t : R3 → ℝ)
    (hδ : 0 < δ) (ht : ContDiff ℝ ∞ t) :
    ContDiff ℝ ∞ (logProfile δ c p t) :=
  contDiff_const.add (contDiff_const.mul ((contDiff_softplus_comp δ t ht).log
    (fun x => (softplus_pos δ (t x) hδ).ne')))

lemma contDiff_log_referenceRadius (δ R : ℝ) (p : ℕ) (L : ℝ)
    (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (fun x => Real.log (referenceRadius δ R p L x)) := by
  rw [log_referenceRadius δ R p L hδ hR]
  exact contDiff_logProfile δ (Real.log R) p _ hδ (contDiff_referenceDepth L)

lemma densityWeightedDivergence_le_of_profile_hessian (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (c1 : ℝ) (x : R3)
    (hquad : ∀ X : R3, coordinateHessian f
      (fun V W => coordinateConnectionField (inverseMetricOperator g)
        (metricOperatorField g) x V W) x X X ≤
      -c1 * metricDifferentialNorm g f x * ⟪metricOperatorField g x X, X⟫_ℝ) :
    densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ) (vol g)
      (fun y => inverseMetricOperator g y (gradient f y)) x ≤
      -(3 * c1) * (vol g x * metricDifferentialNorm g f x) := by
  have h := densityWeightedDivergence_le_of_quadratic_metricHessian_local g f x
    (c1 * metricDifferentialNorm g f x)
    (fun i j => (hs i j).differentiable (by simp) x) (hp x)
    (Filter.Eventually.of_forall (fun y => (hp y).isHermitian))
    (hf.contDiffAt.of_le (by simp)) (fun X => by
      simpa only [inverseMetricOperator, neg_mul, mul_assoc] using hquad X)
  have he : (fun y => inverseMetricOperator g y (gradient f y)) =
      (fun y => matrixOperatorMap ((g y)⁻¹) (gradient f y)) := by
    funext y
    rw [inverseMetricOperator_eq_matrix_inverse_of_posDef g hp]
  rw [← he] at h
  convert h using 1 <;> ring

lemma dilatedReferenceMetric_smooth_entries (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam L : ℝ) : ∀ i j, ContDiff ℝ ∞
      (fun x => referenceMetric (dilatedMetric g lam) L x i j) := by
  exact EnergyBridge.conformalMatrix_smooth_entries _ _ (dilatedMetric_smooth_entries g hg lam)
    (contDiff_const.mul contDiff_referenceCoordinateDepth)

lemma dilatedReferenceMetric_posDef (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam L : ℝ) : ∀ x, (referenceMetric (dilatedMetric g lam) L x).PosDef :=
  EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef g hg lam)

theorem exists_dilated_referenceRadius_uniform_divergence_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L c0 c1 C T : ℝ, 0 < L ∧ 0 < c0 ∧ 0 < c1 ∧ 0 < C ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p j : ℕ, j ≤ p → ∀ x ∈ K,
        c0 * (p : ℝ) ≤ metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
          (fun y => Real.log (referenceRadius δ R p L y)) x ∧
        densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
          (vol (referenceMetric (dilatedMetric g lam) L))
          (fun y => inverseMetricOperator (referenceMetric (dilatedMetric g lam) L) y
            (gradient (fun z => Real.log (referenceRadius δ R p L z)) y)) x ≤
          -(3 * c1) * (vol (referenceMetric (dilatedMetric g lam) L) x *
            metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
              (fun y => Real.log (referenceRadius δ R p L y)) x) ∧
        referenceRadius δ R p L x *
          metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ j ≤
          R * (p : ℝ) ^ j * C ^ j * (Real.log (1 + Real.exp T)) ^ (p - j) := by
  obtain ⟨L, c0, c1, C, T, hL, hc0, hc1, hC, hbounds⟩ :=
    exists_dilated_referenceRadius_uniform_metric_bounds g hg K hK
  refine ⟨L, c0, c1, C, T, hL, hc0, hc1, hC, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p j hj x hx
  obtain ⟨hb, hH, hr⟩ := hbounds lam hlam δ hδ hδ1 R hR p j hj x hx
  refine ⟨hb, ?_, hr⟩
  exact densityWeightedDivergence_le_of_profile_hessian _
    (dilatedReferenceMetric_smooth_entries g hg lam L)
    (dilatedReferenceMetric_posDef g hg lam L) _
    (contDiff_log_referenceRadius δ R p L hδ hR) c1 x hH

theorem exists_dilated_referenceRadius_uniform_base_square_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L c1 : ℝ, 0 < L ∧ 0 < c1 ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, ∀ k : ℝ, 0 ≤ k → ∀ u : R3 → ℝ, ContDiff ℝ ∞ u →
        HasCompactSupport u → Function.support u ⊆ K →
        let γ := referenceMetric (dilatedMetric g lam) L
        let f := fun y => Real.log (referenceRadius δ R p L y)
        (∫ x : R3, vol γ x * coefficientQuadratic (inverseMetricOperator γ) x (gradient u x)) +
          k ^ 2 * (∫ x : R3, vol γ x * coefficientQuadratic (inverseMetricOperator γ) x
            (gradient f x) * u x ^ 2) +
          k * (3 * c1) * (∫ x : R3, (vol γ x * metricDifferentialNorm γ f x) * u x ^ 2) ≤
          (∫ x : R3, vol γ x * coefficientQuadratic (inverseMetricOperator γ) x
            (gradient u x + (k * u x) • gradient f x)) := by
  obtain ⟨L, c0, c1, C, T, hL, hc0, hc1, hC, hbounds⟩ :=
    exists_dilated_referenceRadius_uniform_divergence_bound g hg K hK
  refine ⟨L, c1, hL, hc1, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p k hk u hu hc hsupport
  let γ := referenceMetric (dilatedMetric g lam) L
  let f := fun y => Real.log (referenceRadius δ R p L y)
  have hs := dilatedReferenceMetric_smooth_entries g hg lam L
  have hp := dilatedReferenceMetric_posDef g hg lam L
  have hf := contDiff_log_referenceRadius δ R p L hδ hR
  apply compact_posDef_metric_density_gradient_profile_lower_bound
    (EuclideanSpace.basisFun (Fin 3) ℝ) γ hs hp k (3 * c1) hk u f
    (metricDifferentialNorm γ f) hu hf (continuous_metricDifferentialNorm γ hs hp f hf) hc
  intro x hx
  exact (hbounds lam hlam δ hδ hδ1 R hR p 0 (Nat.zero_le p) x (hsupport hx)).2.1

end OAI.AnisotropicCalderon.ConformalDepth
