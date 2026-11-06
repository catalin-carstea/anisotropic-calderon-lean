import Calderon.NormalizedGeodesicMetric
import Calderon.ShrinkingMetricBridge

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_commonRadius_endpointDerivative (Θ : E × E → E)
    (hΘ : ContDiff ℝ ∞ Θ) (y0 : E)
    (hD : HasFDerivAt Θ
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (y0,0))
    (K : Set E) (hK : IsCompact K) (κ : ℝ) (hκ : 0 < κ) :
    ∃ A : Set (E × ℝ), IsOpen A ∧ (y0,0) ∈ A ∧
      ∀ p ∈ A, ∀ z ∈ K,
        ‖normalizedEndpointDerivative Θ (p,z) - ContinuousLinearMap.id ℝ E‖ < κ := by
  have hc := (contDiff_normalizedEndpointDerivative Θ hΘ).continuous
  have ho : IsOpen {p : (E × ℝ) × E |
      ‖normalizedEndpointDerivative Θ p - ContinuousLinearMap.id ℝ E‖ < κ} :=
    isOpen_lt (hc.sub continuous_const).norm continuous_const
  have hsub : ({(y0,0)} : Set (E × ℝ)) ×ˢ K ⊆
      {p : (E × ℝ) × E |
        ‖normalizedEndpointDerivative Θ p - ContinuousLinearMap.id ℝ E‖ < κ} := by
    intro p hp
    have he : p.1 = (y0,0) := hp.1
    change ‖normalizedEndpointDerivative Θ (p.1,p.2) - ContinuousLinearMap.id ℝ E‖ < κ
    rw [he,normalizedEndpointDerivative_zero Θ y0 p.2 hD,sub_self,norm_zero]
    exact hκ
  obtain ⟨A,T,hA,_,ha,hKT,hAT⟩ :=
    generalized_tube_lemma isCompact_singleton hK ho hsub
  refine ⟨A,hA,ha (mem_singleton (y0,0)),?_⟩
  intro p hp z hz
  exact hAT (a := (p,z)) ⟨hp,hKT hz⟩

theorem exists_commonRadius_endpointDerivative_bound (Θ : E × E → E)
    (hΘ : ContDiff ℝ ∞ Θ) (y0 : E)
    (hD : HasFDerivAt Θ
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (y0,0))
    (K : Set E) (hK : IsCompact K) (κ : ℝ) (hκ : 0 < κ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y, ‖y-y0‖ ≤ ε → ∀ r : ℝ, |r| ≤ ε → ∀ z ∈ K,
      ‖normalizedEndpointDerivative Θ ((y,r),z) - ContinuousLinearMap.id ℝ E‖ < κ := by
  obtain ⟨A,hA,ha,hAK⟩ := exists_commonRadius_endpointDerivative Θ hΘ y0 hD K hK κ hκ
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hA (y0,0) ha
  refine ⟨δ/2,by positivity,?_⟩
  intro y hy r hr z hz
  apply hAK (y,r) (hball ?_) z hz
  rw [Metric.mem_ball,dist_eq_norm]
  change max ‖y-y0‖ ‖r-(0 : ℝ)‖ < δ
  apply max_lt
  · exact lt_of_le_of_lt hy (half_lt_self hδ)
  · simpa only [sub_zero,Real.norm_eq_abs] using lt_of_le_of_lt hr (half_lt_self hδ)

variable [FiniteDimensional ℝ E]

theorem exists_compact_operator_ellipticity {P : Type*} [TopologicalSpace P]
    (H : P → E →L[ℝ] E) (hH : Continuous H) (S : Set P) (hS : IsCompact S)
    (hpos : ∀ p ∈ S, ∀ u : E, u ≠ 0 → 0 < inner ℝ (H p u) u) :
    ∃ lam Λ : ℝ, 0 < lam ∧ 0 ≤ Λ ∧ ∀ p ∈ S,
      (∀ u : E, lam*‖u‖^2 ≤ inner ℝ (H p u) u) ∧
      ∀ u v : E, |inner ℝ (H p u) v| ≤ Λ*‖u‖*‖v‖ := by
  let q : P × E → ℝ := fun p => inner ℝ (H p.1 p.2) p.2
  have hq : Continuous q := ((hH.comp continuous_fst).clm_apply continuous_snd).inner
    continuous_snd
  have hT := hS.prod (isCompact_sphere (0 : E) 1)
  obtain ⟨lam,hlam,hlamq⟩ := hT.exists_forall_le' hq.continuousOn (a := (0 : ℝ)) (by
    intro p hp
    have hu : p.2 ≠ 0 := by
      have hn := mem_sphere_zero_iff_norm.mp hp.2
      intro hz
      simp [hz] at hn
    exact hpos p.1 hp.1 p.2 hu)
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn hH.continuousOn
  refine ⟨lam,max C 0,hlam,le_max_right _ _,?_⟩
  intro p hp
  constructor
  · intro u
    by_cases hu : u = 0
    · simp [hu]
    have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have hs : ‖u‖⁻¹ • u ∈ Metric.sphere (0 : E) 1 := by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_smul,norm_inv,norm_norm,inv_mul_cancel₀ hn]
    have hb := hlamq (p,‖u‖⁻¹ • u) ⟨hp,hs⟩
    have hb' : lam ≤ ‖u‖⁻¹ ^ 2 * inner ℝ (H p u) u := by
      simpa [q,map_smul,real_inner_smul_left,real_inner_smul_right,pow_two,mul_assoc] using hb
    have hm := mul_le_mul_of_nonneg_left hb' (sq_nonneg ‖u‖)
    have he : ‖u‖^2 * (‖u‖⁻¹ ^ 2 * inner ℝ (H p u) u) = inner ℝ (H p u) u := by
      field_simp [hn]
    rw [he] at hm
    simpa only [mul_comm] using hm
  · intro u v
    calc
      |inner ℝ (H p u) v| ≤ ‖H p u‖*‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖H p‖*‖u‖)*‖v‖ :=
        mul_le_mul_of_nonneg_right ((H p).le_opNorm u) (norm_nonneg v)
      _ ≤ (max C 0*‖u‖)*‖v‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ((hC p hp).trans (le_max_left _ _)) (norm_nonneg u))
        (norm_nonneg v)

variable [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem normalizedEndpointMetric_pos (Θ : E × E → E) (M : E → E →L[ℝ] E)
    (p : (E × ℝ) × E) (hM : ∀ x u, u ≠ 0 → 0 < inner ℝ (M x u) u)
    (hJ : Function.Injective (normalizedEndpointDerivative Θ p)) (u : E) (hu : u ≠ 0) :
    0 < inner ℝ (normalizedEndpointMetric Θ M p u) u := by
  rw [normalizedEndpointMetric_inner]
  apply hM
  intro hz
  apply hu
  exact hJ (hz.trans (map_zero _).symm)

theorem exists_commonRadius_metric_ellipticity (Θ : E × E → E)
    (M : E → E →L[ℝ] E) (hΘ : ContDiff ℝ ∞ Θ) (hM : ContDiff ℝ ∞ M)
    (hpos : ∀ x u, u ≠ 0 → 0 < inner ℝ (M x u) u) (y0 : E)
    (hD : HasFDerivAt Θ
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (y0,0))
    (K : Set E) (hK : IsCompact K) :
    ∃ ε lam Λ : ℝ, 0 < ε ∧ 0 < lam ∧ 0 ≤ Λ ∧
      ∀ y, ‖y-y0‖ ≤ ε → ∀ r : ℝ, |r| ≤ ε → ∀ z ∈ K,
        (∀ u : E, lam*‖u‖^2 ≤ inner ℝ (normalizedEndpointMetric Θ M ((y,r),z) u) u) ∧
        ∀ u v : E, |inner ℝ (normalizedEndpointMetric Θ M ((y,r),z) u) v| ≤ Λ*‖u‖*‖v‖ := by
  obtain ⟨ε,hε,hJ⟩ := exists_commonRadius_endpointDerivative_bound Θ hΘ y0 hD K hK
    (1/2) (by norm_num)
  let S : Set ((E × ℝ) × E) :=
    (Metric.closedBall y0 ε ×ˢ Icc (-ε) ε) ×ˢ K
  have hS : IsCompact S := ((isCompact_closedBall y0 ε).prod isCompact_Icc).prod hK
  have hP : ∀ p ∈ S, ∀ u : E, u ≠ 0 →
      0 < inner ℝ (normalizedEndpointMetric Θ M p u) u := by
    intro p hp u hu
    have hy : ‖p.1.1-y0‖ ≤ ε := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hp.1.1
    have hr : |p.1.2| ≤ ε := abs_le.mpr hp.1.2
    have hb := le_of_lt (hJ p.1.1 hy p.1.2 hr p.2 hp.2)
    have hi := ShrinkingMetricBridge.injective_of_norm_sub_id_le
      (normalizedEndpointDerivative Θ p) (1/2) (by norm_num)
      (ShrinkingMetricBridge.norm_map_sub_le_of_opNorm _ _ hb)
    exact normalizedEndpointMetric_pos Θ M p hpos hi u hu
  obtain ⟨lam,Λ,hlam,hΛ,hB⟩ := exists_compact_operator_ellipticity _
    (contDiff_normalizedEndpointMetric Θ M hΘ hM).continuous S hS hP
  refine ⟨ε,lam,Λ,hε,hlam,hΛ,?_⟩
  intro y hy r hr z hz
  apply hB ((y,r),z)
  exact ⟨⟨by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy,abs_le.mp hr⟩,hz⟩

end OAI.AnisotropicCalderon.ConnectionError

namespace OAI.AnisotropicCalderon.MetricOperator
theorem metricOperatorField_pos (g : MatrixField) (hg : IsAdmissibleMetric g)
    (x u : R3) (hu : u ≠ 0) : 0 < inner ℝ (metricOperatorField g x u) u := by
  have huf : (u : Fin 3 → ℝ) ≠ 0 := by
    intro hz
    apply hu
    ext i
    exact congrFun hz i
  have hp := (hg.posDef x).dotProduct_mulVec_pos huf
  simpa [metricOperatorField_apply,EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toEuclideanLin,Matrix.toLpLin_apply,dotProduct_comm] using hp
end OAI.AnisotropicCalderon.MetricOperator
