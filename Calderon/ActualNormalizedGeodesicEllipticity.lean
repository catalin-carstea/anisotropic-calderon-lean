import Calderon.CommonRadiusEllipticity

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_commonRadius_phase_domain (A : Set (E × E)) (hA : IsOpen A)
    (y0 : E) (ha : (y0,0) ∈ A) (K : Set E) (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y, ‖y-y0‖ ≤ ε → ∀ r : ℝ, |r| ≤ ε →
      ∀ z ∈ K, (y,r • z) ∈ A := by
  have hc : Continuous (fun p : (E × ℝ) × E => (p.1.1,p.1.2 • p.2)) :=
    (continuous_fst.fst).prodMk ((continuous_fst.snd).smul continuous_snd)
  have ho : IsOpen ((fun p : (E × ℝ) × E => (p.1.1,p.1.2 • p.2)) ⁻¹' A) :=
    hA.preimage hc
  have hsub : ({(y0,0)} : Set (E × ℝ)) ×ˢ K ⊆
      (fun p : (E × ℝ) × E => (p.1.1,p.1.2 • p.2)) ⁻¹' A := by
    intro p hp
    change (p.1.1,p.1.2 • p.2) ∈ A
    rw [show p.1 = (y0,0) from hp.1]
    simpa only [zero_smul] using ha
  obtain ⟨U,T,hU,_,h0,hKT,hUT⟩ :=
    generalized_tube_lemma isCompact_singleton hK ho hsub
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hU (y0,0) (h0 (mem_singleton (y0,0)))
  refine ⟨δ/2,by positivity,?_⟩
  intro y hy r hr z hz
  have hp : (y,r) ∈ U := by
    apply hball
    rw [Metric.mem_ball,dist_eq_norm]
    change max ‖y-y0‖ ‖r-(0 : ℝ)‖ < δ
    apply max_lt
    · exact lt_of_le_of_lt hy (half_lt_self hδ)
    · simpa only [sub_zero,Real.norm_eq_abs] using lt_of_le_of_lt hr (half_lt_self hδ)
  exact hUT (a := ((y,r),z)) ⟨hp,hKT hz⟩
end OAI.AnisotropicCalderon.ConnectionError

namespace OAI.AnisotropicCalderon.MetricOperator
open ConnectionError
theorem exists_actual_normalized_geodesic_ellipticity (g : MatrixField)
    (hg : IsAdmissibleMetric g) (y0 : R3) (K : Set R3) (hK : IsCompact K) :
    ∃ (Φ : (R3 × R3) → ℝ → R3 × R3) (ε lam Λ : ℝ),
      0 < ε ∧ 0 < lam ∧ 0 ≤ Λ ∧
      ContDiff ℝ ∞ (fun p : (R3 × R3) × ℝ => Φ p.1 p.2) ∧
      (∀ z, Φ z 0 = z) ∧
      ContDiff ℝ ∞ (fun z => (Φ z 1).1) ∧
      ContDiff ℝ ∞ (normalizedEndpointMetric (fun z => (Φ z 1).1) (metricOperatorField g)) ∧
      (∀ y, ‖y-y0‖ ≤ ε →
        (∀ t, Φ (y,0) t = (y,0)) ∧
        HasFDerivAt (fun z => (Φ z 1).1)
          (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0)) ∧
      ∀ y, ‖y-y0‖ ≤ ε → ∀ r : ℝ, |r| ≤ ε → ∀ z ∈ K,
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (Φ (y,r • z))
          (geodesicPhaseField (inverseMetricField (metricOperatorField g))
            (metricOperatorField g) (Φ (y,r • z) t)) t) ∧
        (∀ u : R3, lam*‖u‖^2 ≤ inner ℝ
          (normalizedEndpointMetric (fun z => (Φ z 1).1) (metricOperatorField g) ((y,r),z) u) u) ∧
        (∀ u v : R3, |inner ℝ
          (normalizedEndpointMetric (fun z => (Φ z 1).1) (metricOperatorField g) ((y,r),z) u) v|
            ≤ Λ*‖u‖*‖v‖) ∧
        normalizedEndpointMetric (fun z => (Φ z 1).1) (metricOperatorField g) ((y,0),z) =
          metricOperatorField g y := by
  obtain ⟨Φ,A,hA,ha,hΦ,h0,hstat,hODE,hΘ,hD⟩ :=
    exists_smooth_metric_geodesic_endpoint g hg y0
  obtain ⟨ε0,hε0,hdom⟩ := exists_commonRadius_phase_domain A hA y0 ha
    (K ∪ {0}) (hK.union isCompact_singleton)
  obtain ⟨ε1,lam,Λ,hε1,hlam,hΛ,hB⟩ := exists_commonRadius_metric_ellipticity
    (fun z => (Φ z 1).1) (metricOperatorField g) hΘ (contDiff_metricOperatorField g hg)
    (metricOperatorField_pos g hg) y0 (hD y0 ha) K hK
  let ε := min ε0 ε1
  have hε : 0 < ε := lt_min hε0 hε1
  have hc (y : R3) (hy : ‖y-y0‖ ≤ ε) : (y,0) ∈ A := by
    have h := hdom y (hy.trans (min_le_left _ _)) 0 (by simpa using hε0.le)
      0 (Or.inr (mem_singleton (0 : R3)))
    simpa only [zero_smul] using h
  refine ⟨Φ,ε,lam,Λ,hε,hlam,hΛ,hΦ,h0,hΘ,
    contDiff_normalizedEndpointMetric _ _ hΘ (contDiff_metricOperatorField g hg),
    (fun y hy => ⟨hstat y (hc y hy),hD y (hc y hy)⟩),?_⟩
  intro y hy r hr z hz
  have hin := hdom y (hy.trans (min_le_left _ _)) r (hr.trans (min_le_left _ _)) z (Or.inl hz)
  have hb := hB y (hy.trans (min_le_right _ _)) r (hr.trans (min_le_right _ _)) z hz
  refine ⟨hODE (y,r • z) hin,hb.1,hb.2,?_⟩
  exact normalizedEndpointMetric_zero _ _ y z
    (congrArg Prod.fst (hstat y (hc y hy) 1)) (hD y (hc y hy))
end OAI.AnisotropicCalderon.MetricOperator
