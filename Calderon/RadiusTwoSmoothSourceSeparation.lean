import Calderon.RadiusTwoSmoothSourceCommonExterior

/-! A conditional application of A.7. -/
set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature

def radiusTwoSmoothSourceEvaluationLinear
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3) :
    𝓓(fixedExteriorSourceOpens, ℝ) →ₗ[ℝ] ℝ where
  toFun f := radiusTwoSmoothSourceResponse hreg hcalc g hg f p
  map_add' f k := congrFun (radiusTwoSmoothSourceResponse_add hreg hcalc g hg f k) p
  map_smul' c f := congrFun (radiusTwoSmoothSourceResponse_smul hreg hcalc g hg c f) p

theorem radiusTwoSmoothSourceEvaluationLinear_apply
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (f : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    radiusTwoSmoothSourceEvaluationLinear hreg hcalc g hg p f =
      radiusTwoSmoothSourceResponse hreg hcalc g hg f p := rfl

theorem radiusTwoSmoothSourceResponse_separates_points
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3))
    (q : R3) (hq : q ∈ closedBall (0 : R3) 2) (hpq : p ≠ q) :
    ∃ f : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse hreg hcalc g hg f p ≠
        radiusTwoSmoothSourceResponse hreg hcalc g hg f q :=
  (hSep g hg (radiusTwoSmoothSourceResponse hreg hcalc g hg)
    (isRadiusTwoSmoothSourceResponse_radiusTwoSmoothSourceResponse hreg hcalc g hg)).1 p hp q hq hpq

theorem exists_radiusTwoSmoothSourceResponse_ne_zero
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) :
    ∃ f : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse hreg hcalc g hg f p ≠ 0 := by
  let q : R3 := EuclideanSpace.single (0 : Fin 3) (2 : ℝ)
  have hnq : ‖q‖ = 2 := by simp [q, EuclideanSpace.norm_single]
  have hq : q ∈ closedBall (0 : R3) 2 := by simp [mem_closedBall, dist_eq_norm, hnq]
  have hpq : p ≠ q := by
    intro heq
    have hpNorm : ‖p‖ < 2 := mem_ball_zero_iff.mp hp
    rw [heq, hnq] at hpNorm
    linarith
  obtain ⟨f,hf⟩ := radiusTwoSmoothSourceResponse_separates_points hreg hcalc hSep g hg p hp q hq hpq
  have hZero := (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg f).2.2.2 q (by rw [hnq])
  exact ⟨f, by simpa only [hZero] using hf⟩

theorem radiusTwoSmoothSourceEvaluationLinear_injective
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation) (g : MatrixField) (hg : IsAdmissibleMetric g) :
    Function.Injective (fun p : (radiusTwoOpens : Set R3) =>
      radiusTwoSmoothSourceEvaluationLinear hreg hcalc g hg (p : R3)) := by
  intro p q heq
  apply Subtype.ext
  by_contra hne
  obtain ⟨f,hf⟩ := radiusTwoSmoothSourceResponse_separates_points
    hreg hcalc hSep g hg p p.property q (ball_subset_closedBall q.property) hne
  exact hf (congrArg (fun L : 𝓓(fixedExteriorSourceOpens, ℝ) →ₗ[ℝ] ℝ => L f) heq)

theorem radiusTwoSmoothSourceResponse_fderiv_surjective
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) :
    Function.Surjective (fun f : 𝓓(fixedExteriorSourceOpens, ℝ) =>
      fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg f) p) :=
  (hSep g hg (radiusTwoSmoothSourceResponse hreg hcalc g hg)
    (isRadiusTwoSmoothSourceResponse_radiusTwoSmoothSourceResponse hreg hcalc g hg)).2 p hp

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceEvaluationLinear
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceEvaluationLinear_apply
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponse_separates_points
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSmoothSourceResponse_ne_zero
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceEvaluationLinear_injective
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponse_fderiv_surjective
