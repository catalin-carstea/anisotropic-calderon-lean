import Calderon.ActualSourcePartnerPullbackMetric
import Calderon.NativeMetricScalarProduct
import Calderon.PrincipalCoefficientInjectivity

/-! HELD exact Main M5 closing stitch. The actual pullback parent must be
genuinely checked before this source may be compiled or staged. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature ConnectionError NativeSourceChartCalculus

theorem metric_eq_pullback_of_source_response_eq
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (Phi : R3 ≃ R3) (hPhi : ContDiff ℝ ∞ (Phi : R3 → R3))
    (hInv : ContDiff ℝ ∞ (Phi.symm : R3 → R3))
    (hFix : ∀ x : R3, 1 ≤ ‖x‖ → Phi x = x)
    (hMatch : ∀ x ∈ (radiusTwoOpens : Set R3),
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 s x =
        radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s (Phi x)) :
    ∀ x : R3, g2 x = (D (Phi : R3 → R3) x).transpose * g1 (Phi x) * D (Phi : R3 → R3) x := by
  classical
  let k : MatrixField := pullbackMetric g1 (Phi : R3 → R3)
  let c : R3 → ℝ := sourcePartnerPullbackPrincipalScalar g1 g2 Phi
  let C : Set R3 := ball (0 : R3) (5/4 : ℝ)
  have hk : IsAdmissibleMetric k :=
    isAdmissibleMetric_pullbackMetric_of_smooth_equiv_fixes_exterior g1 hg1 Phi hPhi hInv hFix
  have hc : DifferentiableOn ℝ c C :=
    ((contDiff_sourcePartnerPullbackPrincipalScalar g1 g2 hg1 hg2 Phi hPhi hInv hFix).differentiable
      (by simp)).differentiableOn
  have hCoeff : ∀ x ∈ C, principalCoefficient k x = c x • principalCoefficient g2 x :=
    principalCoefficient_pullback_eq_scalar_smul_of_source_match
      g1 g2 hg1 hg2 Phi hPhi hInv hFix hMatch
  have hPDE : ∀ source : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ C,
      nativeMetricDifferential k
        (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 source) x = 0 := by
    intro source x hx
    exact nativeMetricDifferential_pullback_source_eq_zero_of_source_match
      g1 g2 hg1 hg2 Phi hPhi hInv hFix hMatch source x hx
  have hRoom : C ⊆ (radiusTwoOpens : Set R3) :=
    ball_subset_ball (by norm_num : (5/4 : ℝ) ≤ 2)
  have hSource : ∀ x ∈ C, x ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ) :=
    notMem_fixedExteriorSource_closedBall_of_mem_ball_five_fourths
  let p : R3 := EuclideanSpace.single (0 : Fin 3) (9/8 : ℝ)
  have hpNorm : ‖p‖ = (9/8 : ℝ) := by
    dsimp only [p]
    rw [EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hp : p ∈ C := mem_ball_zero_iff.mpr (by rw [hpNorm]; norm_num)
  have hpExterior : 1 ≤ ‖p‖ := by rw [hpNorm]; norm_num
  have hConst : EqOn c (fun _ => c p) C :=
    eqOn_const_of_nativeMetricDifferential_source_eq_zero
      fixedDirichletRegularity fixedSobolevCalculus k g2 hg2 c C isOpen_ball
      (convex_ball (0 : R3) (5/4 : ℝ)).isPreconnected hRoom hSource hc hCoeff hPDE p hp
  have hpOne : c p = 1 := by
    change principalCoefficient k p 2 2 / principalCoefficient g2 p 2 2 = 1
    rw [principalCoefficient_eq_one_of_exterior k hk p hpExterior,
      principalCoefficient_eq_one_of_exterior g2 hg2 p hpExterior]
    norm_num
  have hMetric : EqOn g2 k C := by
    intro x hx
    have hcOne : c x = 1 := (hConst hx).trans hpOne
    have hAx := hCoeff x hx
    rw [hcOne, one_smul] at hAx
    exact (eq_of_principalCoefficient_eq_at_of_posDef k g2 x (hk.posDef x) (hg2.posDef x) hAx).symm
  intro x
  rw [← pullbackMetric_eq_original_D]
  change g2 x = k x
  by_cases hx : x ∈ C
  · exact hMetric hx
  · have hnorm : (5/4 : ℝ) ≤ ‖x‖ :=
      le_of_not_gt (fun h => hx (mem_ball_zero_iff.mpr h))
    have hExterior : 1 ≤ ‖x‖ := by linarith
    rw [hg2.euclidean_exterior x hExterior, hk.euclidean_exterior x hExterior]

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.metric_eq_pullback_of_source_response_eq
