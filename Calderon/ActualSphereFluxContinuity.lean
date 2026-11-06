import Calderon.ActualSphereFluxDistribution
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.RadialTestIntegration
open SphereHarmonic

theorem continuousOn_surfaceIntegral_smul (f : R3 → ℝ) (R : ℝ)
    (hf : ContinuousOn f (closedBall (0 : R3) R)) :
    ContinuousOn (fun r : ℝ => ∫ «ω» : UnitSphere, f (r • «ω».val) ∂surfaceMeasure)
      (Icc (0 : ℝ) R) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : R3) R).exists_bound_of_continuousOn hf
  have hmem (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) («ω» : UnitSphere) :
      r • «ω».val ∈ closedBall (0 : R3) R := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_eq_of_mem_sphere «ω», mul_one,
      Real.norm_of_nonneg hr.1]
    exact hr.2
  apply continuousOn_of_dominated (μ := surfaceMeasure)
    (F := fun r : ℝ => fun «ω» : UnitSphere => f (r • «ω».val))
    (bound := fun _ : UnitSphere => C)
  · intro r hr
    have hscale : Continuous (fun «ω» : UnitSphere => r • «ω».val) :=
      (continuous_const : Continuous (fun _ : UnitSphere => r)).smul
        (continuous_subtype_val : Continuous (fun x : UnitSphere => (x.val : R3)))
    have hc : Continuous (fun «ω» : UnitSphere => f (r • «ω».val)) :=
      hf.comp_continuous hscale (hmem r hr)
    exact hc.aestronglyMeasurable (μ := surfaceMeasure)
  · intro r hr
    exact ae_of_all surfaceMeasure fun «ω» => hC _ (hmem r hr «ω»)
  · exact integrable_const (μ := surfaceMeasure) C
  · apply ae_of_all surfaceMeasure
    intro «ω»
    exact hf.comp (continuous_id.smul continuous_const).continuousOn
      (fun r hr => hmem r hr «ω»)

theorem continuousOn_sphereFlux (V : R3 → R3) (hV : Continuous V) (R : ℝ) :
    ContinuousOn (sphereFlux V) (Icc (0 : ℝ) R) := by
  have hq : Continuous (fun x : R3 => ⟪x,V x⟫_ℝ) := continuous_id.inner hV
  have hi := continuousOn_surfaceIntegral_smul (fun x : R3 => ⟪x,V x⟫_ℝ) R hq.continuousOn
  have he : sphereFlux V = (fun r : ℝ => r *
      ∫ «ω» : UnitSphere, ⟪r • «ω».val,V (r • «ω».val)⟫_ℝ ∂surfaceMeasure) := by
    funext r
    unfold sphereFlux
    simp_rw [real_inner_smul_left]
    rw [integral_const_mul]
    ring
  rw [he]
  exact continuousOn_id.mul hi

theorem continuousOn_sphereDivergenceProfile
    (b : OrthonormalBasis (Fin 3) ℝ R3) (V : R3 → R3) (hV : ContDiff ℝ 1 V) (R : ℝ) :
    ContinuousOn (sphereDivergenceProfile b V) (Icc (0 : ℝ) R) := by
  have hc : Continuous (radialDivergence b V) := by
    unfold radialDivergence
    apply continuous_finset_sum
    intro i hi
    exact (innerSL ℝ (b i)).continuous.comp
      ((hV.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hi := continuousOn_surfaceIntegral_smul (radialDivergence b V) R hc.continuousOn
  exact (continuousOn_id.pow 2).mul hi

theorem sphereFlux_zero (V : R3 → R3) : sphereFlux V 0 = 0 := by
  simp only [sphereFlux, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]

end OAI.AnisotropicCalderon.RadialTestIntegration

#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.continuousOn_surfaceIntegral_smul
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.continuousOn_sphereFlux
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.continuousOn_sphereDivergenceProfile
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.sphereFlux_zero
