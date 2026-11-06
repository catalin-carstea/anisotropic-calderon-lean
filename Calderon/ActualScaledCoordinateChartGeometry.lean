import Calderon.ActualCoordinateChartSeparation
import TaskInterface
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter TopologicalSpace
open scoped Topology ContDiff Matrix.Norms.Elementwise NNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConnectionError ExteriorSource

theorem exists_scaled_coordinate_chart_geometry
    (X : R3 → R3) (U : Set R3) (hU : IsOpen U) (h0 : (0:R3) ∈ U)
    (hX : ContDiffOn ℝ ∞ X U)
    (hJ : IsUnit (coordinateJacobianMatrix X 0).det)
    (hRoom : X 0 ∈ (radiusTwoOpens : Set R3))
    (B : ℝ) (hB : 0 < B) :
    ∃ (lambda0 c b : ℝ), 0 < lambda0 ∧ lambda0 ≤ 1 ∧ 0 < c ∧ 0 < b ∧ b < 2 ∧
      (∀ lambda ∈ Ioc (0:ℝ) lambda0, ∀ x : R3, ‖x‖ ≤ B →
        lambda • x ∈ U ∧ ‖X (lambda • x)‖ ≤ b) ∧
      (∀ lambda ∈ Ioc (0:ℝ) lambda0, ∀ x y : R3, ‖x‖ ≤ B → ‖y‖ ≤ B →
        c * lambda * dist x y ≤ dist (X (lambda • x)) (X (lambda • y))) := by
  have hAt := hX.contDiffAt (hU.mem_nhds h0)
  obtain ⟨r, c, hr, hc, hSep⟩ := exists_coordinate_chart_local_separation X hAt hJ
  have hNorm : ‖X 0‖ < 2 := mem_ball_zero_iff.mp hRoom
  let b : ℝ := (‖X 0‖+2)/2
  have hb : 0 < b := by dsimp only [b]; positivity
  have hb2 : b < 2 := by dsimp only [b];linarith
  have hImage : ∀ᶠ x in 𝓝 (0:R3), ‖X x‖ < b :=
    (hAt.continuousAt.norm.eventually_lt_const (by dsimp only [b];linarith))
  obtain ⟨rI,hrI,hBI⟩ := Metric.mem_nhds_iff.mp hImage
  obtain ⟨rU,hrU,hBU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let a : ℝ := min r (min rI rU)
  have ha : 0 < a := lt_min hr (lt_min hrI hrU)
  let lambda0 : ℝ := min 1 (a/(B+1))
  have hl : 0 < lambda0 := lt_min zero_lt_one (div_pos ha (by linarith))
  have hBall : ∀ lambda ∈ Ioc (0:ℝ) lambda0, ∀ x : R3, ‖x‖ ≤ B →
      lambda • x ∈ ball (0:R3) a := by
    intro lambda hlambda x hx
    rw [mem_ball_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos hlambda.1]
    have hla : lambda * (B+1) ≤ a := (le_div_iff₀ (by linarith : 0 < B+1)).mp
      (hlambda.2.trans (min_le_right _ _))
    have hmul : lambda * ‖x‖ ≤ lambda * B := mul_le_mul_of_nonneg_left hx hlambda.1.le
    nlinarith only [hla,hmul,hlambda.1]
  refine ⟨lambda0,c,b,hl,min_le_left _ _,hc,hb,hb2,?_,?_⟩
  · intro lambda hlambda x hx
    have hxa := hBall lambda hlambda x hx
    refine ⟨hBU ((ball_subset_ball (min_le_right _ _ |>.trans (min_le_right _ _))) hxa),?_⟩
    exact (hBI ((ball_subset_ball (min_le_right _ _ |>.trans (min_le_left _ _))) hxa)).le
  · intro lambda hlambda x y hx hy
    have hxr : lambda • x ∈ ball (0:R3) r := ball_subset_ball (min_le_left _ _) (hBall lambda hlambda x hx)
    have hyr : lambda • y ∈ ball (0:R3) r := ball_subset_ball (min_le_left _ _) (hBall lambda hlambda y hy)
    have h := hSep (lambda • x) hxr (lambda • y) hyr
    rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos hlambda.1] at h
    simpa only [mul_assoc] using h

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
