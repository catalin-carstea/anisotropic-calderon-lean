import Calderon.ActualEnlargedBallNormalizedMetric
import Calderon.NativeH1InwardDilation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! EXPANSION.json precedes literal dimension-three radius-two rescaling. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped Pointwise ContDiff Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError DirichletFamily

theorem two_smul_ball_one_eq_ball_two :
    (2 : ℝ) • ball (0 : R3) 1 = ball (0 : R3) 2 := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs]
  norm_num
  constructor <;> intro h <;> linarith

theorem setIntegral_ball_two_eq_eight_comp_two (f : R3 → ℝ) :
    (∫ z in ball (0 : R3) 2, f z ∂(volume : Measure R3)) =
      8 * (∫ x in ball (0 : R3) 1, f ((2 : ℝ) • x) ∂(volume : Measure R3)) := by
  have h := Measure.setIntegral_comp_smul (volume : Measure R3) f
    (ball (0 : R3) 1) (by norm_num : (2 : ℝ) ≠ 0)
  have hRank : Module.finrank ℝ R3 = 3 := finrank_euclideanSpace_fin
  rw [two_smul_ball_one_eq_ball_two,hRank] at h
  norm_num [smul_eq_mul] at h
  linarith

theorem gradient_smooth_comp_two (w : SmoothData) (x : R3) :
    (gradient (fun z : R3 => w.1 ((2 : ℝ) • z)) x : R3) =
      (2 : ℝ) • (gradient w.1 ((2 : ℝ) • x) : R3) :=
  gradient_comp_const_smul w.1 2 x ((w.2.differentiable (by simp)) ((2 : ℝ) • x))

theorem metricBilinear_density_comp_two
    (g : MatrixField) (w v : SmoothData) (x : R3) :
    TauCeti.PDE.matrixBilinearForm (principalCoefficient (enlargedBallNormalizedMetric g 2) x)
      (gradient (fun z : R3 => w.1 ((2 : ℝ) • z)) x : R3)
      (gradient (fun z : R3 => v.1 ((2 : ℝ) • z)) x : R3) =
      4 * TauCeti.PDE.matrixBilinearForm (principalCoefficient g ((2 : ℝ) • x))
        (gradient w.1 ((2 : ℝ) • x) : R3) (gradient v.1 ((2 : ℝ) • x) : R3) := by
  rw [principalCoefficient_enlargedBallNormalizedMetric,
    gradient_smooth_comp_two w x,gradient_smooth_comp_two v x]
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul,RingHom.id_apply]
  ring

theorem metricBilinear_energy_ball_two_rescaling
    (g : MatrixField) (w v : SmoothData) :
    (∫ z in ball (0 : R3) 2, TauCeti.PDE.matrixBilinearForm (principalCoefficient g z)
      (gradient w.1 z : R3) (gradient v.1 z : R3) ∂(volume : Measure R3)) =
      2 * (∫ x in ball (0 : R3) 1,
        TauCeti.PDE.matrixBilinearForm (principalCoefficient (enlargedBallNormalizedMetric g 2) x)
          (gradient (fun z : R3 => w.1 ((2 : ℝ) • z)) x : R3)
          (gradient (fun z : R3 => v.1 ((2 : ℝ) • z)) x : R3) ∂(volume : Measure R3)) := by
  rw [setIntegral_ball_two_eq_eight_comp_two]
  have hFour : (∫ x in ball (0 : R3) 1,
      TauCeti.PDE.matrixBilinearForm (principalCoefficient (enlargedBallNormalizedMetric g 2) x)
        (gradient (fun z : R3 => w.1 ((2 : ℝ) • z)) x : R3)
        (gradient (fun z : R3 => v.1 ((2 : ℝ) • z)) x : R3) ∂(volume : Measure R3)) =
      4 * (∫ x in ball (0 : R3) 1,
        TauCeti.PDE.matrixBilinearForm (principalCoefficient g ((2 : ℝ) • x))
          (gradient w.1 ((2 : ℝ) • x) : R3) (gradient v.1 ((2 : ℝ) • x) : R3)
          ∂(volume : Measure R3)) := by
    calc
      _ = ∫ x in ball (0 : R3) 1,
          4 * TauCeti.PDE.matrixBilinearForm (principalCoefficient g ((2 : ℝ) • x))
            (gradient w.1 ((2 : ℝ) • x) : R3) (gradient v.1 ((2 : ℝ) • x) : R3)
            ∂(volume : Measure R3) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => metricBilinear_density_comp_two g w v x))
      _ = _ := integral_const_mul 4 _
  rw [hFour]
  ring

theorem source_pairing_ball_two_rescaling (F w : R3 → ℝ) :
    (∫ z in ball (0 : R3) 2, F z * w z ∂(volume : Measure R3)) =
      8 * (∫ x in ball (0 : R3) 1, F ((2 : ℝ) • x) * w ((2 : ℝ) • x)
        ∂(volume : Measure R3)) :=
  setIntegral_ball_two_eq_eight_comp_two (fun z => F z * w z)

theorem smoothSourceFunctional_ball_two_rescaling
    (g : MatrixField) (F : R3 → ℝ) (w : SmoothData) :
    (1/2 : ℝ) * (∫ z in ball (0 : R3) 2,
      TauCeti.PDE.matrixBilinearForm (principalCoefficient g z)
        (gradient w.1 z : R3) (gradient w.1 z : R3) ∂(volume : Measure R3)) -
      (∫ z in ball (0 : R3) 2, F z * w.1 z ∂(volume : Measure R3)) =
    2 * ((1/2 : ℝ) * (∫ x in ball (0 : R3) 1,
      TauCeti.PDE.matrixBilinearForm (principalCoefficient (enlargedBallNormalizedMetric g 2) x)
        (gradient (fun z : R3 => w.1 ((2 : ℝ) • z)) x : R3)
        (gradient (fun z : R3 => w.1 ((2 : ℝ) • z)) x : R3) ∂(volume : Measure R3)) -
      4 * (∫ x in ball (0 : R3) 1, F ((2 : ℝ) • x) * w.1 ((2 : ℝ) • x)
        ∂(volume : Measure R3))) := by
  rw [metricBilinear_energy_ball_two_rescaling,source_pairing_ball_two_rescaling]
  ring

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.two_smul_ball_one_eq_ball_two
#print axioms OAI.AnisotropicCalderon.ExteriorSource.setIntegral_ball_two_eq_eight_comp_two
#print axioms OAI.AnisotropicCalderon.ExteriorSource.gradient_smooth_comp_two
#print axioms OAI.AnisotropicCalderon.ExteriorSource.metricBilinear_density_comp_two
#print axioms OAI.AnisotropicCalderon.ExteriorSource.metricBilinear_energy_ball_two_rescaling
#print axioms OAI.AnisotropicCalderon.ExteriorSource.source_pairing_ball_two_rescaling
#print axioms OAI.AnisotropicCalderon.ExteriorSource.smoothSourceFunctional_ball_two_rescaling
