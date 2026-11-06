import Calderon.RadiusTwoNativeL2Dilation
import Calderon.RadiusTwoBoundedSourceOperator

/-! EXPANSION.json and AUTHORITY-SUPPLEMENT.json precede this actual source H2 bound.
The pre-existing regularity proposition remains an explicit hypothesis. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal ContDiff InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem norm_radiusTwoNormalizedSource_and_forcing_le
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f : RadiusTwoL2) :
    ‖radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f)‖ +
      ‖((4 : ℝ) • radiusTwoNativeL2Dilation f : BallSobolev 0)‖ ≤
        (3 * ‖radiusTwoSourceSolutionL g hg‖ + 4) * ‖f‖ := by
  let u : BallH1Zero := radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f)
  let f1 : BallSobolev 0 := (4 : ℝ) • radiusTwoNativeL2Dilation f
  have hP : ‖radiusTwoNativeL2Dilation f‖ ≤ ‖f‖ :=
    ((radiusTwoNativeL2Dilation (V := ℝ)).le_opNorm f).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (norm_radiusTwoNativeL2Dilation_le_one (V := ℝ)) (norm_nonneg f))
  have hf1 : ‖f1‖ ≤ 4 * ‖f‖ := by
    calc
      ‖f1‖ = (4 : ℝ) * ‖radiusTwoNativeL2Dilation f‖ := by
        dsimp only [f1]
        rw [norm_smul,Real.norm_eq_abs]
        norm_num
      _ ≤ 4 * ‖f‖ := mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 4)
  have hu : ‖u‖ ≤ 3 * (‖radiusTwoSourceSolutionL g hg‖ * ‖f‖) := by
    calc
      ‖u‖ ≤ ‖radiusTwoNativeZeroDilation‖ * ‖radiusTwoSourceSolution g hg f‖ :=
        radiusTwoNativeZeroDilation.le_opNorm _
      _ ≤ 3 * ‖radiusTwoSourceSolution g hg f‖ := mul_le_mul_of_nonneg_right
        norm_radiusTwoNativeZeroDilation_le_three (norm_nonneg _)
      _ ≤ 3 * (‖radiusTwoSourceSolutionL g hg‖ * ‖f‖) :=
        mul_le_mul_of_nonneg_left (norm_radiusTwoSourceSolution_le g hg f) (by norm_num)
  change ‖u‖ + ‖f1‖ ≤ (3 * ‖radiusTwoSourceSolutionL g hg‖ + 4) * ‖f‖
  calc
    ‖u‖ + ‖f1‖ ≤ 3 * (‖radiusTwoSourceSolutionL g hg‖ * ‖f‖) + 4 * ‖f‖ :=
      add_le_add hu hf1
    _ = _ := by ring

end OAI.AnisotropicCalderon.ExteriorSource
