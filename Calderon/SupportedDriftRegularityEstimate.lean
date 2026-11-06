import Calderon.SupportedDriftPrincipalRegularity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem norm_sub_le_successor_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : E →L[ℝ] F) (V : E) (f : F) (m B : ℝ) (hm : 0 ≤ m)
    (hV : ‖V‖ ≤ B * (m + ‖f‖)) :
    m + ‖f - D V‖ ≤ (2 + ‖D‖ * B) * (m + ‖f‖) := by
  have hD : ‖D V‖ ≤ ‖D‖ * (B * (m + ‖f‖)) :=
    (D.le_opNorm V).trans (mul_le_mul_of_nonneg_left hV (norm_nonneg D))
  calc
    m + ‖f - D V‖ ≤ m + (‖f‖ + ‖D V‖) :=
      add_le_add (le_refl m) (norm_sub_le f (D V))
    _ ≤ m + (‖f‖ + ‖D‖ * (B * (m + ‖f‖))) :=
      add_le_add (le_refl m) (add_le_add (le_refl ‖f‖) hD)
    _ = (1 + ‖D‖ * B) * (m + ‖f‖) := by ring
    _ ≤ (2 + ‖D‖ * B) * (m + ‖f‖) :=
      mul_le_mul_of_nonneg_right
        (add_le_add (by norm_num : (1 : ℝ) ≤ 2) (le_refl (‖D‖ * B)))
        (add_nonneg hm (norm_nonneg f))


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
