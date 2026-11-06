import Calderon.ActualReferenceWeakRoom
import Calderon.SmoothCommonSupportStrongOperator
import Calderon.CompactInverseDerivativeBounds

/-! Source-only exact joint actual inverse topology on the same common weak
room. Joint coefficient maps are the native maps of the identical evaluated
spatial functions. No new operator or desired uniform inverse premise. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

theorem jointReferenceStrongCoefficient_data :
    ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ w ∧
    ContDiff ℝ ∞ (conformalReferenceFramedDriftBase g L Φ H) ∧
    (∀ p z, z ∉ closedBall (0 : R3) 3 → a (p,z) = 0) ∧
    (∀ p z, z ∉ closedBall (0 : R3) 3 → w (p,z) = 0) := by
  rcases hData.1 with ⟨_,_,_,_,_,_,_,_,ha,hw,hSupport,_,_,_,_⟩
  refine ⟨ha,hw,hData.2.1,?_,?_⟩
  · intro p z hz
    have hz3 : 3 ≤ ‖z‖ := le_of_lt (by
      simpa only [mem_closedBall,dist_zero_right,not_le] using hz)
    exact (hSupport p z hz3).1
  · intro p z hz
    have hz3 : 3 ≤ ‖z‖ := le_of_lt (by
      simpa only [mem_closedBall,dist_zero_right,not_le] using hz)
    exact (hSupport p z hz3).2


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
