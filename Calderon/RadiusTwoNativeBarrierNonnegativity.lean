import Calderon.RadiusTwoNativePolynomialBarrier

/-! EXPANSION.json precedes this literal native barrier nonnegativity consequence. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier

lemma radiusTwoBarrierH1_value_nonneg_ae (M : ℝ) (hM : 0 ≤ M) :
    ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
      0 ≤ TauCeti.W1p.value (radiusTwoBarrierH1 M) x := by
  filter_upwards [radiusTwoBarrierH1_value_ae M,
    ae_restrict_mem radiusTwoOpens.isOpen.measurableSet] with x hValue hx
  have hNorm : ‖x‖ < 2 := by
    change x ∈ ball (0 : R3) 2 at hx
    exact mem_ball_zero_iff.mp hx
  have hSq : ‖x‖ ^ 2 ≤ 4 := by
    have h := (sq_le_sq₀ (norm_nonneg x) (by norm_num : (0 : ℝ) ≤ 2)).mpr hNorm.le
    norm_num at h ⊢
    exact h
  rw [hValue]
  exact mul_nonneg hM (sub_nonneg.mpr hSq)

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoBarrierH1_value_nonneg_ae
