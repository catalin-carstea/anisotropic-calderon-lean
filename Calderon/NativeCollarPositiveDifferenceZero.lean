import Calderon.NativeNonnegativeBarrierZeroTruncation
import Calderon.NativeBoundaryCollarCutoff
import Calderon.NativeNestedCutoffZeroLocalization
import Calderon.NativeCutoffRestrictionValueRecovery
import Calderon.NativePositivePartRestriction
import Calderon.NativePositiveDifferenceValues
import Calderon.RadiusTwoEuclideanCollar

/-! EXPANSION.json precedes derived annular positive-difference zero membership. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier

lemma restrict_posPart_sub_mem_collar_zero_of_innerBand
    (a aPrime b : ℝ) (ha : 0 < a) (haa : a < aPrime) (hab : aPrime < b)
    (u v : RadiusTwoH1) (hu : u ∈ TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2)
    (hv : ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens, 0 ≤ TauCeti.W1p.value v x)
    (hBand : ∀ᵐ x ∂(volume : Measure R3).restrict (radiusTwoCollarOpens a),
      ‖x‖ < b → TauCeti.W1p.value u x ≤ TauCeti.W1p.value v x) :
    TauCeti.W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a)
      (TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (u-v)) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) (radiusTwoCollarOpens a) 2 := by
  let z : RadiusTwoH1 := TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (u-v)
  have hz : z ∈ TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2 :=
    posPart_sub_mem_w1p0Submodule_of_nonneg u v hu hv
  obtain ⟨eta,C,hEta,hC,hVal,hGrad,hZero,hOut,hSupport⟩ :=
    exists_boundaryCollarCutoff (E := R3) aPrime b (ha.trans haa) hab
  have hSupportU : tsupport eta ∩ (radiusTwoOpens : Set R3) ⊆ (radiusTwoCollarOpens a : Set R3) := by
    intro x hx
    have hNotBall : x ∉ ball (0 : R3) aPrime := hSupport hx.1
    have hNormLow : aPrime ≤ ‖x‖ := le_of_not_gt
      (fun h => hNotBall (mem_ball_zero_iff.mpr h))
    have hNormHigh : ‖x‖ < 2 := by
      have hx2 := hx.2
      change x ∈ ball (0 : R3) 2 at hx2
      exact mem_ball_zero_iff.mp hx2
    exact ⟨haa.trans_le hNormLow,hNormHigh⟩
  have hMu : (volume : Measure R3).restrict (radiusTwoCollarOpens a) ≤
      (volume : Measure R3).restrict radiusTwoOpens :=
    Measure.restrict_mono_set volume
      (SetLike.coe_subset_coe.mpr (radiusTwoCollarOpens_le_radiusTwoOpens a))
  have hZValue := (native_posPart_sub_value_ae u v).filter_mono (ae_mono hMu)
  have hRecovery : ∀ᵐ x ∂(volume : Measure R3).restrict (radiusTwoCollarOpens a),
      eta x ≠ 1 → TauCeti.W1p.value z x = 0 := by
    filter_upwards [hZValue,hBand] with x hZ hB
    intro hNe
    have hxb : ‖x‖ < b := by
      by_contra hNot
      have hNotBall : x ∉ ball (0 : R3) b := fun hx => hNot (mem_ball_zero_iff.mp hx)
      exact hNe (hOut x hNotBall)
    exact hZ.trans (max_eq_right (sub_nonpos.mpr (hB hxb)))
  have hMem := restrict_contDiffSMul_mem_w1p0Submodule
    (radiusTwoCollarOpens_le_radiusTwoOpens a) eta hEta hC
    (fun x _ => hVal x) (fun x _ => hGrad x) hSupportU hz
  have hEq := restrict_contDiffSMul_eq_of_value_zero_on_ne_one
    (radiusTwoCollarOpens_le_radiusTwoOpens a) eta hEta hC
    (fun x _ => hVal x) (fun x _ => hGrad x) z hRecovery
  exact hEq ▸ hMem

lemma posPart_restrict_sub_mem_collar_zero_of_innerBand
    (a aPrime b : ℝ) (ha : 0 < a) (haa : a < aPrime) (hab : aPrime < b)
    (u v : RadiusTwoH1) (hu : u ∈ TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2)
    (hv : ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens, 0 ≤ TauCeti.W1p.value v x)
    (hBand : ∀ᵐ x ∂(volume : Measure R3).restrict (radiusTwoCollarOpens a),
      ‖x‖ < b → TauCeti.W1p.value u x ≤ TauCeti.W1p.value v x) :
    TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (TauCeti.W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) u -
        TauCeti.W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) v) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) (radiusTwoCollarOpens a) 2 := by
  have hMem := restrict_posPart_sub_mem_collar_zero_of_innerBand a aPrime b ha haa hab u v hu hv hBand
  have hSub : TauCeti.W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) (u-v) =
      TauCeti.W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) u -
        TauCeti.W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) v := map_sub _ u v
  have hEq := (restrictL_posPart (radiusTwoCollarOpens_le_radiusTwoOpens a) (u-v)).trans
    (congrArg (TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞)) hSub)
  exact hEq ▸ hMem

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.restrict_posPart_sub_mem_collar_zero_of_innerBand
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.posPart_restrict_sub_mem_collar_zero_of_innerBand
