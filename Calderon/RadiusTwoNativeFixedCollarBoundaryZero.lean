import Calderon.RadiusTwoNativeCollarTwoSidedBound
import Calderon.RadiusTwoCollarScalarBarrierData

/-! EXPANSION.json precedes the final fixed-native-collar bound and boundary-zero extension. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open TauCeti TauCeti.PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

lemma exists_native_fixed_collar_barrier_and_boundary_zero
    (u : RadiusTwoH1Zero) (U : R3 → ℝ) (a0 : ℝ) (ha0 : 1 ≤ a0) (ha02 : a0 < 2)
    (hWeak : ∀ v : W1p0 (volume : Measure R3) (radiusTwoCollarOpens a0) 2,
      energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (0 : R3 → R3) (0 : R3 → ℝ)
        (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a0) (u : RadiusTwoH1))
        (v : W1p (volume : Measure R3) (radiusTwoCollarOpens a0) 2) = 0)
    (hCont : ContinuousOn U (radiusTwoCollarOpens a0 : Set R3))
    (hU : ∀ᵐ x ∂(volume : Measure R3).restrict (radiusTwoCollarOpens a0),
      W1p.value (u : RadiusTwoH1) x = U x) :
    ∃ a M : ℝ, a0 < a ∧ a < 2 ∧ 0 ≤ M ∧
      (∀ x ∈ radiusTwoCollarOpens a, |U x| ≤ M*(4-‖x‖^2)) ∧
      (∀ y : R3, ‖y‖ = 2 →
        (if ‖y‖ < 2 then U y else 0) = 0 ∧
        ContinuousAt (fun x : R3 => if ‖x‖ < 2 then U x else 0) y) := by
  let a : ℝ := (a0+2)/2
  let aPrime : ℝ := (a+2)/2
  let b : ℝ := (aPrime+2)/2
  have h0a : a0 < a := by dsimp only [a]; linarith
  have ha2 : a < 2 := by dsimp only [a]; linarith
  have ha : 0 < a := by linarith
  have haa : a < aPrime := by dsimp only [aPrime]; linarith
  have haPrime2 : aPrime < 2 := by dsimp only [aPrime]; linarith
  have hab : aPrime < b := by dsimp only [b]; linarith
  have hb2 : b < 2 := by dsimp only [b]; linarith
  have hb0 : 0 ≤ b := by linarith
  obtain ⟨M,hM,hBand⟩ := exists_radialBarrier_bound_on_compact_innerBand U a0 a b h0a hb0 hb2 hCont
  have hSub := radiusTwoCollarOpens_antitone h0a.le
  have hMu : (volume : Measure R3).restrict (radiusTwoCollarOpens a) ≤
      (volume : Measure R3).restrict (radiusTwoCollarOpens a0) :=
    Measure.restrict_mono_set volume (SetLike.coe_subset_coe.mpr hSub)
  have hUSmall := hU.filter_mono (ae_mono hMu)
  have hWeakSmall := native_collar_harmonic_restrict (u : RadiusTwoH1) a0 a h0a.le hWeak
  have hAbs := native_harmonic_collar_abs_le_barrier_of_innerBand
    a aPrime b M ha haa hab hM u U hWeakSmall hUSmall hBand
  have hContSmall : ContinuousOn U (radiusTwoCollarOpens a : Set R3) :=
    hCont.mono (SetLike.coe_subset_coe.mpr hSub)
  have hPoly : Continuous (fun x : R3 => M*(4-‖x‖^2)) :=
    continuous_const.mul (continuous_const.sub (continuous_norm.pow 2))
  have hPoint : ∀ x ∈ radiusTwoCollarOpens a, |U x| ≤ M*(4-‖x‖^2) :=
    leOn_open_of_ae_le_of_continuousOn (radiusTwoCollarOpens a)
      (fun x : R3 => |U x|) (fun x : R3 => M*(4-‖x‖^2)) hContSmall.abs hPoly.continuousOn hAbs
  refine ⟨a,M,h0a,ha2,hM,hPoint,?_⟩
  intro y hy
  refine ⟨?_,continuousAt_zeroExtension_of_radialBarrier U a M ha2 hM hPoint y hy⟩
  simp only [hy,lt_self_iff_false,if_false]

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.exists_native_fixed_collar_barrier_and_boundary_zero
