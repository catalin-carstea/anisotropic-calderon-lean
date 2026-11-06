import Calderon.RadiusTwoNativeCollarBarrierComparison
import Calderon.NativeCollarHarmonicNegation

/-! EXPANSION.json precedes actual two-sided AE comparison; band data are later derived from continuity. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open TauCeti TauCeti.PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

lemma native_harmonic_collar_abs_le_barrier_of_innerBand
    (a aPrime b M : ℝ) (ha : 0 < a) (haa : a < aPrime) (hab : aPrime < b) (hM : 0 ≤ M)
    (u : RadiusTwoH1Zero) (U : R3 → ℝ)
    (hWeak : ∀ v : W1p0 (volume : Measure R3) (radiusTwoCollarOpens a) 2,
      energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (0 : R3 → R3) (0 : R3 → ℝ)
        (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) (u : RadiusTwoH1))
        (v : W1p (volume : Measure R3) (radiusTwoCollarOpens a) 2) = 0)
    (hU : ∀ᵐ x ∂(volume : Measure R3).restrict (radiusTwoCollarOpens a),
      W1p.value (u : RadiusTwoH1) x = U x)
    (hBand : ∀ x : R3, a ≤ ‖x‖ → ‖x‖ ≤ b → |U x| ≤ M*(4-‖x‖^2)) :
    ∀ᵐ x ∂(volume : Measure R3).restrict (radiusTwoCollarOpens a),
      |U x| ≤ M*(4-‖x‖^2) := by
  have hMu : (volume : Measure R3).restrict (radiusTwoCollarOpens a) ≤
      (volume : Measure R3).restrict radiusTwoOpens :=
    Measure.restrict_mono_set volume
      (SetLike.coe_subset_coe.mpr (radiusTwoCollarOpens_le_radiusTwoOpens a))
  have hBarrier := (radiusTwoBarrierH1_value_ae M).filter_mono (ae_mono hMu)
  have hPosBand : ∀ᵐ x ∂(volume : Measure R3).restrict (radiusTwoCollarOpens a),
      ‖x‖ < b → W1p.value (u : RadiusTwoH1) x ≤ W1p.value (radiusTwoBarrierH1 M) x := by
    filter_upwards [hU,hBarrier,ae_restrict_mem (radiusTwoCollarOpens a).isOpen.measurableSet]
      with x hUx hVx hx
    intro hxb
    rw [hUx,hVx]
    exact (le_abs_self (U x)).trans (hBand x hx.1.le hxb.le)
  have hNegLp : W1p.value ((-u : RadiusTwoH1Zero) : RadiusTwoH1) =
      -W1p.value (u : RadiusTwoH1) := by
    change W1p.value (-(u : RadiusTwoH1)) = _
    simp only [← W1p.valueL_apply,map_neg]
  have hNegU : ∀ᵐ x ∂(volume : Measure R3).restrict (radiusTwoCollarOpens a),
      W1p.value ((-u : RadiusTwoH1Zero) : RadiusTwoH1) x = -U x := by
    rw [hNegLp]
    filter_upwards [hU,(Lp.coeFn_neg (W1p.value (u : RadiusTwoH1))).filter_mono (ae_mono hMu)]
      with x hUx hNx
    rw [hNx,Pi.neg_apply,hUx]
  have hNegWeak : ∀ v : W1p0 (volume : Measure R3) (radiusTwoCollarOpens a) 2,
      energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (0 : R3 → R3) (0 : R3 → ℝ)
        (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) ((-u : RadiusTwoH1Zero) : RadiusTwoH1))
        (v : W1p (volume : Measure R3) (radiusTwoCollarOpens a) 2) = 0 :=
    native_collar_harmonic_neg a u hWeak
  have hNegBand : ∀ᵐ x ∂(volume : Measure R3).restrict (radiusTwoCollarOpens a),
      ‖x‖ < b → W1p.value ((-u : RadiusTwoH1Zero) : RadiusTwoH1) x ≤
        W1p.value (radiusTwoBarrierH1 M) x := by
    filter_upwards [hNegU,hBarrier,ae_restrict_mem (radiusTwoCollarOpens a).isOpen.measurableSet]
      with x hNx hVx hx
    intro hxb
    rw [hNx,hVx]
    exact (neg_le_abs (U x)).trans (hBand x hx.1.le hxb.le)
  have hPos := native_harmonic_collar_le_barrier_of_innerBand a aPrime b M ha haa hab hM u hWeak hPosBand
  have hNeg := native_harmonic_collar_le_barrier_of_innerBand a aPrime b M ha haa hab hM (-u) hNegWeak hNegBand
  filter_upwards [hPos,hNeg,hU,hNegU,hBarrier,
    W1p.value_restrictL_ae (radiusTwoCollarOpens_le_radiusTwoOpens a) (u : RadiusTwoH1),
    W1p.value_restrictL_ae (radiusTwoCollarOpens_le_radiusTwoOpens a) ((-u : RadiusTwoH1Zero) : RadiusTwoH1),
    W1p.value_restrictL_ae (radiusTwoCollarOpens_le_radiusTwoOpens a) (radiusTwoBarrierH1 M)]
    with x hPx hNx hUx hNegx hVx hRu hRN hRV
  rw [hRu,hUx,hRV,hVx] at hPx
  rw [hRN,hNegx,hRV,hVx] at hNx
  exact abs_le.mpr ⟨by linarith,hPx⟩

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.native_harmonic_collar_abs_le_barrier_of_innerBand
