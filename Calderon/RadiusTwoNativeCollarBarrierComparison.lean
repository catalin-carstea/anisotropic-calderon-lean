import Calderon.NativeCollarPositiveDifferenceZero
import Calderon.RadiusTwoNativeBarrierNonnegativity
import Calderon.RadiusTwoNativeBarrierZeroTestEquation
import Calderon.NativeCollarHarmonicRestriction
import Calderon.NativeBallTwoLaplacianLowerBound
import Calderon.NativeWeakComparison

/-! EXPANSION.json precedes the actual native one-sided fixed-collar comparison. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open TauCeti TauCeti.PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

lemma native_harmonic_collar_le_barrier_of_innerBand
    (a aPrime b M : ℝ) (ha : 0 < a) (haa : a < aPrime) (hab : aPrime < b) (hM : 0 ≤ M)
    (u : RadiusTwoH1Zero)
    (hWeak : ∀ v : W1p0 (volume : Measure R3) (radiusTwoCollarOpens a) 2,
      energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (0 : R3 → R3) (0 : R3 → ℝ)
        (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) (u : RadiusTwoH1))
        (v : W1p (volume : Measure R3) (radiusTwoCollarOpens a) 2) = 0)
    (hBand : ∀ᵐ x ∂(volume : Measure R3).restrict (radiusTwoCollarOpens a),
      ‖x‖ < b → W1p.value (u : RadiusTwoH1) x ≤ W1p.value (radiusTwoBarrierH1 M) x) :
    ∀ᵐ x ∂(volume : Measure R3).restrict (radiusTwoCollarOpens a),
      W1p.value (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) (u : RadiusTwoH1)) x ≤
      W1p.value (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) (radiusTwoBarrierH1 M)) x := by
  have hBoundary := posPart_restrict_sub_mem_collar_zero_of_innerBand
    a aPrime b ha haa hab (u : RadiusTwoH1) (radiusTwoBarrierH1 M) u.2
    (radiusTwoBarrierH1_value_nonneg_ae M hM) hBand
  have hSubset : (radiusTwoCollarOpens a : Set R3) ⊆ ball (0 : R3) 2 := by
    intro x hx
    exact mem_ball_zero_iff.mpr hx.2
  have hLower := native_laplacian_lower_bound_of_subset_ball_two (radiusTwoCollarOpens a) hSubset
  refine value_le_of_energyFormH1_le
    (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ))
    (memLp_identityEnergyIntegrand (radiusTwoCollarOpens a))
    hBoundary (by norm_num : (0 : ℝ) < 1/34) hLower ?_
  intro v hv
  exact (hWeak v).le.trans (radiusTwoBarrier_energy_nonneg_on_collar a M hM v hv)

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.native_harmonic_collar_le_barrier_of_innerBand
