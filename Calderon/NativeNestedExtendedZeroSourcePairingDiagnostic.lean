import Calderon.NativeNestedMetricEnergyLocalization

/-! EXPANSION.json precedes this exact focused source restriction diagnostic. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma extendedZeroTest_source_pairing_zero (Omega OmegaOuter : Opens R3)
    (hsub : Omega ≤ OmegaOuter) (z : TauCeti.W1p0 (volume : Measure R3) Omega 2)
    (F : R3 → ℝ)
    (hZero : ∀ᵐ x ∂(volume : Measure R3).restrict OmegaOuter,
      x ∈ (Omega : Set R3) → F x = 0) :
    (∫ x in OmegaOuter, F x * TauCeti.W1p.value
      (TauCeti.W1p0.extendByZeroL hsub z : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) x
      ∂(volume : Measure R3)) = 0 := by
  have hValue : TauCeti.W1p.value
      (TauCeti.W1p0.extendByZeroL hsub z : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) =ᵐ[
      (volume : Measure R3).restrict OmegaOuter] (Omega : Set R3).indicator
      (TauCeti.W1p.value (z : TauCeti.W1p (volume : Measure R3) Omega 2) : R3 → ℝ) := by
    rw [TauCeti.W1p0.value_extendByZeroL]
    exact TauCeti.coeFn_extendByZeroLpₗᵢ ℝ Omega.isOpen.measurableSet
      (SetLike.coe_subset_coe.mpr hsub) _
  have hAE : (fun x => F x * TauCeti.W1p.value
      (TauCeti.W1p0.extendByZeroL hsub z : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) x) =ᵐ[
      (volume : Measure R3).restrict OmegaOuter] fun _ => 0 := by
    filter_upwards [hValue,hZero] with x hv hF
    by_cases hx : x ∈ (Omega : Set R3)
    · rw [hF hx,zero_mul]
    · rw [hv,Set.indicator_of_notMem hx,mul_zero]
  simpa only [integral_zero] using integral_congr_ae hAE

end OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain
#print axioms OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain.extendedZeroTest_source_pairing_zero
