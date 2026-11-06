import Calderon.RadiusTwoNativeSourceFoundation

/-! EXPANSION.json precedes completion in the genuine closed native zero submodule. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoNativeZero_sequence_limit
    (u : ℕ → RadiusTwoH1) (hCauchy : CauchySeq u)
    (hMem : ∀ n : ℕ, u n ∈ TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2) :
    ∃ w : RadiusTwoH1Zero, Tendsto u atTop (𝓝 (w : RadiusTwoH1)) := by
  obtain ⟨w,hw⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hw0 : w ∈ TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2 :=
    (TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2).isClosed.mem_of_tendsto
      hw (Eventually.of_forall hMem)
  exact ⟨⟨w,hw0⟩,hw⟩

end OAI.AnisotropicCalderon.ExteriorSource
