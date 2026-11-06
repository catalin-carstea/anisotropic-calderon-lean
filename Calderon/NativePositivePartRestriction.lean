import TauCeti.Analysis.Sobolev.W1p.ChainRule
import TauCeti.Analysis.Sobolev.W1p.Restriction

/-! EXPANSION.json precedes actual positive-part restriction compatibility. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E}

lemma restrictL_posPart (hU : U ≤ Omega) (u : TauCeti.W1p mu Omega 2) :
    TauCeti.W1p.restrictL hU (TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) u) =
      TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (TauCeti.W1p.restrictL hU u) := by
  let hp : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hOuter : ∀ᵐ x ∂mu.restrict Omega,
      TauCeti.W1p.value (TauCeti.W1p.posPart hp u) x = max (TauCeti.W1p.value u x) 0 := by
    rw [TauCeti.W1p.value_posPart]
    exact Lp.coeFn_posPart _
  have hInner : ∀ᵐ x ∂mu.restrict U,
      TauCeti.W1p.value (TauCeti.W1p.posPart hp (TauCeti.W1p.restrictL hU u)) x =
        max (TauCeti.W1p.value (TauCeti.W1p.restrictL hU u) x) 0 := by
    rw [TauCeti.W1p.value_posPart]
    exact Lp.coeFn_posPart _
  apply TauCeti.W1p.ext_value
  apply Lp.ext
  have hMu : mu.restrict U ≤ mu.restrict Omega :=
    Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)
  filter_upwards [TauCeti.W1p.value_restrictL_ae hU (TauCeti.W1p.posPart hp u),
    TauCeti.W1p.value_restrictL_ae hU u,hOuter.filter_mono (ae_mono hMu),hInner]
    with x hPosRestr hRestr hOut hIn
  rw [hPosRestr,hOut,hIn,hRestr]

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.restrictL_posPart
