import TauCeti.Analysis.Sobolev.W1p.ChainRule

/-! EXPANSION.json precedes the two actual native value-algebra leaves. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E}

lemma native_sub_value_ae (u v : TauCeti.W1p mu Omega 2) :
    ∀ᵐ x ∂mu.restrict Omega, TauCeti.W1p.value (u-v) x =
      TauCeti.W1p.value u x-TauCeti.W1p.value v x := by
  have hSub : TauCeti.W1p.value (u-v) = TauCeti.W1p.value u-TauCeti.W1p.value v := by
    simp only [← TauCeti.W1p.valueL_apply,map_sub]
  rw [hSub]
  filter_upwards [Lp.coeFn_sub (TauCeti.W1p.value u) (TauCeti.W1p.value v)] with x hx
  exact hx

lemma native_posPart_sub_value_ae (u v : TauCeti.W1p mu Omega 2) :
    ∀ᵐ x ∂mu.restrict Omega, TauCeti.W1p.value
      (TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (u-v)) x =
        max (TauCeti.W1p.value u x-TauCeti.W1p.value v x) 0 := by
  have hPos : ∀ᵐ x ∂mu.restrict Omega, TauCeti.W1p.value
      (TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (u-v)) x =
        max (TauCeti.W1p.value (u-v) x) 0 := by
    rw [TauCeti.W1p.value_posPart]
    exact Lp.coeFn_posPart _
  filter_upwards [native_sub_value_ae u v,hPos] with x hSub hP
  rw [hP,hSub]

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.native_sub_value_ae
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.native_posPart_sub_value_ae
