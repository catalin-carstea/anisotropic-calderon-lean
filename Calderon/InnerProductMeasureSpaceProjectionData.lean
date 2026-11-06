import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! Only inherited measurable-space data and proof-coherent volume projections. -/
set_option autoImplicit false
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

universe u
variable {E : Type u} [g : NormedAddCommGroup E] [i : InnerProductSpace ℝ E]
  [m : MeasurableSpace E]

lemma measureSpaceOfInnerProductSpace_toMeasurableSpace_eq
    (hfd : FiniteDimensional ℝ E) (hb : BorelSpace E) :
    @MeasureTheory.MeasureSpace.toMeasurableSpace E
      (@measureSpaceOfInnerProductSpace E g i hfd m hb) = m := by
  rfl

lemma measureSpaceOfInnerProductSpace_volume_eq
    (hfd₁ hfd₂ : FiniteDimensional ℝ E) (hb₁ hb₂ : BorelSpace E) :
    @MeasureTheory.MeasureSpace.volume E
      (@measureSpaceOfInnerProductSpace E g i hfd₁ m hb₁) =
    @MeasureTheory.MeasureSpace.volume E
      (@measureSpaceOfInnerProductSpace E g i hfd₂ m hb₂) := by
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.measureSpaceOfInnerProductSpace_toMeasurableSpace_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.measureSpaceOfInnerProductSpace_volume_eq
