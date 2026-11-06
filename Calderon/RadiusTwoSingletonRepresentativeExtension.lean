import Calderon.RadiusTwoNativeSourceFoundation
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace OAI.AnisotropicCalderon.ExteriorSource

theorem radiusTwo_ae_eq_of_ae_eq_off_singleton
    (p : R3) (F G : R3 → ℝ)
    (hFG : F =ᵐ[(volume : Measure R3).restrict
      ((radiusTwoOpens : Set R3) \ {p})] G) :
    F =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] G := by
  have hNe : ∀ᵐ z ∂(volume : Measure R3), z ≠ p := Measure.ae_ne volume p
  have hSets : ((radiusTwoOpens : Set R3) \ {p}) =ᵐ[(volume : Measure R3)]
      (radiusTwoOpens : Set R3) := by
    filter_upwards [hNe] with z hz
    change (z ∈ (radiusTwoOpens : Set R3) ∧ z ∉ ({p} : Set R3)) =
      (z ∈ (radiusTwoOpens : Set R3))
    simp only [Set.mem_singleton_iff,hz,not_false_eq_true,and_true]
  have hMeasure := Measure.restrict_congr_set hSets
  rw [hMeasure] at hFG
  exact hFG

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwo_ae_eq_of_ae_eq_off_singleton
