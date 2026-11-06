import Calderon.RadiusTwoCommonDeltaCutoffAnnihilation

/-! Full EXPANSION.json precedes this literal cutoff annihilation consequence. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace OAI.AnisotropicCalderon.ExteriorSource

theorem radiusTwo_cutoff_annihilation_of_one_on_tsupport
    (η χ : R3 → ℝ) (hOne : ∀ x ∈ tsupport η, χ x = 1)
    (ρ : ℕ → RadiusTwoL2)
    (hAnn : ∀ᶠ n in atTop, ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
      χ x * ρ n x = 0) :
    ∀ᶠ n in atTop, ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
      η x * ρ n x = 0 := by
  filter_upwards [hAnn] with n hn
  filter_upwards [hn] with x hx
  by_cases hη : η x = 0
  · rw [hη,zero_mul]
  · have hχ : χ x = 1 := hOne x (subset_tsupport η hη)
    rw [hχ,one_mul] at hx
    rw [hx,mul_zero]

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwo_cutoff_annihilation_of_one_on_tsupport
