import OAI.Analysis.AnisotropicCalderon.Defs

namespace OAI.AnisotropicCalderon.EnergyBridge

/-- The exact infimum mechanism for a continuous functional on a closure.
Its boundedness and continuity hypotheses must be supplied in any analytic application. -/
theorem sInf_image_closure_eq {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : s.Nonempty) {F : X → ℝ} (hF : Continuous F)
    (hbelow : BddBelow (F '' closure s)) :
    sInf (F '' closure s) = sInf (F '' s) := by
  have hsub : F '' s ⊆ F '' closure s := Set.image_mono subset_closure
  have hsmall : BddBelow (F '' s) := hbelow.mono hsub
  apply le_antisymm
  · exact csInf_le_csInf hbelow (hs.image F) hsub
  · apply le_csInf ((hs.mono subset_closure).image F)
    have hclosed : IsClosed {x | sInf (F '' s) ≤ F x} :=
      isClosed_le continuous_const hF
    have hcontain : s ⊆ {x | sInf (F '' s) ≤ F x} := by
      intro x hx
      exact csInf_le hsmall ⟨x, hx, rfl⟩
    rintro y ⟨x, hx, rfl⟩
    exact closure_minimal hcontain hclosed hx

end OAI.AnisotropicCalderon.EnergyBridge

#print axioms OAI.AnisotropicCalderon.EnergyBridge.sInf_image_closure_eq
