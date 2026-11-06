import Calderon.NativeCollarHarmonicRestriction

/-! EXPANSION.json precedes the derived actual negative weak-equation leaf. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open TauCeti TauCeti.PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

lemma native_collar_harmonic_neg (a : ℝ) (u : RadiusTwoH1Zero)
    (hWeak : ∀ v : W1p0 (volume : Measure R3) (radiusTwoCollarOpens a) 2,
      energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (0 : R3 → R3) (0 : R3 → ℝ)
        (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) (u : RadiusTwoH1))
        (v : W1p (volume : Measure R3) (radiusTwoCollarOpens a) 2) = 0)
    (v : W1p0 (volume : Measure R3) (radiusTwoCollarOpens a) 2) :
    energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) ((-u : RadiusTwoH1Zero) : RadiusTwoH1))
      (v : W1p (volume : Measure R3) (radiusTwoCollarOpens a) 2) = 0 := by
  have hRestr : W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a)
      ((-u : RadiusTwoH1Zero) : RadiusTwoH1) =
      -(W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) (u : RadiusTwoH1)) :=
    map_neg _ (u : RadiusTwoH1)
  rw [hRestr,← energyFormH1L_apply (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ))
    (memLp_identityEnergyIntegrand (radiusTwoCollarOpens a)),
    map_neg,neg_apply,energyFormH1L_apply,hWeak v,neg_zero]

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.native_collar_harmonic_neg
