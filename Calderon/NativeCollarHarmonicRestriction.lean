import Calderon.RadiusTwoEuclideanCollar
import Calderon.NativeNestedExtendedZeroEnergyDiagnostic

/-! EXPANSION.json precedes derived harmonicity on a smaller actual collar. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open TauCeti TauCeti.PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

lemma memLp_identityEnergyIntegrand (Omega : Opens R3) :
    MemLp (fun _ : R3 => energyIntegrand (1 : Matrix (Fin 3) (Fin 3) ℝ)
      (0 : R3) (0 : ℝ)) ⊤ ((volume : Measure R3).restrict Omega) := by
  have hUE := uniformlyEllipticOn_const_one_one (n := Fin 3) (Omega : Set R3)
  exact memLp_energyIntegrand_of_bounds (by norm_num : (0 : ℝ) ≤ 1)
    aestronglyMeasurable_const aestronglyMeasurable_const aestronglyMeasurable_const
    (fun x hx eta xi => hUE.upper_bound hx eta xi)
    (beta := 0) (gamma := 0) (fun _ _ => by simp) (fun _ _ => by simp)

lemma radiusTwoCollarOpens_antitone {a0 a : ℝ} (ha : a0 ≤ a) :
    radiusTwoCollarOpens a ≤ radiusTwoCollarOpens a0 := by
  intro x hx
  exact ⟨ha.trans_lt hx.1,hx.2⟩

lemma native_collar_harmonic_restrict (u : RadiusTwoH1) (a0 a : ℝ) (ha : a0 ≤ a)
    (hWeak : ∀ v : W1p0 (volume : Measure R3) (radiusTwoCollarOpens a0) 2,
      energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (0 : R3 → R3) (0 : R3 → ℝ)
        (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a0) u)
        (v : W1p (volume : Measure R3) (radiusTwoCollarOpens a0) 2) = 0)
    (v : W1p0 (volume : Measure R3) (radiusTwoCollarOpens a) 2) :
    energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a) u)
      (v : W1p (volume : Measure R3) (radiusTwoCollarOpens a) 2) = 0 := by
  have hSub := radiusTwoCollarOpens_antitone ha
  have hEnergy := EnergyBridge.NativeNestedDomain.energyFormH1_extendedZeroTest_eq_restriction
    (radiusTwoCollarOpens a) (radiusTwoCollarOpens a0) hSub
    (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
    (memLp_identityEnergyIntegrand (radiusTwoCollarOpens a0))
    (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a0) u) v
  have hZero := hEnergy.symm.trans (hWeak (W1p0.extendByZeroL hSub v))
  have hRestr := W1p.restrictL_restrictL (radiusTwoCollarOpens_le_radiusTwoOpens a0) hSub u
  have hTransport := congrArg
    (fun z : W1p (volume : Measure R3) (radiusTwoCollarOpens a) 2 =>
      energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (0 : R3 → R3) (0 : R3 → ℝ) z
        (v : W1p (volume : Measure R3) (radiusTwoCollarOpens a) 2)) hRestr
  exact hTransport.symm.trans hZero

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.memLp_identityEnergyIntegrand
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoCollarOpens_antitone
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.native_collar_harmonic_restrict
