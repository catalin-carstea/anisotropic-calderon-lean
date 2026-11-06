import Calderon.NativeNestedMetricEnergyLocalization

/-! EXPANSION.json precedes this genuine restricted zero-test energy identity. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma energyFormH1_restrictedZeroTest_eq_setIntegral (Omega OmegaOuter : Opens R3)
    (hsub : Omega ≤ OmegaOuter) (A : MatrixField)
    (U : TauCeti.W1p (volume : Measure R3) OmegaOuter 2)
    (z : TauCeti.W1p0 (volume : Measure R3) Omega 2) :
    TauCeti.PDE.energyFormH1 A 0 0 (TauCeti.W1p.restrictL hsub U)
      (z : TauCeti.W1p (volume : Measure R3) Omega 2) =
    ∫ x in Omega, TauCeti.PDE.energyIntegrand (A x) 0 0
      (TauCeti.PDE.jetField U x)
      (TauCeti.PDE.jetField (TauCeti.W1p0.extendByZeroL hsub z :
        TauCeti.W1p (volume : Measure R3) OmegaOuter 2) x) ∂(volume : Measure R3) := by
  have hRecoveredEnergy :
      TauCeti.PDE.energyFormH1 A 0 0 (TauCeti.W1p.restrictL hsub U)
        (TauCeti.W1p.restrictL hsub (TauCeti.W1p0.extendByZeroL hsub z :
          TauCeti.W1p (volume : Measure R3) OmegaOuter 2)) =
      TauCeti.PDE.energyFormH1 A 0 0 (TauCeti.W1p.restrictL hsub U)
        (z : TauCeti.W1p (volume : Measure R3) Omega 2) :=
    congrArg (fun t : TauCeti.W1p (volume : Measure R3) Omega 2 =>
      TauCeti.PDE.energyFormH1 A 0 0 (TauCeti.W1p.restrictL hsub U) t)
      (restrictL_extendByZeroL Omega OmegaOuter hsub z)
  exact hRecoveredEnergy.symm.trans
    (energyFormH1_restrict_eq_setIntegral Omega OmegaOuter hsub A U
      (TauCeti.W1p0.extendByZeroL hsub z : TauCeti.W1p (volume : Measure R3) OmegaOuter 2))

end OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain
#print axioms OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain.energyFormH1_restrictedZeroTest_eq_setIntegral
