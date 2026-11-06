import Calderon.NativeNestedExtendedZeroEnergyDiagnostic
import Calderon.NativeNestedExtendedZeroSourcePairingDiagnostic

/-! EXPANSION.json precedes this exact focused source restriction diagnostic. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma source_restriction_weak_harmonic (Omega OmegaOuter : Opens R3)
    (hsub : Omega ≤ OmegaOuter) (A : MatrixField)
    (hc : MemLp (fun x => TauCeti.PDE.energyIntegrand (A x) 0 0) ⊤
      ((volume : Measure R3).restrict OmegaOuter))
    (U : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) (F : R3 → ℝ)
    (hZero : ∀ᵐ x ∂(volume : Measure R3).restrict OmegaOuter,
      x ∈ (Omega : Set R3) → F x = 0)
    (hSolve : ∀ v : TauCeti.W1p0 (volume : Measure R3) OmegaOuter 2,
      TauCeti.PDE.energyFormH1 A 0 0 U (v : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) =
      ∫ x in OmegaOuter, F x * TauCeti.W1p.value
        (v : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) x ∂(volume : Measure R3))
    (z : TauCeti.W1p0 (volume : Measure R3) Omega 2) :
    TauCeti.PDE.energyFormH1 A 0 0 (TauCeti.W1p.restrictL hsub U)
      (z : TauCeti.W1p (volume : Measure R3) Omega 2) = 0 := by
  exact (energyFormH1_extendedZeroTest_eq_restriction Omega OmegaOuter hsub A hc U z).symm.trans
    ((hSolve (TauCeti.W1p0.extendByZeroL hsub z)).trans
      (extendedZeroTest_source_pairing_zero Omega OmegaOuter hsub z F hZero))
end OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain
#print axioms OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain.source_restriction_weak_harmonic
