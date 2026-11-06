import Calderon.TauBoundaryEnergyData
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.Sobolev.W1p.Restriction

/-! EXPANSION.json precedes this actual nested-domain replacement construction. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma restrictL_extendByZeroL (Omega OmegaOuter : Opens R3) (hsub : Omega ≤ OmegaOuter)
    (z : TauCeti.W1p0 (volume : Measure R3) Omega 2) :
    TauCeti.W1p.restrictL hsub
      (TauCeti.W1p0.extendByZeroL hsub z : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) =
      (z : TauCeti.W1p (volume : Measure R3) Omega 2) := by
  apply TauCeti.W1p.ext_value
  apply Lp.ext
  have hRestr := TauCeti.W1p.value_restrictL_ae hsub
    (TauCeti.W1p0.extendByZeroL hsub z : TauCeti.W1p (volume : Measure R3) OmegaOuter 2)
  have hExt : TauCeti.W1p.value
      (TauCeti.W1p0.extendByZeroL hsub z : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) =ᵐ[
        (volume : Measure R3).restrict Omega]
      TauCeti.W1p.value (z : TauCeti.W1p (volume : Measure R3) Omega 2) := by
    rw [TauCeti.W1p0.value_extendByZeroL]
    exact TauCeti.coeFn_extendByZeroLpₗᵢ_restrict ℝ Omega.isOpen.measurableSet
      (SetLike.coe_subset_coe.mpr hsub) _
  exact hRestr.trans hExt

def nativeZeroBoundaryReplacement (Omega OmegaOuter : Opens R3) (hsub : Omega ≤ OmegaOuter)
    (W : TauCeti.W1p0 (volume : Measure R3) OmegaOuter 2)
    (z : TauCeti.W1p0 (volume : Measure R3) Omega 2) :
    TauCeti.W1p0 (volume : Measure R3) OmegaOuter 2 :=
  W + TauCeti.W1p0.extendByZeroL hsub z

lemma nativeZeroBoundaryReplacement_restrict (Omega OmegaOuter : Opens R3)
    (hsub : Omega ≤ OmegaOuter)
    (W : TauCeti.W1p0 (volume : Measure R3) OmegaOuter 2)
    (z : TauCeti.W1p0 (volume : Measure R3) Omega 2) :
    TauCeti.W1p.restrictL hsub
      (nativeZeroBoundaryReplacement Omega OmegaOuter hsub W z :
        TauCeti.W1p (volume : Measure R3) OmegaOuter 2) =
      TauCeti.W1p.restrictL hsub (W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) +
        (z : TauCeti.W1p (volume : Measure R3) Omega 2) := by
  change TauCeti.W1p.restrictL hsub
    ((W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) +
      (TauCeti.W1p0.extendByZeroL hsub z : TauCeti.W1p (volume : Measure R3) OmegaOuter 2)) = _
  exact (map_add (TauCeti.W1p.restrictL hsub) _ _).trans
    (congrArg (fun v : TauCeti.W1p (volume : Measure R3) Omega 2 =>
      TauCeti.W1p.restrictL hsub (W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) + v)
      (restrictL_extendByZeroL Omega OmegaOuter hsub z))

lemma nativeZeroBoundaryReplacement_value_eq_outside (Omega OmegaOuter : Opens R3)
    (hsub : Omega ≤ OmegaOuter)
    (W : TauCeti.W1p0 (volume : Measure R3) OmegaOuter 2)
    (z : TauCeti.W1p0 (volume : Measure R3) Omega 2) :
    ∀ᵐ x ∂(volume : Measure R3).restrict OmegaOuter, x ∉ (Omega : Set R3) →
      TauCeti.W1p.value (nativeZeroBoundaryReplacement Omega OmegaOuter hsub W z :
        TauCeti.W1p (volume : Measure R3) OmegaOuter 2) x =
      TauCeti.W1p.value (W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) x := by
  let E : TauCeti.W1p (volume : Measure R3) OmegaOuter 2 := TauCeti.W1p0.extendByZeroL hsub z
  have hExt : TauCeti.W1p.value E =ᵐ[(volume : Measure R3).restrict OmegaOuter]
      (Omega : Set R3).indicator
        (TauCeti.W1p.value (z : TauCeti.W1p (volume : Measure R3) Omega 2) : R3 → ℝ) := by
    dsimp only [E]
    rw [TauCeti.W1p0.value_extendByZeroL]
    exact TauCeti.coeFn_extendByZeroLpₗᵢ ℝ Omega.isOpen.measurableSet
      (SetLike.coe_subset_coe.mpr hsub) _
  have hAdd : TauCeti.W1p.value
      (nativeZeroBoundaryReplacement Omega OmegaOuter hsub W z :
        TauCeti.W1p (volume : Measure R3) OmegaOuter 2) =
      TauCeti.W1p.value (W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) +
        TauCeti.W1p.value E :=
    map_add TauCeti.W1p.valueL (W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) E
  rw [hAdd]
  filter_upwards [Lp.coeFn_add
    (TauCeti.W1p.value (W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2))
    (TauCeti.W1p.value E), hExt] with x hx hEx hxOut
  rw [hx,Pi.add_apply,hEx,Set.indicator_of_notMem hxOut,add_zero]

lemma nativeZeroBoundaryReplacement_gradient_eq_outside (Omega OmegaOuter : Opens R3)
    (hsub : Omega ≤ OmegaOuter)
    (W : TauCeti.W1p0 (volume : Measure R3) OmegaOuter 2)
    (z : TauCeti.W1p0 (volume : Measure R3) Omega 2) :
    ∀ᵐ x ∂(volume : Measure R3).restrict OmegaOuter, x ∉ (Omega : Set R3) →
      TauCeti.W1p.gradient (nativeZeroBoundaryReplacement Omega OmegaOuter hsub W z :
        TauCeti.W1p (volume : Measure R3) OmegaOuter 2) x =
      TauCeti.W1p.gradient (W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) x := by
  let E : TauCeti.W1p (volume : Measure R3) OmegaOuter 2 := TauCeti.W1p0.extendByZeroL hsub z
  have hExt : TauCeti.W1p.gradient E =ᵐ[(volume : Measure R3).restrict OmegaOuter]
      (Omega : Set R3).indicator
        (TauCeti.W1p.gradient (z : TauCeti.W1p (volume : Measure R3) Omega 2) : R3 → R3) := by
    dsimp only [E]
    rw [TauCeti.W1p0.gradient_extendByZeroL]
    exact TauCeti.coeFn_extendByZeroLpₗᵢ ℝ Omega.isOpen.measurableSet
      (SetLike.coe_subset_coe.mpr hsub) _
  have hAdd : TauCeti.W1p.gradient
      (nativeZeroBoundaryReplacement Omega OmegaOuter hsub W z :
        TauCeti.W1p (volume : Measure R3) OmegaOuter 2) =
      TauCeti.W1p.gradient (W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) +
        TauCeti.W1p.gradient E :=
    map_add TauCeti.W1p.gradientL (W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) E
  rw [hAdd]
  filter_upwards [Lp.coeFn_add
    (TauCeti.W1p.gradient (W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2))
    (TauCeti.W1p.gradient E), hExt] with x hx hEx hxOut
  rw [hx,Pi.add_apply,hEx,Set.indicator_of_notMem hxOut,add_zero]

end OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain
#print axioms OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain.restrictL_extendByZeroL
#print axioms OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain.nativeZeroBoundaryReplacement
#print axioms OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain.nativeZeroBoundaryReplacement_restrict
#print axioms OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain.nativeZeroBoundaryReplacement_value_eq_outside
#print axioms OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain.nativeZeroBoundaryReplacement_gradient_eq_outside
