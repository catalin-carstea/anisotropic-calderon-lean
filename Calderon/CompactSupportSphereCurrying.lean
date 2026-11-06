import Calderon.BoundedParameterSmoothness
import Calderon.NativeValueRadialTrace

set_option autoImplicit false
noncomputable section
open Set Function
open scoped ContDiff Topology BoundedContinuousFunction
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume SphereHarmonic

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def boundedSphereRestrictionL : (R3 →ᵇ V) →L[ℝ] C(UnitSphere,V) := by
  let T : (R3 →ᵇ V) →ₗ[ℝ] C(UnitSphere,V) :=
    { toFun := fun f => ⟨fun x => f x.val,f.continuous.comp continuous_subtype_val⟩
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  apply T.mkContinuous 1
  intro f
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  exact f.norm_coe_le_norm x.val

theorem boundedSphereRestrictionL_apply (f : R3 →ᵇ V) (x : UnitSphere) :
    boundedSphereRestrictionL f x = f x.val := rfl

theorem contDiff_compactSupportSphereSlice
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : P × R3 → V) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ContDiff ℝ ∞ (fun p : P => (⟨fun x : UnitSphere => g (p,x.val),
      hg.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩ : C(UnitSphere,V))) := by
  let K : Set R3 := Prod.snd '' tsupport g
  have hK : IsCompact K := hgc.image continuous_snd
  have hz : ∀ p z, z ∉ K → g (p,z) = 0 := by
    intro p z hz
    by_contra hn
    exact hz ⟨(p,z),subset_tsupport g hn,rfl⟩
  have hs := BoundedParameterSmoothness.contDiff_infty_commonSupportSlice g hg K hK hz
  convert (boundedSphereRestrictionL (V := V)).contDiff.comp hs using 1
  funext p
  apply ContinuousMap.ext
  intro x
  rfl

end OAI.AnisotropicCalderon.DirichletFamily
