import Calderon.FiniteDimensionalLocalSmoothExtension
import Calderon.CompactSupportSphereCurrying

set_option autoImplicit false
noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume SphereHarmonic

theorem contDiffAt_sphereFamily_of_joint_on_open
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : P × R3 → V) (S : Set (P × R3)) (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (F : P → C(UnitSphere,V))
    (hF : ∀ p, (∀ x : UnitSphere, (p,x.val) ∈ S) → ∀ x : UnitSphere, F p x = f (p,x.val))
    (p0 : P) (hCover : ∀ x : UnitSphere, (p0,x.val) ∈ S) :
    ContDiffAt ℝ ∞ F p0 := by
  let K : Set (P × R3) := {p0} ×ˢ sphere (0 : R3) 1
  have hK : IsCompact K := isCompact_singleton.prod (isCompact_sphere _ _)
  have hKS : K ⊆ S := by
    rintro ⟨p,z⟩ ⟨hp,hz⟩
    have hp0 : p = p0 := Set.mem_singleton_iff.mp hp
    rw [hp0]
    exact hCover ⟨z,hz⟩
  obtain ⟨g,hg,hgc,hEq⟩ := exists_contDiff_eq_near_compact_of_contDiffOn K S hK hS hKS f hf
  let G : P → C(UnitSphere,V) := fun p =>
    ⟨fun x => g (p,x.val),hg.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩
  have hG : ContDiff ℝ ∞ G := contDiff_compactSupportSphereSlice g hg hgc
  have hNear : ∀ᶠ p in 𝓝 p0, ∀ z ∈ sphere (0 : R3) 1, g (p,z) = f (p,z) := by
    apply (isCompact_sphere (0 : R3) 1).eventually_forall_of_forall_eventually
    intro z hz
    exact hEq (p0,z) ⟨rfl,hz⟩
  have hIn : ∀ᶠ p in 𝓝 p0, ∀ z ∈ sphere (0 : R3) 1, (p,z) ∈ S := by
    apply (isCompact_sphere (0 : R3) 1).eventually_forall_of_forall_eventually
    intro z hz
    exact hS.mem_nhds (hCover ⟨z,hz⟩)
  apply hG.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hNear,hIn] with p hp hin
  apply ContinuousMap.ext
  intro x
  exact (hF p (fun z => hin z.val z.property) x).trans (hp x.val x.property).symm

end OAI.AnisotropicCalderon.DirichletFamily
