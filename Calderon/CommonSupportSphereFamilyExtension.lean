import Calderon.NativeBoundaryMultiplierLocalSmoothness

set_option autoImplicit false
noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge SphereHarmonic

theorem exists_contDiff_commonSupport_eq_near_compact_sphere
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (K : Set P) (hK : IsCompact K) (S : Set (P × R3)) (hS : IsOpen S)
    (f : P × R3 → ℝ) (hf : ContDiffOn ℝ ∞ f S)
    (hCover : ∀ p ∈ K, ∀ x : UnitSphere, (p,x.val) ∈ S) :
    ∃ (m : P × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
      (Km : Set R3) (hKm : IsCompact Km)
      (hmz : ∀ p x, x ∉ Km → m (p,x)=0),
      ∀ p ∈ K, ∀ᶠ z in 𝓝 p, ∀ x : UnitSphere,
        m (z,x.val)=f (z,x.val) ∧ (z,x.val) ∈ S := by
  let K0 : Set (P × R3) := K ×ˢ sphere (0 : R3) 1
  have hK0 : IsCompact K0 := hK.prod (isCompact_sphere _ _)
  have hK0S : K0 ⊆ S := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩
    exact hCover p hp ⟨x,hx⟩
  obtain ⟨m,hm,hmc,hEq⟩ :=
    exists_contDiff_eq_near_compact_of_contDiffOn K0 S hK0 hS hK0S f hf
  let Km : Set R3 := Prod.snd '' tsupport m
  have hKm : IsCompact Km := hmc.image continuous_snd
  have hmz : ∀ p x, x ∉ Km → m (p,x)=0 := by
    intro p x hx
    by_contra hn
    exact hx ⟨(p,x),subset_tsupport m hn,rfl⟩
  refine ⟨m,hm,Km,hKm,hmz,?_⟩
  intro p hp
  have hNear : ∀ᶠ z in 𝓝 p, ∀ x ∈ sphere (0 : R3) 1, m (z,x)=f (z,x) := by
    apply (isCompact_sphere (0 : R3) 1).eventually_forall_of_forall_eventually
    intro x hx
    exact hEq (p,x) ⟨hp,hx⟩
  have hIn : ∀ᶠ z in 𝓝 p, ∀ x ∈ sphere (0 : R3) 1, (z,x) ∈ S := by
    apply (isCompact_sphere (0 : R3) 1).eventually_forall_of_forall_eventually
    intro x hx
    exact hS.mem_nhds (hCover p hp ⟨x,hx⟩)
  filter_upwards [hNear,hIn] with z hz hin
  exact fun x => ⟨hz x.val x.property,hin x.val x.property⟩

end OAI.AnisotropicCalderon.DirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.exists_contDiff_commonSupport_eq_near_compact_sphere
