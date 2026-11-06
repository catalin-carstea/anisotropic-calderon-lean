import Calderon.LocalSmoothAmbientExtension
import Mathlib.Topology.Compactness.Compact
/-! Source-only same ambient extension on a compact continuous parameter family.
Full expansion and literal interfaces were sealed before bodies. -/
set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem exists_smoothData_eq_near_compact_family
    {P : Type} [TopologicalSpace P]
    (X : P × R3 → R3) (hX : Continuous X) (p0 : P)
    (K S : Set R3) (hK : IsCompact K) (hS : IsOpen S)
    (hCover : (fun z => X (p0,z)) '' K ⊆ S)
    (u : R3 → ℝ) (hu : ContDiffOn ℝ ∞ u S) :
    ∃ (v : SmoothData) (U : Set P), HasCompactSupport v.1 ∧ IsOpen U ∧ p0 ∈ U ∧
      ∀ p ∈ U, (fun z => X (p,z)) '' K ⊆ S ∧
        ∀ z ∈ K, v.1 =ᶠ[𝓝 (X (p,z))] u := by
  let X0 : R3 → R3 := fun z => X (p0,z)
  let K0 := X0 '' K
  have hX0 : Continuous X0 := hX.comp (continuous_const.prodMk continuous_id)
  have hK0 : IsCompact K0 := hK.image hX0
  obtain ⟨v,hv,hNear⟩ := exists_smoothData_eq_near_compact K0 S hK0 hS hCover u hu
  let E := {x : R3 | v.1 x = u x}
  let A := S ∩ interior E
  have hA : IsOpen A := hS.inter isOpen_interior
  have hBase : ({p0} : Set P) ×ˢ K ⊆ X ⁻¹' A := by
    rintro ⟨p,z⟩ ⟨hp,hz⟩
    have hp0 : p = p0 := by simpa only [mem_singleton_iff] using hp
    subst p
    have hx : X (p0,z) ∈ K0 := ⟨z,hz,rfl⟩
    exact ⟨hCover hx,mem_interior_iff_mem_nhds.mpr (hNear (X (p0,z)) hx)⟩
  obtain ⟨U,V,hU,_,hBaseU,hKV,hUV⟩ :=
    generalized_tube_lemma (isCompact_singleton : IsCompact ({p0} : Set P)) hK
      (hA.preimage hX) hBase
  refine ⟨v,U,hv,hU,hBaseU (mem_singleton p0),?_⟩
  intro p hp
  have hImage (z : R3) (hz : z ∈ K) : X (p,z) ∈ A := hUV ⟨hp,hKV hz⟩
  constructor
  · rintro x ⟨z,hz,rfl⟩
    exact (hImage z hz).1
  · intro z hz
    exact mem_interior_iff_mem_nhds.mp (hImage z hz).2


end OAI.AnisotropicCalderon.DirichletFamily
