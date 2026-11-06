import Calderon.NativeOrderOneCoefficientMultiplierTopology
import Calderon.FiniteDimensionalLocalSmoothExtension

/-! Full upfront: EXPANSION-NativeThreeHalfBoundaryMultiplierLocalSmoothness-v001.md.
Actual native H3/2 multiplier, arbitrary ambient extensions, local operator norm. -/
set_option autoImplicit false
noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeOrderOneCoefficientMultiplier

theorem nativeThreeHalfCoefficientMulL_eq_of_sphereValue_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F G : SmoothCoefficientJets 3)
    (hSphere : smoothSphereValue (nativeH2CoefficientSmoothData F) =
      smoothSphereValue (nativeH2CoefficientSmoothData G)) :
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (3/2 : ℝ) 0 (by norm_num)
  rw [sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero,
    sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero,hSphere]

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem contDiffAt_nativeThreeHalfCoefficientMulL_of_joint_on_open
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (f : P × R3 → ℝ) (S : Set (P × R3)) (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (F : P → SmoothCoefficientJets 3)
    (hFValue : ∀ p, (∀ x : UnitSphere, (p,x.val) ∈ S) → ∀ x : UnitSphere,
      smoothSphereValue (nativeH2CoefficientSmoothData (F p)) x = f (p,x.val))
    (p0 : P) (hCover : ∀ x : UnitSphere, (p0,x.val) ∈ S) :
    ContDiffAt ℝ ∞ (fun p => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (F p)) p0 := by
  let K0 : Set (P × R3) := {p0} ×ˢ sphere (0 : R3) 1
  have hK0 : IsCompact K0 := isCompact_singleton.prod (isCompact_sphere _ _)
  have hK0S : K0 ⊆ S := by
    rintro ⟨p,z⟩ ⟨hp,hz⟩
    have hp0 : p = p0 := Set.mem_singleton_iff.mp hp
    rw [hp0]
    exact hCover ⟨z,hz⟩
  obtain ⟨g,hg,hgc,hEq⟩ :=
    exists_contDiff_eq_near_compact_of_contDiffOn K0 S hK0 hS hK0S f hf
  let K : Set R3 := Prod.snd '' tsupport g
  have hK : IsCompact K := hgc.image continuous_snd
  have hz : ∀ p z, z ∉ K → g (p,z) = 0 := by
    intro p z hOutside
    by_contra hn
    exact hOutside ⟨(p,z),subset_tsupport g hn,rfl⟩
  have hSmooth := contDiff_nativeThreeHalfCoefficientMulL_commonSupport
    hcalc hF hO hD τ0 g hg K hK hz
  have hNear : ∀ᶠ p in 𝓝 p0, ∀ z ∈ sphere (0 : R3) 1, g (p,z) = f (p,z) := by
    apply (isCompact_sphere (0 : R3) 1).eventually_forall_of_forall_eventually
    intro z hz
    exact hEq (p0,z) ⟨rfl,hz⟩
  have hIn : ∀ᶠ p in 𝓝 p0, ∀ z ∈ sphere (0 : R3) 1, (p,z) ∈ S := by
    apply (isCompact_sphere (0 : R3) 1).eventually_forall_of_forall_eventually
    intro z hz
    exact hS.mem_nhds (hCover ⟨z,hz⟩)
  apply hSmooth.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hNear,hIn] with p hp hin
  apply nativeThreeHalfCoefficientMulL_eq_of_sphereValue_eq hcalc hF hO hD τ0
  apply ContinuousMap.ext
  intro x
  change smoothSphereValue (nativeH2CoefficientSmoothData (F p)) x =
    coefficientValue 3 (commonSupportCoefficientFamily 3 g hg K hK hz p) x.val
  rw [coefficientValue_commonSupportCoefficientFamily]
  exact (hFValue p (fun z => hin z.val z.property) x).trans (hp x.val x.property).symm

end OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier

#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.nativeThreeHalfCoefficientMulL_eq_of_sphereValue_eq
#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.contDiffAt_nativeThreeHalfCoefficientMulL_of_joint_on_open
