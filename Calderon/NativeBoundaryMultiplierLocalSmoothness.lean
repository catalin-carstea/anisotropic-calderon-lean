import Calderon.NativeCoefficientBoundaryMultiplier
import Calderon.FiniteDimensionalLocalSmoothExtension

set_option autoImplicit false
noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic NativeFullSharpHalfTrace
  NativeHalfSmoothMultiplier

theorem nativeHalfCoefficientMulL_eq_of_sphereValue_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F G : SmoothCoefficientJets 2)
    (hSphere : smoothSphereValue (coefficientSmoothData F) =
      smoothSphereValue (coefficientSmoothData G)) :
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 F =
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 G := by
  obtain ⟨M,hM,hm,hgm⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  obtain ⟨N,hN,hn,hgn⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData G)
  rw [nativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F hM hm hgm,
    nativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 G hN hn hgn]
  exact nativeHalfSmoothMulL_eq_of_sphereValue_eq hF hO hD τ0
    (coefficientSmoothData F) (coefficientSmoothData G) hM hN hm hgm hn hgn hSphere

theorem nativeNegativeHalfCoefficientMulL_eq_of_sphereValue_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F G : SmoothCoefficientJets 2)
    (hSphere : smoothSphereValue (coefficientSmoothData F) =
      smoothSphereValue (coefficientSmoothData G)) :
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F =
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G := by
  exact congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
    realHalfOperatorAdjointL A)
      (nativeHalfCoefficientMulL_eq_of_sphereValue_eq hcalc hF hO hD τ0 F G hSphere)

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem contDiffAt_nativeHalfCoefficientMulL_of_joint_on_open
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (f : P × R3 → ℝ) (S : Set (P × R3)) (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (F : P → SmoothCoefficientJets 2)
    (hFValue : ∀ p, (∀ x : UnitSphere, (p,x.val) ∈ S) → ∀ x : UnitSphere,
      smoothSphereValue (coefficientSmoothData (F p)) x = f (p,x.val))
    (p0 : P) (hCover : ∀ x : UnitSphere, (p0,x.val) ∈ S) :
    ContDiffAt ℝ ∞ (fun p => nativeHalfCoefficientMulL hcalc hF hO hD τ0 (F p)) p0 := by
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
  have hSmooth := contDiff_nativeHalfCoefficientMulL_commonSupport
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
  apply nativeHalfCoefficientMulL_eq_of_sphereValue_eq hcalc hF hO hD τ0
  apply ContinuousMap.ext
  intro x
  change smoothSphereValue (coefficientSmoothData (F p)) x =
    coefficientValue 2 (commonSupportCoefficientFamily 2 g hg K hK hz p) x.val
  rw [coefficientValue_commonSupportCoefficientFamily]
  exact (hFValue p (fun z => hin z.val z.property) x).trans (hp x.val x.property).symm

theorem contDiffAt_nativeNegativeHalfCoefficientMulL_of_joint_on_open
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (f : P × R3 → ℝ) (S : Set (P × R3)) (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (F : P → SmoothCoefficientJets 2)
    (hFValue : ∀ p, (∀ x : UnitSphere, (p,x.val) ∈ S) → ∀ x : UnitSphere,
      smoothSphereValue (coefficientSmoothData (F p)) x = f (p,x.val))
    (p0 : P) (hCover : ∀ x : UnitSphere, (p0,x.val) ∈ S) :
    ContDiffAt ℝ ∞ (fun p => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (F p)) p0 := by
  have hAdj : ContDiff ℝ ∞ (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      realHalfOperatorAdjointL A) := by
    apply ContinuousLinearMap.contDiff
  exact hAdj.contDiffAt.comp p0
    (contDiffAt_nativeHalfCoefficientMulL_of_joint_on_open
      hcalc hF hO hD τ0 f S hS hf F hFValue p0 hCover)

end OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

#print axioms OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier.nativeHalfCoefficientMulL_eq_of_sphereValue_eq
#print axioms OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier.nativeNegativeHalfCoefficientMulL_eq_of_sphereValue_eq
#print axioms OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier.contDiffAt_nativeHalfCoefficientMulL_of_joint_on_open
#print axioms OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier.contDiffAt_nativeNegativeHalfCoefficientMulL_of_joint_on_open
