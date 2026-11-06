import Calderon.ActualMixedKernelFiveHalfDensityProfileSmooth
import Calderon.ActualMixedKernelGlobalNativeDensity

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter Function
open scoped ENNReal ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError SphereHarmonic
  MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint

/-- The existing global native density has a compact high-regularity lift on the
same source and cover. The equality is with that very density on the cylinder. -/
theorem exists_same_global_native_mixed_kernel_fiveHalf_density
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (hPsi : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      Psi y = nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Gext hG
        (lam,(y,referenceRadius delta Rstar p L y))) :
    ∃ Psi5 : R3 → SphereSobolev (5/2 : ℝ),
      ContDiff ℝ ∞ Psi5 ∧ HasCompactSupport Psi5 ∧
      ∀ y ∈ cylinder,
        sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (Psi5 y) = Psi y := by
  let U := nativeMixedKernelHighDensityProfileDomain S L delta Rstar p cover
  let psi5 := nativeMixedKernelGluedFiveHalfDensityProfile hcalc hF hO hD τ0
    S L lam delta Rstar p cover Gext hG
  have hU : IsOpen U :=
    isOpen_nativeMixedKernelHighDensityProfileDomain S L delta Rstar p cover hdelta hRstar
  have hCU : cylinder ⊆ U :=
    cylinder_subset_nativeMixedKernelHighDensityProfileDomain S L delta Rstar p cover hRadius
  have hSmooth : ContDiffOn ℝ ∞ psi5 U :=
    contDiffOn_nativeMixedKernelGluedFiveHalfDensityProfile hcalc hreg hF hO hD τ0
      S L lam delta Rstar p cover Gext hG hdelta hRstar hLam
  obtain ⟨Psi5,hPsi5,hPsi5Compact,hGerm⟩ :=
    exists_contDiff_compact_extension_eq_near_compact cylinder U
      isCompact_native_center_cylinder hU hCU psi5 hSmooth
  refine ⟨Psi5,hPsi5,hPsi5Compact,?_⟩
  intro y hy
  obtain ⟨i,hi⟩ := cover.covers_cylinder y hy
  have hEq5 : Psi5 y = psi5 y := (hGerm y hy).eq_of_nhds
  rw [hEq5]
  change sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
      (nativeMixedKernelGluedFiveHalfDensityProfile hcalc hF hO hD τ0
        S L lam delta Rstar p cover Gext hG y) = Psi y
  rw [sphereSobolevInclusionL_nativeMixedKernelGluedFiveHalfDensityProfile hcalc hreg hF hO hD τ0
    S L lam delta Rstar p cover Gext hG y]
  rw [nativeMixedKernelGluedHighDensityProfile_eq_packet hcalc hF hO hD τ0 S L
    lam delta Rstar p cover Gext hG hdelta hRstar hLam i y hi (hRadius y hy)]
  exact (hPsi i y ⟨hy,hi⟩).symm

/-- A cutoff supported in the original cylinder sees exactly the existing
low-order native density after lowering the high-order lift. -/
theorem smul_sphereSobolevInclusionL_same_global_native_mixed_kernel_fiveHalf_density
    (chi : R3 → ℝ)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (Psi5 : R3 → SphereSobolev (5/2 : ℝ))
    (hchi : tsupport chi ⊆ interior cylinder)
    (hEq : ∀ y ∈ cylinder,
      sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (Psi5 y) = Psi y) :
    (fun y => chi y • sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (Psi5 y)) =
      (fun y => chi y • Psi y) := by
  funext y
  by_cases hy : chi y = 0
  · simp [hy]
  have hys : y ∈ tsupport chi := subset_closure (mem_support.mpr hy)
  rw [hEq y (interior_subset (hchi hys))]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
