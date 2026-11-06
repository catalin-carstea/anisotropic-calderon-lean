import Calderon.ActualMixedKernelGlobalNativeFiveHalfDensity
import Calderon.ActualNativeHarmonicTestDensityUniqueness
import Calderon.ActualSameCutoffFiveHalfFieldEquality

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter Function
open scoped ENNReal ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError SphereHarmonic
  MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint

/-- Any density satisfying the original native physical-flux identity for this
same constructed kernel has the canonical compact H5/2 lift. -/
theorem exists_fiveHalf_lift_of_eligible_native_density
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (hPsiSmooth : ContDiff ℝ ∞ Psi) (hPsiCompact : HasCompactSupport Psi)
    (hFlux : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ u : SmoothData,
      (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
        (packetEndpoint S L (cover.packet i) lam y
          (referenceRadius delta Rstar p L y) z) = 0) →
      nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p Psi u y =
      nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
        y (referenceRadius delta Rstar p L y) y)
    (chi : R3 → ℝ) (hchiSupp : tsupport chi ⊆ interior cylinder) :
    ∃ Psi5 : R3 → SphereSobolev (5/2 : ℝ),
      ContDiff ℝ ∞ Psi5 ∧ HasCompactSupport Psi5 ∧
      (∀ y ∈ cylinder,
        sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (Psi5 y) = Psi y) ∧
      (fun y => sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
        (chi y • Psi5 y)) = (fun y => chi y • Psi y) := by
  obtain ⟨Gext,hG,Psi0,Psi5,hGc,hPsi0Smooth,hPsi0Comp,hPsi5Smooth,hPsi5Comp,
      hInc,hGerm,U,hU,hCU,hPsiPacket,hFlux0⟩ :=
    exists_global_native_mixed_kernel_density_with_fiveHalf_lift
      hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K
      hdelta hRstar hLam hRadius
  have hEq : ∀ y ∈ cylinder, Psi0 y = Psi y := by
    intro y hy
    obtain ⟨i,hi⟩ := cover.covers_cylinder y hy
    have hrPos : 0 < referenceRadius delta Rstar p L y :=
      referenceRadius_pos delta Rstar p L y hdelta hRstar
    have hrCeil : referenceRadius delta Rstar p L y < cover.radiusCeiling :=
      hRadius y hy
    apply eq_of_nativeMixedKernelDensityFunctional_eq_on_actual_physical_harmonic_tests
      hcalc hreg hF hO hD τ0 S L lam delta Rstar p cover i hLam y hi
      hrPos hrCeil Psi0 Psi
    intro V hV u hCover hPhysical
    have hBall : ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y
            (referenceRadius delta Rstar p L y) z) = 0 := by
      intro z hz
      exact hPhysical _ (hCover ⟨z,ball_subset_closedBall hz,rfl⟩)
    have h0 := hFlux0 i y ⟨hy,hi⟩ u hBall
    change nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
      lam delta Rstar p Psi0 u y =
      nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
        y (referenceRadius delta Rstar p L y) y at h0
    exact h0.trans (hFlux i y ⟨hy,hi⟩ u hBall).symm
  have hIncPsi : ∀ y ∈ cylinder,
      sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (Psi5 y) = Psi y := by
    intro y hy
    exact (hInc y hy).trans (hEq y hy)
  exact ⟨Psi5,hPsi5Smooth,hPsi5Comp,hIncPsi,
    sphereSobolevInclusionL_sameCutoff_fiveHalf_field chi hchiSupp Psi5 Psi hIncPsi⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
