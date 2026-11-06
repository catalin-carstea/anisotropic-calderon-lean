import Calderon.ActualNativeCurrentFrontKernelUniqueness
import Calderon.NativeMixedKernelBoundaryGermDensity
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError ConformalDepth
attribute [local irreducible] nativeMixedKernelDensityFunctional nativeMixedKernelWronskianFlux
  harmonicSphereSubspace

def RepresentsNativeMixedKernelDensity
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (Psi : R3 → SphereSobolev (3/2:ℝ)) : Prop :=
  ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
    ∀ u : SmoothData,
    (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
      (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
        (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
    nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u y =
      nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1 y (referenceRadius delta Rstar p L y) y

theorem exists_smallDilation_native_density_independent_of_constructed_kernel
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : KnownSideSourceData) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ (L : ℝ) (cover : NativeNormalCover S L)
      (lam delta Rstar bound separation : ℝ) (p : ℕ)
      (K1 K2 : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
      (Psi1 Psi2 : R3 → SphereSobolev (3/2:ℝ)),
      RepresentsNativeMixedKernelDensity hO hD τ0 S L lam delta Rstar bound separation p cover K1 Psi1 →
      RepresentsNativeMixedKernelDensity hO hD τ0 S L lam delta Rstar bound separation p cover K2 Psi2 →
      0 < lam → lam ≤ lam0 → lam ≤ cover.dilationCeiling → 0 < delta → 0 < Rstar →
      (∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) →
      ∀ y ∈ cylinder, Psi1 y = Psi2 y := by
  obtain ⟨lam0,hlam0,hGerm⟩ := exists_uniform_constructedMixedKernel_sphere_germ_uniqueness S
  refine ⟨lam0,hlam0,?_⟩
  intro L cover lam delta Rstar bound separation p K1 K2 Psi1 Psi2 hRep1 hRep2
    hlam hlamSmall hlamRoom hdelta hRstar hRadius y hy
  obtain ⟨i,hi⟩ := cover.covers_cylinder y hy
  have hLam : lam ∈ Icc (0:ℝ) cover.dilationCeiling := ⟨hlam.le,hlamRoom⟩
  have hrPos := referenceRadius_pos delta Rstar p L y hdelta hRstar
  apply eq_of_nativeMixedKernelDensityFunctional_eq_on_actual_physical_harmonic_tests
    hcalc hreg hF hO hD τ0 S L lam delta Rstar p cover i hLam y hi hrPos (hRadius y hy) Psi1 Psi2
  intro V hV u hCover hPhysical
  have hBall : ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
      (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
        (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0 := by
    intro z hz
    exact hPhysical _ (hCover ⟨z,ball_subset_closedBall hz,rfl⟩)
  have hFlux := nativeMixedKernelWronskianFlux_eq_of_product_germs S L (cover.packet i) lam
    K1.kernel K2.kernel u.1 y (referenceRadius delta Rstar p L y) y
    (hGerm L cover lam delta Rstar bound separation p K1 K2 hlam hlamSmall hlamRoom hdelta hRstar hRadius i y ⟨hy,hi⟩)
  exact (hRep1 i y ⟨hy,hi⟩ u hBall).trans (hFlux.trans (hRep2 i y ⟨hy,hi⟩ u hBall).symm)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
