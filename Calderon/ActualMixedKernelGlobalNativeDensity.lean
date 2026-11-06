import Calderon.ActualMixedKernelPhysicalDensityRepresentation
import Calderon.ActualMixedKernelDensityProfileGluing
import Calderon.NativeHighDensityLocalExtension

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint

attribute [local irreducible] nativeMixedKernelHighDensity sphereSobolevZeroEquiv sphereSobolevInclusionL

theorem exists_global_native_mixed_kernel_high_density_represents_physicalFlux
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    ∃ (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
      (Psi : R3 → SphereSobolev (3/2 : ℝ)),
      HasCompactSupport Gext ∧ ContDiff ℝ ∞ Psi ∧ HasCompactSupport Psi ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        ∀ z ∈ sphere (0 : R3) 1, Gext =ᶠ[𝓝 (packetEndpoint S L (cover.packet i) lam y
          (referenceRadius delta Rstar p L y) z,y)] K.kernel) ∧
      ∃ U : Set R3, IsOpen U ∧ cylinder ⊆ U ∧
        (∀ i : Fin cover.count, ∀ y ∈ U ∩ (cover.packet i).centers,
          Psi y = nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Gext hG
            (lam,(y,referenceRadius delta Rstar p L y))) ∧
        ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers, ∀ u : SmoothData,
          (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
            (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
            (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
          ⟪(sphereSobolevZeroEquiv hO hD).symm
            (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)),
            τ0.valueTraceL (smoothSobolev (referencePhysicalPullbackData S.g1 S.g1_admissible L
              (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
              (cover.packet i).native_data.1.1.1 lam y (referenceRadius delta Rstar p L y) u))⟫_ℝ =
          nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
            y (referenceRadius delta Rstar p L y) y := by
  obtain ⟨Gext,hG,hGc,hGerm⟩ := exists_smooth_mixed_kernel_eq_near_all_native_surfaces
    S L lam delta Rstar bound separation p cover K hdelta hRstar hLam hRadius
  obtain ⟨psi0,U,hU,hCU,hSmooth,hPacket⟩ :=
    exists_smooth_nativeMixedKernelHighDensity_profile_on_neighborhood
      hcalc hreg hF hO hD τ0 S L lam delta Rstar p cover Gext hG hdelta hRstar hLam hRadius
  obtain ⟨Psi,hPsi,hPsiCompact,hPsiGerm⟩ := exists_contDiff_compact_extension_eq_near_compact
    cylinder U isCompact_native_center_cylinder hU hCU psi0 hSmooth
  let V : Set R3 := U ∩ {y | Psi =ᶠ[𝓝 y] psi0}
  have hV : IsOpen V := hU.inter isOpen_setOfPred_eventually_nhds
  have hCV : cylinder ⊆ V := fun y hy => ⟨hCU hy,hPsiGerm y hy⟩
  have hEq : ∀ i : Fin cover.count, ∀ y ∈ V ∩ (cover.packet i).centers,
      Psi y = nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Gext hG
        (lam,(y,referenceRadius delta Rstar p L y)) := by
    intro i y hy
    exact hy.1.2.eq_of_nhds.trans (hPacket i y ⟨hy.1.1,hy.2⟩)
  refine ⟨Gext,hG,Psi,hGc,hPsi,hPsiCompact,hGerm,V,hV,hCV,hEq,?_⟩
  intro i y hy u hphysical
  rw [hEq i y ⟨hCV hy.1,hy.2⟩]
  have hq : lam ∈ Icc (0 : ℝ) 1 := ⟨hLam.1,hLam.2.trans cover.dilation_le_one⟩
  have hc := ((cover.packet i).centers_room y hy.2).1.le
  have hRpos := referenceRadius_pos delta Rstar p L y hdelta hRstar
  have hr : |referenceRadius delta Rstar p L y| ≤ 4*(cover.packet i).rho := by
    rw [abs_of_pos hRpos]
    exact ((hRadius y hy.1).trans (cover.radius_room i)).le
  exact (nativeMixedKernelHighDensity_represents_physicalFlux hcalc hreg hF hO hD τ0 S L
    (cover.packet i) Gext hG lam hq y hc (referenceRadius delta Rstar p L y) hr hRpos u
    hphysical).trans (nativeMixedKernelWronskianFlux_eq_of_product_germs S L (cover.packet i)
      lam Gext K.kernel u.1 y (referenceRadius delta Rstar p L y) y (hGerm i y hy))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
