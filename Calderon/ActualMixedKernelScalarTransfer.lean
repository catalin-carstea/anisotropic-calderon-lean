import Calderon.ActualMixedKernelGlobalNativeDensity
import Calderon.ActualMixedKernelFixedFluxSecondPDE

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter Function
open scoped ContDiff Topology Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift

/-- A compact moving family retains full product germs on one open center room. -/
private theorem exists_open_moving_compact_product_germs
    (A : Set R3) (hA : IsCompact A) (X : R3 → R3 → R3)
    (hX : Continuous (Function.uncurry X)) (G H : R3 × R3 → ℝ) (y : R3)
    (hBase : ∀ z ∈ A, G =ᶠ[𝓝 (X y z,y)] H) :
    ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
      ∀ y' ∈ Y, ∀ z ∈ A, G =ᶠ[𝓝 (X y' z,y')] H := by
  let E : Set (R3 × R3) := {w | G =ᶠ[𝓝 w] H}
  have hE : IsOpen E := isOpen_setOfPred_eventually_nhds (p := fun w => G w = H w)
  let T : R3 × R3 → R3 × R3 := fun w => (X w.2 w.1,w.2)
  have hT : Continuous T :=
    (hX.comp (continuous_snd.prodMk continuous_fst)).prodMk continuous_snd
  have hRoom : IsOpen (T ⁻¹' E) := hE.preimage hT
  have hInside : A ×ˢ ({y} : Set R3) ⊆ T ⁻¹' E := by
    rintro ⟨z,p⟩ ⟨hz,hp⟩
    have hp' : p = y := mem_singleton_iff.mp hp
    subst p
    exact hBase z hz
  obtain ⟨U,Y,_,hY,hAU,hyY,hUY⟩ :=
    generalized_tube_lemma hA isCompact_singleton hRoom hInside
  refine ⟨Y,hY,hyY (mem_singleton y),?_⟩
  intro y' hy' z hz
  have ht : (z,y') ∈ T ⁻¹' E := hUY ⟨hAU hz,hy'⟩
  exact ht

/-- A compact moving image remains in its original open physical test room. -/
private theorem exists_open_moving_compact_image_subset
    (A : Set R3) (hA : IsCompact A) (X : R3 → R3 → R3)
    (hX : Continuous (Function.uncurry X)) (V : Set R3) (hV : IsOpen V) (y : R3)
    (hBase : X y '' A ⊆ V) :
    ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧ ∀ y' ∈ Y, X y' '' A ⊆ V := by
  let T : R3 × R3 → R3 := fun w => X w.2 w.1
  have hT : Continuous T := hX.comp (continuous_snd.prodMk continuous_fst)
  have hRoom : IsOpen (T ⁻¹' V) := hV.preimage hT
  have hInside : A ×ˢ ({y} : Set R3) ⊆ T ⁻¹' V := by
    rintro ⟨z,p⟩ ⟨hz,hp⟩
    have hp' : p = y := mem_singleton_iff.mp hp
    subst p
    exact hBase ⟨z,hz,rfl⟩
  obtain ⟨U,Y,_,hY,hAU,hyY,hUY⟩ :=
    generalized_tube_lemma hA isCompact_singleton hRoom hInside
  refine ⟨Y,hY,hyY (mem_singleton y),?_⟩
  intro y' hy' x hx
  obtain ⟨z,hz,rfl⟩ := hx
  have ht : (z,y') ∈ T ⁻¹' V := hUY ⟨hAU hz,hy'⟩
  exact ht

def nativeMixedKernelDensityFunctional
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam delta Rstar : ℝ) (p : ℕ) (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (u : SmoothData) (y : R3) : ℝ :=
  ⟪(sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)),
    τ0.valueTraceL (smoothSobolev (referencePhysicalPullbackData S.g1 S.g1_admissible L
      P.y0 P.Phi P.B P.native_data.1.1.1 lam y (referenceRadius delta Rstar p L y) u))⟫_ℝ

attribute [local irreducible] nativeMixedKernelHighDensity sphereSobolevZeroEquiv sphereSobolevInclusionL

theorem exists_open_nativeMixedKernelDensityFunctional_secondPDE
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (Psi : R3 → SphereSobolev (3/2 : ℝ)) (U : Set R3) (hU : IsOpen U)
    (hCU : cylinder ⊆ U)
    (hProfile : ∀ i : Fin cover.count, ∀ z ∈ U ∩ (cover.packet i).centers,
      Psi z = nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L (cover.packet i) Gext hG
        (lam,(z,referenceRadius delta Rstar p L z)))
    (hGerm : ∀ i : Fin cover.count, ∀ z ∈ cylinder ∩ (cover.packet i).centers,
      ∀ t ∈ sphere (0 : R3) 1, Gext =ᶠ[𝓝 (packetEndpoint S L (cover.packet i) lam z
        (referenceRadius delta Rstar p L z) t,z)] K.kernel)
    (i : Fin cover.count) (y : R3) (hy : y ∈ cylinder ∩ (cover.packet i).centers)
    (hrceil : referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (V : Set R3) (hV : IsOpen V) (u : SmoothData)
    (hCover : packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
      closedBall (0 : R3) 1 ⊆ V)
    (hphysical : ∀ x ∈ V, coordinateFluxDivergence
      (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) :
    ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
      ContDiffOn ℝ ∞ (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p Psi u) Y ∧
      ∀ z ∈ Y, normalizedSecondLaplacian S.g1 S.g2 L lam
        (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u) z = 0 := by
  let P := cover.packet i
  let R := referenceRadius delta Rstar p L
  let X : R3 → R3 → R3 := fun z t => packetEndpoint S L P lam z (R z) t
  have hR : ContDiff ℝ ∞ R := contDiff_referenceRadius_actual delta Rstar p L hdelta hRstar
  have hTheta : ContDiff ℝ ∞ (fun v : ℝ × (R3 × R3) => (P.Phi v.1 v.2 1).1) :=
    P.native_data.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ (Function.uncurry X) :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk ((contDiff_fst.prodMk (hR.comp contDiff_fst)).prodMk contDiff_snd))
  obtain ⟨YG,hYG,hyG,hGerms⟩ := exists_open_moving_compact_product_germs
    (sphere (0 : R3) 1) (isCompact_sphere _ _) X hX.continuous Gext K.kernel y (hGerm i y hy)
  obtain ⟨YT,hYT,hyT,hTest⟩ := exists_open_moving_compact_image_subset
    (closedBall (0 : R3) 1) (isCompact_closedBall _ _) X hX.continuous V hV y hCover
  obtain ⟨YM,hYM,hyM,hMoving⟩ := exists_open_native_mixed_kernel_moving_fixed_flux_eq
    S L lam delta Rstar bound separation p cover K hdelta hRstar i y hy V hV u hCover hphysical
  obtain ⟨YF,hYF,hyF,hFixedSmooth,hFixedPDE⟩ := exists_open_native_mixed_kernel_fixed_flux_secondPDE
    S L lam delta Rstar bound separation p cover K hdelta hRstar i y hy u
  let W : Set R3 := (U ∩ P.centers) ∩ {z | R z < cover.radiusCeiling}
  have hW : IsOpen W := (hU.inter P.centers_open).inter (isOpen_lt hR.continuous continuous_const)
  have hyW : y ∈ W := ⟨⟨hCU hy.1,hy.2⟩,hrceil⟩
  let Y : Set R3 := W ∩ YG ∩ YT ∩ YM ∩ YF
  have hY : IsOpen Y := (((hW.inter hYG).inter hYT).inter hYM).inter hYF
  have hyY : y ∈ Y := ⟨⟨⟨⟨hyW,hyG⟩,hyT⟩,hyM⟩,hyF⟩
  have hq : lam ∈ Icc (0 : ℝ) 1 := ⟨hLam.1,hLam.2.trans cover.dilation_le_one⟩
  have hEq : ∀ z ∈ Y,
      nativeMixedKernelDensityFunctional hO hD τ0 S L P lam delta Rstar p Psi u z =
        nativeMixedKernelWronskianFlux S L P lam K.kernel u.1 y (R y) z := by
    intro z hz
    have hzW : z ∈ W := hz.1.1.1.1
    have hzG : z ∈ YG := hz.1.1.1.2
    have hzT : z ∈ YT := hz.1.1.2
    have hzM : z ∈ YM := hz.1.2
    have hcenter : ‖z-P.y0‖ ≤ 4*P.rho := (P.centers_room z hzW.1.2).1.le
    have hrpos : 0 < R z := referenceRadius_pos delta Rstar p L z hdelta hRstar
    have hr : |R z| ≤ 4*P.rho := by
      rw [abs_of_pos hrpos]
      exact (hzW.2.trans (cover.radius_room i)).le
    have hTestPDE : ∀ t ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1) (X z t) = 0 := by
      intro t ht
      have htClosed : t ∈ closedBall (0 : R3) 1 := by
        apply ball_subset_closedBall
        simpa only [coe_ballOpens,B] using ht
      exact hphysical (X z t) (hTest z hzT ⟨t,htClosed,rfl⟩)
    have hRep : nativeMixedKernelDensityFunctional hO hD τ0 S L P lam delta Rstar p Psi u z =
        nativeMixedKernelWronskianFlux S L P lam Gext u.1 z (R z) z := by
      unfold nativeMixedKernelDensityFunctional
      rw [hProfile i z hzW.1]
      exact nativeMixedKernelHighDensity_represents_physicalFlux hcalc hreg hF hO hD τ0 S L P
        Gext hG lam hq z hcenter (R z) hr hrpos u hTestPDE
    exact hRep.trans ((nativeMixedKernelWronskianFlux_eq_of_product_germs S L P lam Gext K.kernel
      u.1 z (R z) z (hGerms z hzG)).trans (hMoving z hzM))
  refine ⟨Y,hY,hyY,?_,?_⟩
  · exact (hFixedSmooth.mono (fun _ hz => hz.2)).congr (fun z hz => hEq z hz)
  · intro z hz
    have hNear : nativeMixedKernelDensityFunctional hO hD τ0 S L P lam delta Rstar p Psi u =ᶠ[𝓝 z]
        (fun t => nativeMixedKernelWronskianFlux S L P lam K.kernel u.1 y (R y) t) := by
      filter_upwards [hY.mem_nhds hz] with t ht using hEq t ht
    rw [fixedFlux_normalized_congr S L lam _ _ z hNear]
    exact hFixedPDE z hz.2

theorem exists_global_nativeMixedKernelDensityFunctional_secondPDE
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    ∃ Psi : R3 → SphereSobolev (3/2 : ℝ), ContDiff ℝ ∞ Psi ∧ HasCompactSupport Psi ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers, ∀ u : SmoothData,
        (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
          (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u y =
          nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
            y (referenceRadius delta Rstar p L y) y) ∧
      ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        ∀ (V : Set R3), IsOpen V → ∀ u : SmoothData,
        packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
          closedBall (0 : R3) 1 ⊆ V →
        (∀ x ∈ V, coordinateFluxDivergence (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) →
        ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
          ContDiffOn ℝ ∞ (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
            lam delta Rstar p Psi u) Y ∧
          ∀ z ∈ Y, normalizedSecondLaplacian S.g1 S.g2 L lam
            (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u) z = 0 := by
  obtain ⟨Gext,hG,Psi,_,hPsi,hCompact,hGerm,U,hU,hCU,hProfile,hRep⟩ :=
    exists_global_native_mixed_kernel_high_density_represents_physicalFlux
      hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K hdelta hRstar hLam hRadius
  refine ⟨Psi,hPsi,hCompact,?_,?_⟩
  · intro i y hy u hphysical
    simpa only [nativeMixedKernelDensityFunctional] using hRep i y hy u hphysical
  · intro i y hy V hV u hCover hphysical
    exact exists_open_nativeMixedKernelDensityFunctional_secondPDE
      hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p cover K hdelta hRstar hLam
      Gext hG Psi U hU hCU hProfile hGerm i y hy (hRadius y hy.1) V hV u hCover hphysical

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
