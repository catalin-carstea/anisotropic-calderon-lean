import Calderon.ActualGlobalNativeDensityCoordinateReproduction
import Calderon.ActualOriginalSourceResponseCoordinatePDE
import Calderon.ActualMixedKernelGlobalSurfaceExtension
import Calderon.LocalSmoothAmbientExtension
import Calderon.PhysicalHarmonicDilation
import Calderon.ActualCoveredScalarTransfer
import Calderon.ActualNormalizedSecondUCPDictionary
import Calderon.ActualKnownSideInteriorSeed
import Calderon.CollaboratorUniqueContinuationProofOct17
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ExteriorSource
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift

theorem isCompact_actual_closed_physical_transfer_family
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L) (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    IsCompact (cylinder ∪ {x : R3 | ∃ i : Fin cover.count, ∃ y : R3,
      y ∈ cylinder ∩ (cover.packet i).centers ∧ ∃ z ∈ closedBall (0 : R3) 1,
        packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z = x}) := by
  classical
  -- One covering packet chosen at every cylinder center (total-function convention only).
  let choosePacket : ↥cylinder → Fin cover.count := fun y =>
    Classical.choose (cover.covers_cylinder y y.property)
  have hChoose (y : ↥cylinder) :
      (y : R3) ∈ (cover.packet (choosePacket y)).centers :=
    Classical.choose_spec (cover.covers_cylinder y y.property)
  let R := referenceRadius delta Rstar p L
  have hR : Continuous R :=
    (contDiff_referenceRadius_actual delta Rstar p L hdelta hRstar).continuous
  have hRpos (y : R3) : 0 < R y :=
    referenceRadius_pos delta Rstar p L y hdelta hRstar
  have hBall (z : ↥(closedBall (0 : R3) 1)) :
      (z : R3) ∈ closedBall (0 : R3) 2 :=
    closedBall_subset_closedBall (by norm_num) z.property
  -- The chosen actual endpoint on `cylinder × closedBall 1`.
  let F : ↥cylinder × ↥(closedBall (0 : R3) 1) → R3 := fun yz =>
    packetEndpoint S L (cover.packet (choosePacket yz.1)) lam yz.1 (R yz.1) yz.2
  -- Each fixed packet endpoint is continuous from its original globally smooth endpoint.
  have hPacket (i : Fin cover.count) : Continuous
      (fun yz : ↥cylinder × ↥(closedBall (0 : R3) 1) =>
        packetEndpoint S L (cover.packet i) lam yz.1 (R yz.1) yz.2) := by
    let P := cover.packet i
    have hTheta : ContDiff ℝ ∞
        (fun v : ℝ × (R3 × R3) => (P.Phi v.1 v.2 1).1) :=
      P.native_data.1.1.1.2.2.2.2.2.2.2.1
    have hX :=
      (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi
        hTheta).continuous
    have hy : Continuous (fun yz : ↥cylinder × ↥(closedBall (0 : R3) 1) =>
        (yz.1 : R3)) := continuous_subtype_val.comp continuous_fst
    have hz : Continuous (fun yz : ↥cylinder × ↥(closedBall (0 : R3) 1) =>
        (yz.2 : R3)) := continuous_subtype_val.comp continuous_snd
    first
    | exact hX.comp (continuous_const.prodMk ((hy.prodMk (hR.comp hy)).prodMk hz))
    | exact continuous_fst.comp
        ((hX.comp (continuous_const.prodMk ((hy.prodMk (hR.comp hy)).prodMk hz))).prodMk hy)
  -- Coherent relative gluing: near each center one valid packet stays valid.
  have hF : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro yz
    let i := choosePacket yz.1
    have hNear : ∀ᶠ yz' : ↥cylinder × ↥(closedBall (0 : R3) 1) in 𝓝 yz,
        (yz'.1 : R3) ∈ (cover.packet i).centers :=
      ((cover.packet i).centers_open.preimage
        (continuous_subtype_val.comp continuous_fst)).mem_nhds (hChoose yz.1)
    apply (hPacket i).continuousAt.congr_of_eventuallyEq
    filter_upwards [hNear] with yz' hy'
    change packetEndpoint S L (cover.packet (choosePacket yz'.1)) lam
      yz'.1 (R yz'.1) yz'.2 = _
    exact cover.endpoint_coherence (choosePacket yz'.1) i lam hLam yz'.1
      ⟨hChoose yz'.1,hy'⟩ (R yz'.1) (hRpos yz'.1)
      (hRadius yz'.1 yz'.1.property) yz'.2 (hBall yz'.2)
  have hc : IsCompact (Set.univ : Set ↥cylinder) :=
    isCompact_univ_iff.mpr (isCompact_iff_compactSpace.mp isCompact_native_center_cylinder)
  have hb : IsCompact (Set.univ : Set ↥(closedBall (0 : R3) 1)) :=
    isCompact_univ_iff.mpr (isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : R3) 1))
  have hCompact : IsCompact (Set.range F) := by
    simpa only [Set.univ_prod_univ, Set.image_univ] using (hc.prod hb).image hF
  -- The compact image is EXACTLY the literal physical family over all valid packets.
  have hRange : Set.range F = {x : R3 | ∃ i : Fin cover.count, ∃ y : R3,
      y ∈ cylinder ∩ (cover.packet i).centers ∧ ∃ z ∈ closedBall (0 : R3) 1,
        packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z = x} := by
    ext x
    constructor
    · rintro ⟨yz,rfl⟩
      exact ⟨choosePacket yz.1,yz.1,⟨yz.1.property,hChoose yz.1⟩,
        yz.2,yz.2.property,rfl⟩
    · rintro ⟨i,y,hy,z,hz,rfl⟩
      refine ⟨(⟨y,hy.1⟩,⟨z,hz⟩),?_⟩
      change packetEndpoint S L (cover.packet (choosePacket ⟨y,hy.1⟩)) lam
        y (R y) z = _
      exact cover.endpoint_coherence (choosePacket ⟨y,hy.1⟩) i lam hLam y
        ⟨hChoose ⟨y,hy.1⟩,hy.2⟩ (R y) (hRpos y) (hRadius y hy.1) z
        (hBall ⟨z,hz⟩)
  have hUnion := isCompact_native_center_cylinder.union hCompact
  rwa [hRange] at hUnion

/-- Function-germ congruence of the coordinate flux divergence: equal germs of the scalar test
at `x` give equal divergence at `x`, for the SAME metric. -/
theorem originalSourceTransfer_coordinateFluxDivergence_congr_of_eventuallyEq
    (g : MatrixField) (u w : R3 → ℝ) (x : R3) (h : u =ᶠ[𝓝 x] w) :
    coordinateFluxDivergence (metricDivergenceFlux g u) x =
      coordinateFluxDivergence (metricDivergenceFlux g w) x := by
  have hFlux : metricDivergenceFlux g u =ᶠ[𝓝 x] metricDivergenceFlux g w := by
    filter_upwards [h.gradient] with y hy
    change matrixOperatorMap (Real.sqrt (g y).det • (g y)⁻¹) (gradient u y) =
      matrixOperatorMap (Real.sqrt (g y).det • (g y)⁻¹) (gradient w y)
    rw [hy]
  unfold coordinateFluxDivergence
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun y => metricDivergenceFlux g u y i) =ᶠ[𝓝 x]
      (fun y => metricDivergenceFlux g w y i) :=
    hFlux.mono (fun y hy => congrArg (fun v : R3 => v i) hy)
  exact congrArg (fun A : R3 →L[ℝ] ℝ => A (NormalCoordinatesFrame.coordinateVector i))
    hi.fderiv_eq

theorem exists_global_native_density_original_source_reproduction
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    ∃ Psi : R3 → SphereSobolev (3/2 : ℝ), ContDiff ℝ ∞ Psi ∧ HasCompactSupport Psi ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers, ∀ u : SmoothData,
        (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
          (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u y =
          nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
            y (referenceRadius delta Rstar p L y) y) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        lam • y ∈ S.W → ∀ u : SmoothData,
        (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
          (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z) = 0) →
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi u y = u.1 y) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        ∀ (V : Set R3), IsOpen V → ∀ u : SmoothData,
        packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
          closedBall (0 : R3) 1 ⊆ V →
        (∀ x ∈ V, coordinateFluxDivergence (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) →
        ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
          ContDiffOn ℝ ∞ (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
            lam delta Rstar p Psi u) Y ∧
          ∀ z ∈ Y, normalizedSecondLaplacian S.g1 S.g2 L lam
            (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i) lam delta Rstar p Psi u) z = 0 ) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        referencePhysicalDensityOperator S.g1 L (cover.packet i).y0 (cover.packet i).Phi
          (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          S.g1_admissible hcalc hF hO hD τ0 S.g2 lam
          (referenceRadius delta Rstar p L) Psi y = 0 ) ∧
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi (⟨fun _ => (1 : ℝ),contDiff_const⟩ : SmoothData) y = 1 ) ∧
      (∀ V : Set R3, IsOpen V → ∀ u : SmoothData,
        (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
            closedBall (0 : R3) 1 ⊆ V) →
        (∀ x ∈ V, coordinateFluxDivergence
          (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) →
        ∀ v : SmoothData,
        (∀ y ∈ interior cylinder, coordinateFluxDivergence
          (metricDivergenceFlux (fun z => S.g2 (lam • z)) v.1) y = 0) →
        (∀ y ∈ cylinder, lam • y ∈ S.W → u.1 y = v.1 y) →
        ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
            lam delta Rstar p Psi u y = v.1 y) ∧
      (∀ k : Fin 3, ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi
          (⟨fun z : R3 => z k, (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff⟩ : SmoothData) y = y k) ∧
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
        (∀ y ∈ cylinder, S.Xi1 (lam • y) ∉ tsupport s) →
        (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          ∀ z ∈ closedBall (0 : R3) 1, S.Xi1 (lam • packetEndpoint S L (cover.packet i)
            lam y (referenceRadius delta Rstar p L y) z) ∉ tsupport s) →
        (∀ y ∈ cylinder, S.Xi2 (lam • y) ∉ tsupport s) →
        (∀ y ∈ cylinder, lam • y ∈ S.W →
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s
            (S.Xi1 (lam • y)) =
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s
            (S.Xi2 (lam • y))) →
        ∃ u v : SmoothData, HasCompactSupport u.1 ∧ HasCompactSupport v.1 ∧
          (∀ y ∈ cylinder, u.1 =ᶠ[𝓝 y] (fun x => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 (lam • x)))) ∧
          (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
            ∀ z ∈ closedBall (0 : R3) 1,
            u.1 =ᶠ[𝓝 (packetEndpoint S L (cover.packet i) lam y
              (referenceRadius delta Rstar p L y) z)] (fun x => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 (lam • x)))) ∧
          (∀ y ∈ cylinder, v.1 =ᶠ[𝓝 y] (fun x => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 (lam • x)))) ∧
          ∃ V : Set R3, IsOpen V ∧
            (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
                closedBall (0 : R3) 1 ⊆ V) ∧
            (∀ x ∈ V, coordinateFluxDivergence
              (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) ∧
            ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
              nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
                lam delta Rstar p Psi u y =
              radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s
                (S.Xi2 (lam • y)) := by
  -- The SAME coordinate producer: one `Psi` with every old field.
  obtain ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,hOperator,hMass,hPair,hCoord⟩ :=
    exists_global_native_density_normalized_paired_and_coordinate_reproduction
      hcalc hreg hF hO hD τ0 hKernel S L lam delta Rstar bound separation p cover K
      hdelta hRstar hlam hlamRoom hRadius
  refine ⟨Psi,hPsi,hCompact,hRep,hKnown,hPDE,hOperator,hMass,hPair,hCoord,?_⟩
  intro s hCyl1 hBall1 hCyl2 hMatch
  have hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling := ⟨hlam.le,hlamRoom⟩
  have hdil : ContDiff ℝ ∞ (fun y : R3 => lam • y) :=
    (lam • ContinuousLinearMap.id ℝ R3).contDiff
  -- Actual rooms: every closed physical ball point and every cylinder center.
  have hBallRoom : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ z ∈ closedBall (0 : R3) 1, lam • packetEndpoint S L (cover.packet i) lam y
        (referenceRadius delta Rstar p L y) z ∈ S.coordinateRoom := by
    intro i y hy z hz
    exact cover.coordinate_room i lam hLam y hy.2 (referenceRadius delta Rstar p L y)
      (referenceRadius_pos delta Rstar p L y hdelta hRstar) (hRadius y hy.1) z
      (closedBall_subset_closedBall (by norm_num) hz)
  have hCenter : ∀ y ∈ cylinder, lam • y ∈ S.coordinateRoom := by
    intro y hy
    obtain ⟨i,hi⟩ := cover.covers_cylinder y hy
    have he0 : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : R3) ∈ sphere (0 : R3) 1 := by
      first
      | simp
      | rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_single, norm_one]
    obtain ⟨-,hy2,-⟩ := K.domain_room (K.sphere_cover i y ⟨hy,hi⟩ _ he0)
    exact hy2
  -- The literal transported original responses, smooth on the dilated coordinate room.
  let a1 : R3 → ℝ := fun x => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
    S.original1_admissible s (S.Xi1 (lam • x))
  let a2 : R3 → ℝ := fun x => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2
    S.original2_admissible s (S.Xi2 (lam • x))
  let D : Set R3 := (fun x : R3 => lam • x) ⁻¹' S.coordinateRoom
  have ha1 : ContDiffOn ℝ ∞ a1 D :=
    ((radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original1
      S.original1_admissible s).2.1.comp S.Xi1_smooth S.Xi1_room).comp
        hdil.contDiffOn (fun x hx => hx)
  have ha2 : ContDiffOn ℝ ∞ a2 D :=
    ((radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original2
      S.original2_admissible s).2.1.comp S.Xi2_smooth S.Xi2_room).comp
        hdil.contDiffOn (fun x hx => hx)
  -- Source-free open rooms.
  have hT : IsOpen (tsupport s)ᶜ := (isClosed_tsupport _).isOpen_compl
  let U1 : Set R3 := (fun x : R3 => lam • x) ⁻¹'
    (S.coordinateRoom ∩ S.Xi1 ⁻¹' (tsupport s)ᶜ)
  let U2 : Set R3 := (fun x : R3 => lam • x) ⁻¹'
    (S.coordinateRoom ∩ S.Xi2 ⁻¹' (tsupport s)ᶜ)
  have hU1 : IsOpen U1 :=
    (S.Xi1_smooth.continuousOn.isOpen_inter_preimage S.coordinateRoom_open hT).preimage
      hdil.continuous
  have hU2 : IsOpen U2 :=
    (S.Xi2_smooth.continuousOn.isOpen_inter_preimage S.coordinateRoom_open hT).preimage
      hdil.continuous
  have hU1D : U1 ⊆ D := Set.preimage_mono Set.inter_subset_left
  have hU2D : U2 ⊆ D := Set.preimage_mono Set.inter_subset_left
  -- The compact literal physical family `A` lies in `U1`.
  let A : Set R3 := cylinder ∪ {x : R3 | ∃ i : Fin cover.count, ∃ y : R3,
    y ∈ cylinder ∩ (cover.packet i).centers ∧ ∃ z ∈ closedBall (0 : R3) 1,
      packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z = x}
  have hA : IsCompact A :=
    isCompact_actual_closed_physical_transfer_family S L lam delta Rstar p cover
      hdelta hRstar hLam hRadius
  have hCylA : ∀ y ∈ cylinder, y ∈ A := fun y hy => Set.mem_union_left _ hy
  have hFam : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ z ∈ closedBall (0 : R3) 1,
        packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z ∈ A :=
    fun i y hy z hz => Set.mem_union_right _ ⟨i,y,hy,z,hz,rfl⟩
  have hAU1 : A ⊆ U1 := by
    rintro x (hx | ⟨i,y,hy,z,hz,rfl⟩)
    · exact ⟨hCenter x hx,hCyl1 x hx⟩
    · exact ⟨hBallRoom i y hy z hz,hBall1 i y hy z hz⟩
  have hCylU2 : cylinder ⊆ U2 := fun y hy => ⟨hCenter y hy,hCyl2 y hy⟩
  -- ONE compact globally smooth cutoff per response, with exact germs.
  obtain ⟨u,huCompact,huGerm⟩ :=
    exists_smoothData_eq_near_compact A U1 hA hU1 hAU1 a1 (ha1.mono hU1D)
  obtain ⟨v,hvCompact,hvGerm⟩ :=
    exists_smoothData_eq_near_compact cylinder U2 isCompact_native_center_cylinder hU2 hCylU2
      a2 (ha2.mono hU2D)
  -- The common first harmonic test room.
  have hG : IsOpen {x : R3 | u.1 =ᶠ[𝓝 x] a1} := by
    first
    | exact isOpen_setOfPred_eventually_nhds
    | exact isOpen_iff_mem_nhds.mpr fun x hx => Filter.Eventually.eventually_nhds hx
  let V : Set R3 := U1 ∩ {x : R3 | u.1 =ᶠ[𝓝 x] a1}
  have hVopen : IsOpen V := hU1.inter hG
  have hVball : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) ''
        closedBall (0 : R3) 1 ⊆ V := by
    rintro i y hy _ ⟨z,hz,rfl⟩
    exact ⟨hAU1 (hFam i y hy z hz),huGerm _ (hFam i y hy z hz)⟩
  -- First physical PDE of `u` on `V`: germ congruence and the original-source dictionary.
  have huPDE : ∀ x ∈ V, coordinateFluxDivergence
      (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0 := by
    intro x hx
    have hxU : lam • x ∈ S.coordinateRoom ∩ S.Xi1 ⁻¹' (tsupport s)ᶜ := hx.1
    have hxG : u.1 =ᶠ[𝓝 x] a1 := hx.2
    exact (originalSourceTransfer_coordinateFluxDivergence_congr_of_eventuallyEq
      (fun z => S.g1 (lam • z)) u.1 a1 x hxG).trans
        (coordinateFluxDivergence_dilated_original_first_sourceResponse_eq_zero
          S lam s x hxU.1 hxU.2)
  -- Second physical PDE of `v` on the cylinder interior.
  have hvPDE : ∀ y ∈ interior cylinder, coordinateFluxDivergence
      (metricDivergenceFlux (fun z => S.g2 (lam • z)) v.1) y = 0 := by
    intro y hy
    have hyc : y ∈ cylinder := interior_subset hy
    exact (originalSourceTransfer_coordinateFluxDivergence_congr_of_eventuallyEq
      (fun z => S.g2 (lam • z)) v.1 a2 y (hvGerm y hyc)).trans
        (coordinateFluxDivergence_dilated_original_second_sourceResponse_eq_zero
          S lam s y (hCenter y hyc) (hCyl2 y hyc))
  -- Known-side matching from the two center germs and the original response matching.
  have hKnownMatch : ∀ y ∈ cylinder, lam • y ∈ S.W → u.1 y = v.1 y := by
    intro y hy hW
    have h1 : u.1 y = a1 y := (huGerm y (hCylA y hy)).eq_of_nhds
    have h2 : v.1 y = a2 y := (hvGerm y hy).eq_of_nhds
    have h12 : a1 y = a2 y := hMatch y hy hW
    exact h1.trans (h12.trans h2.symm)
  refine ⟨u,v,huCompact,hvCompact,fun y hy => huGerm y (hCylA y hy),
    fun i y hy z hz => huGerm _ (hFam i y hy z hz),hvGerm,V,hVopen,hVball,huPDE,?_⟩
  -- The SAME Psi universal paired reproduction.
  intro i y hy
  exact (hPair V hVopen u hVball huPDE v hvPDE hKnownMatch i y hy).trans
    (hvGerm y hy.1).eq_of_nhds

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
