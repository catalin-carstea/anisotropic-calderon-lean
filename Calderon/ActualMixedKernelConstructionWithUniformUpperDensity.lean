import Calderon.ActualMixedKernelConstructionWithSeed
import Calderon.ActualUpperAnnularSeedDensity
import Calderon.ActualUpperRadiusAnnulusGeometry
import Calderon.ActualMixedKernelGlobalNativeDensity
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter MeasureTheory ConnectionError ConformalDepth RadiusProfile
open scoped ContDiff Topology InnerProductSpace
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  MetricOperator MetricVolume ReferenceWeightedApproximation

/-- The ORIGINAL parameter order, now with one pre-δ seed/extension/bound and
an actual same-source global density profile for each constructed kernel. -/
def ActualMixedKernelConstructionWithUniformUpperDensityGoal
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) : Prop :=
  ∀ (S : KnownSideSourceData) (bound separation : ℝ), 0 < bound → 0 < separation →
  ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
  ∃ cover : NativeNormalCover S L,
  ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
  ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 ∧
  ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
  ∃ R0 : ℝ, 0 < R0 ∧ ∀ Rstar : ℝ, 0 < Rstar → Rstar ≤ R0 →
  ∃ lam0 : ℝ, 0 < lam0 ∧ lam0 ≤ cover.dilationCeiling ∧
  ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
  ∃ (R tail a b : ℝ) (Hseed Hext : R3 × R3 → ℝ),
    ∃ hHext : ContDiff ℝ ∞ Hext, ∃ B : ℝ,
    0 < R ∧ R < cover.radiusCeiling ∧ tail < a ∧ 0 < a ∧ b < R ∧
    HasCompactSupport Hext ∧
    (∀ q ∈ nativeMixedKernelAnnularSurface S L lam a b cover,
      Hext =ᶠ[𝓝 q] Hseed) ∧
    0 ≤ B ∧ ProductSolutionOn S L lam Hseed
      (nativeRadialSeedRoom S L cover lam R tail) ∧
    ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      CurrentRadiusBootstrap S L lam delta Rstar eps p →
      (∀ delta' ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder,
        referenceRadius delta' Rstar p L y < cover.radiusCeiling) ∧
      ∃ K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover,
        nativeRadialSeedRoom S L cover lam R tail ⊆ K.domain ∧
        EqOn K.kernel Hseed (nativeRadialSeedRoom S L cover lam R tail) ∧
        ∃ Psi : R3 → SphereSobolev (3/2 : ℝ),
          ContDiff ℝ ∞ Psi ∧ HasCompactSupport Psi ∧
          (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
            ∀ u : SmoothData,
              (∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
                (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
                  (packetEndpoint S L (cover.packet i) lam y
                    (referenceRadius delta Rstar p L y) z) = 0) →
              nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
                lam delta Rstar p Psi u y =
                nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1 y
                  (referenceRadius delta Rstar p L y) y) ∧
          (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
            (1/4 : ℝ) ≤ referenceCoordinateDepth y → ‖Psi y‖ ≤ B)

/-- No density norm is assumed: the single constant is constructed before δ. -/
theorem actualMixedKernelConstructionWithUniformUpperDensityGoal_of_producer
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (producer : FixedSeparationProductProducer) :
    ActualMixedKernelConstructionWithUniformUpperDensityGoal hcalc hreg hF hO hD τ0 := by
  classical
  intro S bound separation hBound hSep
  obtain ⟨L0,hL0,Hstrict⟩ := exists_native_global_front_strictness_parameters S
  obtain ⟨lB,hlB,Hboundary⟩ := exists_uniform_native_radial_seed_boundary_cover S
  refine ⟨L0,hL0,?_⟩
  intro L hL
  have hLpos : 0 < L := hL0.trans_le hL
  obtain ⟨C⟩ := v021_normal_packet_cover_exists S L hLpos
  obtain ⟨rSeed,c,Bn,hrSeed,hrSeedRoom,hc,hBn,HseedCover⟩ :=
    exists_native_radial_seed_euclidean_cover_parameters S L C
  obtain ⟨rSep,Ksep,hrSep,hrSepRoom,hKsep,Hsep⟩ := exists_native_normal_room_separation_upper S L C
  let R := min (min rSeed rSep) (separation/(4*Ksep))
  have hR : 0 < R := lt_min (lt_min hrSeed hrSep) (div_pos hSep (by positivity))
  have hRSeed : R ≤ rSeed := (min_le_left _ _).trans (min_le_left _ _)
  have hRSep : R ≤ rSep := (min_le_left _ _).trans (min_le_right _ _)
  have hRoom : R < C.radiusCeiling := hRSeed.trans_lt hrSeedRoom
  have hRDist : Ksep*R < separation/2 := by
    have hCap : R ≤ separation/(4*Ksep) := min_le_right _ _
    have hScale : R*(4*Ksep) ≤ separation := (le_div_iff₀ (by positivity)).mp hCap
    nlinarith only [hScale,hSep]
  obtain ⟨T,hT⟩ := exists_referenceDepth_upper_bound_on_cylinder L
  let tb := depthPrimitive L (1/8) (1/4)
  have htb : 0 < tb := depthPrimitive_quarter_pos L hLpos
  obtain ⟨p0,hp0,Hp⟩ := Hstrict L hL C R hR hRoom
  refine ⟨C,p0,hp0,?_⟩
  intro p hp
  obtain ⟨eps0,heps0,heps01,Heps⟩ := Hp p hp
  refine ⟨eps0,heps0,heps01,?_⟩
  intro eps heps hepsCap
  obtain ⟨R0source,hR0source,HRs⟩ := Heps eps heps.le hepsCap
  obtain ⟨R0ann,hR0ann,HAnn⟩ :=
    exists_referenceRadius_fixed_annulus_budget L T tb R p htb hR
  let R0 := min R0source R0ann
  have hR0 : 0 < R0 := lt_min hR0source hR0ann
  refine ⟨R0,hR0,?_⟩
  intro Rstar hRs hRstar
  have hRstarSource : Rstar ≤ R0source := hRstar.trans (min_le_left _ _)
  have hRstarAnn : Rstar ≤ R0ann := hRstar.trans (min_le_right _ _)
  let a := Rstar * tb ^ p
  let b := Rstar * ((Real.log (1 + Real.exp T)) ^ p + 1)
  have ha : 0 < a := mul_pos hRs (pow_pos htb p)
  have hAnn := HAnn Rstar hRs hRstarAnn
  have hb : b < R := by
    dsimp only [b]
    exact hAnn.2.2.1
  obtain ⟨tail0,htail0,htailMargin,Htail0⟩ := exists_native_radial_initial_seed_tail L Rstar p hLpos hRs
  let tail := min tail0 (R/4)
  have hTail : 0 < tail := lt_min htail0 (by positivity)
  have hTail0 : tail ≤ tail0 := min_le_left _ _
  have hTailRoom : tail < R := (min_le_right _ _).trans_lt (by linarith)
  have hTailMargin : tail < Rstar*(depthPrimitive L (1/8) (1/4))^p := hTail0.trans_lt htailMargin
  have hTailA : tail < a := hTailMargin
  have hTailTop : ∀ y ∈ cylinder, tail < referenceRadius 1 Rstar p L y := by
    intro y hy
    have hh := Htail0 y hy
    linarith only [hh,hTail0,htail0]
  let B := bound+Bn+1
  let d := min separation (c*tail)/2
  have hB : 0 < B := by dsimp only [B];positivity
  have hd : 0 < d := div_pos (lt_min hSep (mul_pos hc hTail)) (by norm_num)
  have hBOriginal : bound ≤ B := by dsimp only [B];linarith
  have hBNative : Bn ≤ B := by dsimp only [B];linarith
  have hdOriginal : d ≤ separation := by
    have hh : d ≤ separation/2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith
  have hdNative : d ≤ c*tail := by
    have hh : d ≤ (c*tail)/2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    nlinarith only [hh,hc,hTail]
  obtain ⟨lE,hlE,HE⟩ := producer S B d hB hd
  let lam0 := min C.dilationCeiling (min lB lE)
  have hlam0 : 0 < lam0 := lt_min C.dilation_positive (lt_min hlB hlE)
  have hlamC : lam0 ≤ C.dilationCeiling := min_le_left _ _
  refine ⟨lam0,hlam0,hlamC,?_⟩
  intro lam hlamPos hlamSmall
  have hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling := ⟨hlamPos.le,hlamSmall.trans hlamC⟩
  have hlamB : lam ≤ lB := hlamSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlamE : lam ≤ lE := hlamSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨E,H,hE,hERoom,hInitial,hFar,hESol,hE1,hE2⟩ := HE L lam hlamPos hlamE
  have hSeedE : nativeRadialSeedRoom S L C lam R tail ⊆ E := by
    intro q hq
    rcases HseedCover R hR hRSeed lam hlam tail hTail hq with hi | hf
    · exact hInitial hi
    · exact hFar ⟨hf.1.trans hBNative,hf.2.1.trans hBNative,hdNative.trans hf.2.2⟩
  have hSeedSol := productSolutionOn_mono hESol hSeedE
  have hSeed1 : ∀ q ∈ nativeRadialSeedRoom S L C lam R tail,
      lam • q.2 ∈ S.W → H q=dilatedKernel1 S lam q := fun q hq => hE1 q (hSeedE hq)
  have hSeed2 : ∀ q ∈ nativeRadialSeedRoom S L C lam R tail,
      lam • q.1 ∈ S.W → H q=dilatedKernel2 S lam q := fun q hq => hE2 q (hSeedE hq)
  obtain ⟨Hext,hHext,hHextCompact,hExtSeed⟩ :=
    exists_smooth_annular_seed_extension S L lam R tail a b C
      hlam hR hRoom hTailA ha hb H hSeedSol.1
  obtain ⟨B,hBnonneg,hB⟩ :=
    exists_uniform_nativeMixedKernelHighDensity_annular_bound
      hcalc hreg hF hO hD τ0 S L lam a b C Hext hHext
  refine ⟨R,tail,a,b,H,Hext,hHext,B,hR,hRoom,hTailA,ha,hb,
    hHextCompact,hExtSeed,hBnonneg,hSeedSol,?_⟩
  intro delta hdPos hdOne hBoot
  obtain ⟨hRadiusRoom,hRadiusR,_⟩ := HRs Rstar hRs hRstarSource lam hlam delta hdPos hdOne hBoot
  have hAllStrict : ∀ b ∈ Icc delta (1 : ℝ), ∀ q ∈ nativeSphereFront S L C lam b Rstar p,
      ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun y => S.g2 (lam • y))
        q.1 q.2 (nativeGlobalEnergy S L C lam R b Rstar p) := by
    intro b hb
    have hbPos : 0 < b := hdPos.trans_le hb.1
    have hbBoot := currentRadiusBootstrap_mono_delta S L lam delta b Rstar eps p
      hdPos hb.1 hRs.le heps.le hBoot
    obtain ⟨_,_,W,hW,hFront,hWRoom,hSmooth,hZero,hTests⟩ :=
      HRs Rstar hRs hRstarSource lam hlam b hbPos hb.2 hbBoot
    exact nativeSphereFront_strict_of_packet_tests S L C lam hlam R hR hRoom
      b Rstar p hbPos hRs (hRadiusR b hb) hTests
  have hAllBoundary : ∀ b ∈ Icc delta (1 : ℝ), ∀ q ∈ nativeSphereFront S L C lam b Rstar p,
      q.2 ∈ frontier cylinder → q ∈ nativeRadialSeedRoom S L C lam R tail := by
    intro b hb
    exact Hboundary L hLpos C lam hlamPos hlamB hlam R hR hRoom b Rstar
      (hdPos.trans_le hb.1) hRs p (hRadiusR b hb) tail hTailMargin
  have hReached := native_reached_all_levels_of_actual_strictness S L C lam hlam hlamPos R hR hRoom
    delta Rstar tail p hdPos hdOne hRs hTailRoom hRadiusR hTailTop hAllBoundary hAllStrict
    H hSeedSol hSeed1 hSeed2 delta ⟨le_rfl,hdOne⟩
  have hNativeSep : ∀ q ∈ nativeNonzeroNormalImage S L C lam R, ‖q.1-q.2‖ < separation/2 := by
    intro q hq
    exact (Hsep R hR hRSep lam hlam q hq.1 hq.2).2.trans hRDist
  have hFarOriginal : fixedSeparationSet bound separation ⊆ E := by
    intro q hq
    exact hFar ⟨hq.1.trans hBOriginal,hq.2.1.trans hBOriginal,hdOriginal.trans hq.2.2⟩
  obtain ⟨K,hKRoom,hKEq⟩ := exists_constructedMixedKernel_eq_seed_of_native_reached
    S L C lam hlam hlamPos R hR hRoom delta Rstar bound separation tail p
    hdPos hRs hSep (hRadiusR delta ⟨le_rfl,hdOne⟩) hNativeSep H hReached
    E hE hERoom hInitial hFarOriginal hESol hE1 hE2
  have hRadius : ∀ y ∈ cylinder,
      referenceRadius delta Rstar p L y < C.radiusCeiling :=
    hRadiusRoom delta ⟨le_rfl,hdOne⟩
  obtain ⟨Gext,hGext,Psi,hGextCompact,hPsiSmooth,hPsiCompact,hGermK,
      U,hU,hCU,hPsiPacket,hFlux⟩ :=
    exists_global_native_mixed_kernel_high_density_represents_physicalFlux
      hcalc hreg hF hO hD τ0 S L lam delta Rstar bound separation p C K
      hdPos hRs hlam hRadius
  have hRep (i : Fin C.count) (y : R3)
      (hy : y ∈ cylinder ∩ (C.packet i).centers) (u : SmoothData)
      (hu : ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1)
          (packetEndpoint S L (C.packet i) lam y
            (referenceRadius delta Rstar p L y) z) = 0) :
      nativeMixedKernelDensityFunctional hO hD τ0 S L (C.packet i)
        lam delta Rstar p Psi u y =
        nativeMixedKernelWronskianFlux S L (C.packet i) lam K.kernel u.1 y
          (referenceRadius delta Rstar p L y) y := by
    change ⟪(sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y)),
      τ0.valueTraceL (smoothSobolev (referencePhysicalPullbackData S.g1 S.g1_admissible L
        (C.packet i).y0 (C.packet i).Phi (C.packet i).B
        (C.packet i).native_data.1.1.1 lam y
        (referenceRadius delta Rstar p L y) u))⟫_ℝ = _
    exact hFlux i y hy u hu
  refine ⟨hRadiusRoom,K,hKRoom,hKEq,Psi,hPsiSmooth,hPsiCompact,hRep,?_⟩
  intro i y hy hCoord
  have hDepth : tb ≤ referenceDepth L y :=
    (depthPrimitive_strictMono L (1/8) hLpos).monotone hCoord
  have hAnnY := hAnn.2.2.2 delta hdPos hdOne y hy.1 hDepth (hT y hy.1)
  have hr : referenceRadius delta Rstar p L y ∈ Icc a b := by
    constructor
    · exact referenceRadius_lower_of_quarter_depth L delta Rstar p hLpos hdPos hRs.le y hCoord
    · exact hAnnY.2
  exact norm_actual_nativeMixedKernelDensity_le_of_annular_seed_germs
    hcalc hreg hF hO hD τ0 S L lam R tail a b C hlam hR hRoom
    hTailA ha hb H Hext hHext hExtSeed B hB delta Rstar bound separation p
    K hKEq Psi i y hy hr (fun u hu => hRep i y hy u hu)


theorem actual_mixed_kernel_exists_with_uniform_upper_density
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ActualMixedKernelConstructionWithUniformUpperDensityGoal hcalc hreg hF hO hD τ0 :=
  actualMixedKernelConstructionWithUniformUpperDensityGoal_of_producer
    hcalc hreg hF hO hD τ0 fixed_separation_product_producer

/-- The strengthened construction projects to the exact original goal. -/
theorem actualMixedKernelConstructionGoal_of_uniform_upper_density
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (h : ActualMixedKernelConstructionWithUniformUpperDensityGoal
      hcalc hreg hF hO hD τ0) : ActualMixedKernelConstructionGoal := by
  intro S bound separation hBound hSep
  obtain ⟨L0,hL0,hL⟩ := h S bound separation hBound hSep
  refine ⟨L0,hL0,?_⟩
  intro L hLL0
  obtain ⟨C,p0,hp0,hp⟩ := hL L hLL0
  refine ⟨C,p0,hp0,?_⟩
  intro p hpp0
  obtain ⟨eps0,heps0,heps01,heps⟩ := hp p hpp0
  refine ⟨eps0,heps0,heps01,?_⟩
  intro eps hepsPos hepsSmall
  obtain ⟨R0,hR0,hRstar⟩ := heps eps hepsPos hepsSmall
  refine ⟨R0,hR0,?_⟩
  intro Rstar hRs hRs0
  obtain ⟨lam0,hlam0,hlamC,hlam⟩ := hRstar Rstar hRs hRs0
  refine ⟨lam0,hlam0,hlamC,?_⟩
  intro lam hlamPos hlamSmall delta hdPos hdOne hBoot
  obtain ⟨R,tail,a,b,Hseed,Hext,hHext,B,hR,hRoom,hTailA,ha,hb,hCompact,
      hGerm,hBnonneg,hSeedSol,hDelta⟩ := hlam lam hlamPos hlamSmall
  obtain ⟨hRadius,K,hKRoom,hKEq,Psi,hPsiSmooth,hPsiCompact,hRep,hUpper⟩ :=
    hDelta delta hdPos hdOne hBoot
  exact ⟨hRadius,⟨K⟩⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
