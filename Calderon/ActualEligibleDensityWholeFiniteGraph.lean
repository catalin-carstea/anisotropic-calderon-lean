import Calderon.ActualWholeCoverFinitePhysicalOutputGraph
import Calderon.ActualSameCutoffNormalizedFiniteCore
import Calderon.ActualEligibleDensityWholeCoverOutput
import Calderon.ActualAnyEligiblePsiNormalizedSourceJets
import Calderon.ActualNativeCutoffHalfLift
import Calderon.ActualNormalizedCutoffOperatorDictionary
import Calderon.SphereSobolevHalfWeightedGraphLowering
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConformalDepth ActualScalarPrincipalAdjoint ActualFiniteHarmonicCore WeightedBaseSpectral
  SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph PositiveSpectralCore
attribute [local irreducible] sphereSobolevInclusionL referencePhysicalDensityOperator harmonicSphereSubspace
  nativeNormalizedCutoffPhysicalOperator nativePacketPhysicalDensityOperator sphereSobolevConstantOne

theorem exists_uniform_original_eligible_density_whole_finite_physical_graph
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L:ℝ) (hL:0 < L) (cover:NativeNormalCover S L)
    (hCenter:∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho):
    ∃ p0:ℕ,2 ≤ p0 ∧ ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧
      ∀ p:ℕ,p0 ≤ p → ∀ lambda:ℝ,0 < lambda → lambda ≤ cover.dilationCeiling →
      ∀ delta:ℝ,0 < delta → delta ≤ 1 → ∀ Rstar:ℝ,0 < Rstar →
      ∀ eps:ℝ,0 ≤ eps → eps ≤ eps0 → CurrentRadiusBootstrap S L lambda delta Rstar eps p →
      (∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling) →
      ∀ bound separation:ℝ,∀ K:ConstructedMixedKernel S L lambda delta Rstar bound separation p cover,
      ∀ Psi:R3→SphereSobolev (3/2:ℝ),ContDiff ℝ ∞ Psi → HasCompactSupport Psi →
      RepresentsNativeMixedKernelDensity hO hD tau0 S L lambda delta Rstar bound separation p cover K Psi →
      ∀ chi:R3→ℝ,ContDiff ℝ ∞ chi → HasCompactSupport chi → tsupport chi⊆interior cylinder →
      (∀ n:ℕ,∃ A:smoothCompactFiniteSphereCore hO hD,
        (∀ y:R3,finiteCoreSobolevLift hO hD (3/2:ℝ) A y=
          sphereSobolevPartialSumL (3/2:ℝ) n (normalizedThreeHalfSourceField chi Psi y)) ∧
        tsupport (A:R3→SphereL2)⊆tsupport chi ∧ ∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0) ∧
      ∃ (F:ℕ→R3→SphereL2) (f:R3→SphereL2),
      (∀ n:ℕ,ContDiff ℝ ∞ (F n) ∧ HasCompactSupport (F n) ∧ tsupport (F n)⊆tsupport chi ∧
        ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
          sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F n y))=
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p
            (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (normalizedThreeHalfSourceField chi Psi z)) i y) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f⊆tsupport chi ∧
      (∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (f y))=
          nativeNormalizedCutoffPhysicalOperator hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y) ∧
      Tendsto (fun n:ℕ => ∫ y,ReferenceDensityBounds.referenceDensityFamily S.g1 L (lambda,y)*‖F n y-f y‖^2) atTop (𝓝 0) := by
  obtain ⟨p0,hp0,eps0,heps0,heps01,HOutput⟩ := exists_native_cover_uniform_actual_whole_finite_physical_graph
    hcalc hreg hF hO hD tau0 hKernel S L hL cover hCenter
  refine ⟨p0,hp0,eps0,heps0,heps01,?_⟩
  intro p hp lambda hlam hlamRoom delta hd hd1 Rstar hRs eps heps heps0' hBoot hRadius
    bound separation K Psi hPsi hPsic hRep chi hchi hchic hSupp
  have hLam:lambda∈Icc (0:ℝ) cover.dilationCeiling := ⟨hlam.le,hlamRoom⟩
  obtain ⟨Psi5,hPsi5,hPsi5c,hInc,hSame⟩ := exists_fiveHalf_lift_of_eligible_native_density
    hcalc hreg hF hO hD tau0 S L lambda delta Rstar bound separation p cover K hd hRs hLam hRadius
    Psi hPsi hPsic hRep chi hSupp
  have hMean0 := (sphereMean_any_eligible_native_density_and_cutoff_sub_one hcalc hreg hF hO hD tau0 hKernel
    S L lambda delta Rstar bound separation p cover K hd hRs hlam hlamRoom hRadius Psi hPsi hPsic hRep chi hSupp).2
  have hProps:=normalizedFiveHalfSourceField_properties hO hD chi hchi hchic hSupp Psi Psi5 hPsi5 hInc hMean0
  let V5:=normalizedFiveHalfSourceField chi Psi5
  have hV5:ContDiff ℝ ∞ V5 := hProps.1
  have hV5c:HasCompactSupport V5 := hProps.2.1
  have hLow:(fun y => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (V5 y))=
      normalizedThreeHalfSourceField chi Psi := hProps.2.2.1
  have hV5Supp:tsupport V5⊆tsupport chi := hProps.2.2.2.1
  have hCore (n:ℕ):=exists_meanZero_finiteCore_normalized_fiveHalf_source hO hD chi hchi hchic hSupp
    Psi Psi5 hPsi5 hInc hMean0 n
  refine ⟨hCore,?_⟩
  have hAll:=HOutput p hp lambda hLam delta hd hd1 Rstar hRs eps heps heps0' hBoot
  have hGraphChoice:=hAll.2 V5 hV5 hV5c (hV5Supp.trans hSupp)
  let F:ℕ→R3→SphereL2 := Classical.choose hGraphChoice
  have hFChoice:=Classical.choose_spec hGraphChoice
  let f:R3→SphereL2 := Classical.choose hFChoice
  have hData:=Classical.choose_spec hFChoice
  refine ⟨F,f,?_,hData.2.1,hData.2.2.1,hData.2.2.2.1.trans hV5Supp,?_,hData.2.2.2.2.2⟩
  · intro n
    have hn:=hData.1 n
    refine ⟨hn.1,hn.2.1,hn.2.2.1.trans hV5Supp,?_⟩
    intro i y hy
    have hPartial:(fun z => sphereSobolevPartialSumL (3/2:ℝ) n
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (V5 z)))=
        (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (normalizedThreeHalfSourceField chi Psi z)) :=
      congrArg (fun v:R3→SphereSobolev (3/2:ℝ) => fun z => sphereSobolevPartialSumL (3/2:ℝ) n (v z)) hLow
    exact (hn.2.2.2 i y hy).trans (congrArg (fun v:R3→SphereSobolev (3/2:ℝ) =>
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p v i y) hPartial)
  · intro i y hy
    have hSource:=congrArg (fun v:R3→SphereSobolev (3/2:ℝ) =>
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p v i y) hLow
    exact (hData.2.2.2.2.1 i y hy).trans (hSource.trans
      (nativePacketPhysicalDensityOperator_normalized_source hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
