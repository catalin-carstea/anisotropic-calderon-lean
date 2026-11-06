import Calderon.ActualWholeCoverPhysicalHalfOutput
import Calderon.ActualAnyEligiblePsiNormalizedSourceJets
import Calderon.ActualNativeCutoffHalfLift
import Calderon.ActualNormalizedCutoffOperatorDictionary
import Calderon.SphereSobolevHalfWeightedGraphLowering
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConformalDepth ActualScalarPrincipalAdjoint ActualFiniteHarmonicCore WeightedBaseSpectral
attribute [local irreducible] sphereSobolevInclusionL referencePhysicalDensityOperator harmonicSphereSubspace
  nativeNormalizedCutoffPhysicalOperator nativePacketPhysicalDensityOperator sphereSobolevConstantOne

theorem nativePacketPhysicalDensityOperator_normalized_source
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics)
    (hD:DenseSphereHarmonics) (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L:ℝ)
    (cover:NativeNormalCover S L) (chi:R3→ℝ) (lambda delta Rstar:ℝ) (p:ℕ)
    (Psi:R3→SphereSobolev (3/2:ℝ)) (i:Fin cover.count) (y:R3):
    nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p
      (normalizedThreeHalfSourceField chi Psi) i y=
      nativeNormalizedCutoffPhysicalOperator hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y := by
  unfold nativePacketPhysicalDensityOperator
  exact (nativeNormalizedCutoffPhysicalOperator_eq_original_normalizedSource
    hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y).symm

theorem exists_uniform_original_eligible_density_whole_cover_physical_output
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
      ∃ W:R3→SphereL2,ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧ tsupport W⊆tsupport chi ∧
        ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
          sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (W y))=
          nativeNormalizedCutoffPhysicalOperator hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y := by
  obtain ⟨p0,hp0,eps0,heps0,heps01,HOutput⟩ := exists_native_cover_uniform_global_physical_half_output
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
  obtain ⟨WH,hWH,hWHc,hWHSupp,hGraph⟩ := HOutput p hp lambda hLam delta hd hd1 Rstar hRs eps heps heps0' hBoot
    V5 hV5 hV5c (hV5Supp.trans hSupp)
  let T:=sphereSobolevHalfToSphereL2L hO hD
  let W:R3→SphereL2 := fun y => T (WH y)
  have hW:ContDiff ℝ ∞ W := T.contDiff.comp hWH
  have hWc:HasCompactSupport W := hWHc.comp_left (map_zero T)
  have hWSupp:tsupport W⊆tsupport chi :=
    (tsupport_comp_subset (map_zero T) WH).trans (hWHSupp.trans hV5Supp)
  refine ⟨W,hW,hWc,hWSupp,?_⟩
  intro i y hy
  have hSource:=congrArg (fun v:R3→SphereSobolev (3/2:ℝ) =>
    nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p v i y) hLow
  have hCompat:=sphereSobolevHalfToSphereL2L_negative_compatibility hO hD (WH y)
  change sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
    (sphereSobolevZeroEquiv hO hD (T (WH y)))=_
  exact hCompat.trans ((hGraph i y hy).trans (hSource.trans
    (nativePacketPhysicalDensityOperator_normalized_source hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y)))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
