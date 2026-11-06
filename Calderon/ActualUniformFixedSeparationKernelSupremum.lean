import Calderon.ActualCanonicalTubeBudgetConsumer
import Calderon.ActualUniformExistingCoarseConeBudget
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

theorem exists_uniform_fixed_separation_existing_kernel_supremum_budget
    (S:KnownSideSourceData) (B d:ℝ) (hB:0 < B) (hd:0 < d):
    ∃ Bbig dbig lambda0 N:ℝ,0 < Bbig ∧ 0 < dbig ∧ 0 < lambda0 ∧ 0 < N ∧
      ∀ L lambda:ℝ,lambda∈Ioc (0:ℝ) lambda0 → ∀ (Omega:Set (R3×R3)) (F:R3×R3→ℝ),
      Omega⊆dilatedOffDiagonal S lambda → ProductSolutionOn S L lambda F Omega →
      (∀ z∈Omega,lambda • z.2∈S.W → F z=dilatedKernel1 S lambda z) →
      (∀ z∈Omega,lambda • z.1∈S.W → F z=dilatedKernel2 S lambda z) →
      fixedSeparationSet Bbig dbig⊆Omega → ∀ x∈fixedSeparationSet B d,‖F x‖ ≤ N := by
  obtain ⟨c0,hc0,HC⟩ := uniform_coarse_cone_supremum_budget_of_existing_full_cross_solution S
  let eta:ℝ := min (1/10:ℝ) (c0/13)
  have heta:0 < eta := lt_min (by norm_num) (div_pos hc0 (by norm_num))
  have heta10:eta ≤ 1/10 := min_le_left _ _
  have hc0eta:13*eta ≤ c0 := by have hh:eta ≤ c0/13 := min_le_right _ _;linarith only [hh]
  let M:ℝ := B+4
  have hM:B+3 < M := by dsimp only [M];linarith
  obtain ⟨sigma,T0,e0,hsigma,hsigmaEta,hsigma1,hT0,hTop,he0,he01,hGap,hStrict⟩ :=
    tube_native_strict_sweep_base_pos hc0 heta heta10 hc0eta hd hB.le hM
  obtain ⟨CY,hCY,hP,hCenter⟩ := tube_center_room he0 hM
  let amin:ℝ := min 1 (d/(2*(M+B+B^2)^2))
  let lower:ℝ := amin/4
  let upper:ℝ := (2/c0+1)*max 1 T0^2+2*B+3
  obtain ⟨hamin,hLowerA,hLower,hLowerD,hUpper,hUpperB⟩ := tube_room_constants (T0:=T0) hc0 hd hB.le hM
  have hUpperPos:0 < upper := by dsimp only [upper];positivity
  obtain ⟨Bro,hBro,hRoomBound⟩ := interiorTubeRoom_subset_fixedSeparationSet M e0 B T0 CY lower upper hCY hLower hUpperPos
  obtain ⟨lBand,Cband,hlBand,hCband,HBand⟩ := exists_uniform_canonical_unseeded_tube_band_budget S
    M e0 sigma c0 B T0 amin CY lower upper hc0 hB.le hM he0 hsigma.le hsigma1 hamin hLowerA hUpper hTop
    (fun Y hY hT => (hCenter Y hY hT).1) hStrict
  let Bcoarse:ℝ := max Bro B
  have hBcoarse:0 < Bcoarse := hBro.trans_le (le_max_left _ _)
  obtain ⟨Bc,dc,lc,Nc,hBc,hdc,hlc,hNc,HCoarse⟩ := HC Bcoarse lower hBcoarse hLower
  let Bbig:ℝ := max Bc (max Bro B)
  let dbig:ℝ := min dc lower
  let lambda0:ℝ := min lc lBand
  let N:ℝ := max Nc (Cband*Nc)
  refine ⟨Bbig,dbig,lambda0,N,hBc.trans_le (le_max_left _ _),lt_min hdc hLower,
    lt_min hlc hlBand,hNc.trans_le (le_max_left _ _),?_⟩
  intro L lambda hlam Omega F hOmega hF hF1 hF2 hBig
  have hlamC:lambda∈Ioc (0:ℝ) lc := ⟨hlam.1,hlam.2.trans (min_le_left _ _)⟩
  have hlamBand:lambda∈Icc (0:ℝ) lBand := ⟨hlam.1.le,hlam.2.trans (min_le_right _ _)⟩
  have hCoarseCover:fixedSeparationSet Bc dc⊆Omega := by
    intro z hz
    apply hBig
    exact ⟨hz.1.trans (le_max_left _ _),hz.2.1.trans (le_max_left _ _),(min_le_left _ _).trans hz.2.2⟩
  have hRoomCover:interiorTubeRoom M e0 B T0 CY lower upper⊆Omega := by
    intro z hz
    have hh:=hRoomBound hz
    apply hBig
    exact ⟨hh.1.trans ((le_max_left Bro B).trans (le_max_right _ _)),
      hh.2.1.trans ((le_max_left Bro B).trans (le_max_right _ _)),(min_le_right _ _).trans hh.2.2⟩
  have hSeedBudget:∀ z∈interiorTubeSeed M e0 c0 B T0 CY lower upper,‖F z‖ ≤ Nc := by
    intro z hz
    have hb:=hRoomBound hz.1
    exact HCoarse L lambda hlamC Omega F hOmega hF hF1 hF2 hCoarseCover z.1 z.2
      (hb.1.trans (le_max_left _ _)) (hb.2.1.trans (le_max_left _ _)) hb.2.2 hz.2
  have hFRoom:ProductSolutionOn S L lambda F (interiorTubeRoom M e0 B T0 CY lower upper) :=
    ⟨hF.1.mono hRoomCover,fun z hz => hF.2.1 z (hRoomCover hz),fun z hz => hF.2.2 z (hRoomCover hz)⟩
  intro z hz
  rcases fixedSeparationSet_subset_coarse_or_unseeded_tube_band M e0 sigma c0 B d T0 amin CY lower upper
    hc0 hB.le hM he0.le hsigma hT0 hamin hLowerD hUpperB hTop
    (fun Y hY hT => (hCenter Y hY hT).1) hGap z hz with hCone | hBand
  · exact (HCoarse L lambda hlamC Omega F hOmega hF hF1 hF2 hCoarseCover z.1 z.2
      (hz.1.trans (le_max_right _ _)) (hz.2.1.trans (le_max_right _ _))
      (hLowerD.le.trans hz.2.2) hCone).trans (le_max_left _ _)
  · exact (HBand L lambda hlamBand F hFRoom Nc hNc.le hSeedBudget z hBand).trans (le_max_right _ _)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
