import Calderon.ActualUniformFixedSeparationKernelSupremum
import Calderon.ActualUniformCompactInteriorJetEstimate
import Calderon.ActualFixedSeparationInteriorGeometry
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

theorem exists_uniform_fixed_separation_existing_kernel_joint_jet_budget
    (S:KnownSideSourceData) (B d:ℝ) (hB:0 < B) (hd:0 < d):
    ∃ Bbig dbig lambda0:ℝ,∃ C:ℕ→ℝ,0 < Bbig ∧ 0 < dbig ∧ 0 < lambda0 ∧ (∀ n,0 < C n) ∧
      ∀ L lambda:ℝ,lambda∈Ioc (0:ℝ) lambda0 → ∀ (Omega:Set (R3×R3)) (F:R3×R3→ℝ),
      Omega⊆dilatedOffDiagonal S lambda → ProductSolutionOn S L lambda F Omega →
      (∀ z∈Omega,lambda • z.2∈S.W → F z=dilatedKernel1 S lambda z) →
      (∀ z∈Omega,lambda • z.1∈S.W → F z=dilatedKernel2 S lambda z) →
      fixedSeparationSet Bbig dbig⊆Omega →
      ∀ n:ℕ,∀ z∈fixedSeparationSet B d,‖iteratedFDeriv ℝ n F z‖ ≤ C n := by
  obtain ⟨hU,hKU,hUFixed⟩ := fixedSeparationInteriorRoom_geometry B d hd
  obtain ⟨lj,hlj,Ksource,V,hKs,hKsU,hV,hKV,hVU,Cj,hCj,Hj⟩ :=
    exists_uniform_compact_interior_existing_product_jet_estimate S (fixedSeparationSet B d)
      (fixedSeparationInteriorRoom B d) (isCompact_fixedSeparationSet B d) hU hKU
  obtain ⟨Bs,ds,ls,Ns,hBs,hds,hls,hNs,Hs⟩ :=
    exists_uniform_fixed_separation_existing_kernel_supremum_budget S (B+1) (d/2) (by positivity) (half_pos hd)
  let Bbig:ℝ := max Bs (B+1)
  let dbig:ℝ := min ds (d/2)
  let lambda0:ℝ := min lj ls
  let C:ℕ→ℝ := fun n => Cj n*Ns
  refine ⟨Bbig,dbig,lambda0,C,hBs.trans_le (le_max_left _ _),lt_min hds (half_pos hd),
    lt_min hlj hls,(fun n => mul_pos (hCj n) hNs),?_⟩
  intro L lambda hlam Omega F hOmega hF hF1 hF2 hBig
  have hSupCover:fixedSeparationSet Bs ds⊆Omega := by
    intro z hz
    exact hBig ⟨hz.1.trans (le_max_left _ _),hz.2.1.trans (le_max_left _ _),(min_le_left _ _).trans hz.2.2⟩
  have hRoomCover:fixedSeparationInteriorRoom B d⊆Omega := by
    intro z hz
    have hh:=hUFixed hz
    exact hBig ⟨hh.1.trans (le_max_right _ _),hh.2.1.trans (le_max_right _ _),(min_le_right _ _).trans hh.2.2⟩
  have hFRoom:ProductSolutionOn S L lambda F (fixedSeparationInteriorRoom B d) :=
    ⟨hF.1.mono hRoomCover,fun z hz => hF.2.1 z (hRoomCover hz),fun z hz => hF.2.2 z (hRoomCover hz)⟩
  have hSup:=Hs L lambda ⟨hlam.1,hlam.2.trans (min_le_right _ _)⟩ Omega F hOmega hF hF1 hF2 hSupCover
  have hBudget:∀ z∈Ksource,‖F z‖ ≤ Ns := fun z hz => hSup z (hUFixed (hKsU hz))
  intro n z hz
  exact Hj L lambda ⟨hlam.1.le,hlam.2.trans (min_le_left _ _)⟩ F hFRoom Ns hNs.le hBudget n z (hKV hz)

theorem fixed_separation_product_producer_with_uniform_joint_jets
    (S:KnownSideSourceData) (B d:ℝ) (hB:0 < B) (hd:0 < d):
    ∃ lambda0:ℝ,∃ C:ℕ→ℝ,0 < lambda0 ∧ (∀ n,0 < C n) ∧
      ∀ L lambda:ℝ,0 < lambda → lambda ≤ lambda0 →
      ∃ (Omega:Set (R3×R3)) (F:R3×R3→ℝ),IsOpen Omega ∧
        Omega⊆dilatedOffDiagonal S lambda ∧ initialCross S lambda⊆Omega ∧
        fixedSeparationSet B d⊆Omega ∧ ProductSolutionOn S L lambda F Omega ∧
        (∀ z∈Omega,lambda • z.2∈S.W → F z=dilatedKernel1 S lambda z) ∧
        (∀ z∈Omega,lambda • z.1∈S.W → F z=dilatedKernel2 S lambda z) ∧
        ∀ n:ℕ,∀ z∈fixedSeparationSet B d,‖iteratedFDeriv ℝ n F z‖ ≤ C n := by
  obtain ⟨Bj,dj,lj,C,hBj,hdj,hlj,hC,Hj⟩ :=
    exists_uniform_fixed_separation_existing_kernel_joint_jet_budget S B d hB hd
  let Bprod:ℝ := max Bj B
  let dprod:ℝ := min dj d
  obtain ⟨lp,hlp,Hp⟩ := fixed_separation_product_producer S Bprod dprod
    (hBj.trans_le (le_max_left _ _)) (lt_min hdj hd)
  refine ⟨min lj lp,C,lt_min hlj hlp,hC,?_⟩
  intro L lambda hlam hlam0
  obtain ⟨Omega,F,hO,hRoom,hInitial,hCover,hF,hF1,hF2⟩ := Hp L lambda hlam (hlam0.trans (min_le_right _ _))
  have hJetCover:fixedSeparationSet Bj dj⊆Omega := by
    intro z hz
    exact hCover ⟨hz.1.trans (le_max_left _ _),hz.2.1.trans (le_max_left _ _),(min_le_left _ _).trans hz.2.2⟩
  have hTargetCover:fixedSeparationSet B d⊆Omega := by
    intro z hz
    exact hCover ⟨hz.1.trans (le_max_right _ _),hz.2.1.trans (le_max_right _ _),(min_le_right _ _).trans hz.2.2⟩
  exact ⟨Omega,F,hO,hRoom,hInitial,hTargetCover,hF,hF1,hF2,
    Hj L lambda ⟨hlam,hlam0.trans (min_le_left _ _)⟩ Omega F hRoom hF hF1 hF2 hJetCover⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
