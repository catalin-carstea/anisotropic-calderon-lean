import Calderon.ActualCompactBandBudgetFromLocalEstimates
import Calderon.ActualUniformExistingProductLocalJetEstimate
import Calderon.ActualMixedKernelConstruction
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

/-- The exact radial level already used in the original tube chart. -/
def tubeRadialLevel (M e0 sigma:ℝ) (z:R3×R3):ℝ :=
  ‖z.1-z.2‖/tubeHeight M e0 z.2^(1+sigma)

theorem continuousOn_tubeRadialLevel (M e0 sigma:ℝ) (U:Set (R3×R3))
    (hUt:U⊆{z | 0 < tubeHeight M e0 z.2}) : ContinuousOn (tubeRadialLevel M e0 sigma) U := by
  have ht:ContDiff ℝ ∞ (fun z:R3×R3 => tubeHeight M e0 z.2) := (st_height_contDiff M e0).comp contDiff_snd
  have hden:ContDiffOn ℝ ∞ (fun z:R3×R3 => tubeHeight M e0 z.2^(1+sigma)) U :=
    ht.contDiffOn.rpow_const_of_ne (fun z hz => (hUt hz).ne')
  exact (continuous_fst.sub continuous_snd).norm.continuousOn.div hden.continuousOn
    (fun z hz => (Real.rpow_pos_of_pos (hUt hz) _).ne')

theorem tubePhase_at_tubeRadialLevel_eq_zero (M e0 sigma:ℝ) (p:R3×R3)
    (ht:0 < tubeHeight M e0 p.2) : tubePhase M e0 (tubeRadialLevel M e0 sigma p) sigma p=0 := by
  have hpow:0 < tubeHeight M e0 p.2^(1+sigma) := Real.rpow_pos_of_pos ht _
  have hR:tubeRadius M e0 (tubeRadialLevel M e0 sigma p) sigma p.2=‖p.1-p.2‖ := by
    unfold tubeRadius tubeRadialLevel
    exact div_mul_cancel₀ _ hpow.ne'
  rw [tubePhase,hR,sub_self,zero_div]

theorem tubePhase_pos_iff_tubeRadialLevel_lt (M e0 sigma a:ℝ) (ha:0 ≤ a) (p:R3×R3)
    (ht:0 < tubeHeight M e0 p.2) : 0 < tubePhase M e0 a sigma p ↔ a < tubeRadialLevel M e0 sigma p := by
  exact tube_phase_pos_iff ha ht

theorem exists_uniform_actual_tube_compact_band_supremum_budget
    (S:KnownSideSourceData) (M e0 sigma:ℝ) (K Seed U:Set (R3×R3))
    (hK:IsCompact K) (hSeed:IsOpen Seed) (hU:IsOpen U) (hKU:K⊆U)
    (hUt:U⊆{z | 0 < tubeHeight M e0 z.2}) (lo hi:ℝ) (hlo:0 ≤ lo)
    (hBand:∀ x∈K,lo ≤ tubeRadialLevel M e0 sigma x ∧ tubeRadialLevel M e0 sigma x ≤ hi)
    (hHigh:∀ y∈U,lo ≤ tubeRadialLevel M e0 sigma y → y∈Seed ∨ y∈K)
    (hFlat:∀ p∈K,p∉Seed → ProductHessianStrictAt
      (fun _:R3 => (1:Matrix (Fin 3) (Fin 3) ℝ)) (fun _:R3 => (1:Matrix (Fin 3) (Fin 3) ℝ))
      p.1 p.2 (tubePhase M e0 (tubeRadialLevel M e0 sigma p) sigma)) :
    ∃ lambda0 C:ℝ,0 < lambda0 ∧ 0 < C ∧
      ∀ L:ℝ,∀ lambda∈Icc (0:ℝ) lambda0,∀ F:R3×R3→ℝ,ProductSolutionOn S L lambda F U →
      ∀ N:ℝ,0 ≤ N → (∀ x∈Seed,‖F x‖ ≤ N) → ∀ x∈K,‖F x‖ ≤ C*N := by
  apply exists_compact_band_product_supremum_budget_of_positive_local_estimates S K Seed U hK hSeed hU hKU
    (tubeRadialLevel M e0 sigma) (continuousOn_tubeRadialLevel M e0 sigma U hUt) lo hi hBand hHigh
  intro p hp hpSeed
  have hpHeight:0 < tubeHeight M e0 p.2 := hUt (hKU hp)
  have ha:0 ≤ tubeRadialLevel M e0 sigma p := hlo.trans (hBand p hp).1
  have hTest:ProductHessianStrictAt (fun x => S.g1 ((0:ℝ) • x)) (fun y => S.g2 ((0:ℝ) • y))
      p.1 p.2 (tubePhase M e0 (tubeRadialLevel M e0 sigma p) sigma) := by
    simpa only [zero_smul,S.g1_origin,S.g2_origin] using hFlat p hp hpSeed
  obtain ⟨lambda0,r,hlambda0,hr,KS,hKS,hKSpos,hSmall,C,hC,H⟩ :=
    exists_uniform_existing_product_solution_local_jet_estimate S p.1 p.2 U hU (hKU hp)
      (tubePhase M e0 (tubeRadialLevel M e0 sigma p) sigma)
      ((tube_phase_contDiffOn M e0 (tubeRadialLevel M e0 sigma p) sigma).2.mono hUt)
      (tubePhase_at_tubeRadialLevel_eq_zero M e0 sigma p hpHeight) hTest
  refine ⟨lambda0,r,hlambda0,hr,KS,hKS,?_,hSmall,C 0,hC 0,?_⟩
  · intro y hy
    have hh:=hKSpos hy
    exact ⟨hh.1,(tubePhase_pos_iff_tubeRadialLevel_lt M e0 sigma _ ha y (hUt hh.1)).mp hh.2⟩
  · intro L lambda hlam F hF T hT hBudget x hx
    have h:=H L lambda hlam F hF T hT hBudget 0 x hx
    simpa only [norm_iteratedFDeriv_zero] using h

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
