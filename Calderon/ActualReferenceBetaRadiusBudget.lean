import Calderon.ActualReferenceBetaRadiusScale
import Calderon.ActualKernelBetaRadiusProfile
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConformalDepth RadiusProfile ReferenceWeightedApproximation ActualHigherRadiusProfile

theorem exists_uniform_actual_beta_radius_budget_on_native_cover
    (S:KnownSideSourceData) (L:ℝ) (hL:0 < L) (cover:NativeNormalCover S L):
    ∃ p0:ℕ,2 ≤ p0 ∧ ∀ p:ℕ,p0 ≤ p → ∀ eps:ℝ,0 < eps →
    ∃ R0:ℝ,0 < R0 ∧ ∀ Rstar:ℝ,0 < Rstar → Rstar ≤ R0 →
      (∀ lambda∈Icc (0:ℝ) 1,∀ delta:ℝ,0 < delta → delta ≤ 1 → ∀ y∈cylinder,
        referenceRadius delta Rstar p L y*(actualReferenceBeta S.g1 L lambda delta Rstar p y)^2 ≤ eps) ∧
      (∀ delta:ℝ,0 < delta → delta ≤ 1 → ∀ y∈cylinder,
        referenceRadius delta Rstar p L y < cover.radiusCeiling) := by
  obtain ⟨pBeta,_hqBeta,_hpBeta,HBetaP⟩ :=
    exists_fixed_actual_reference_beta_power_radius_profile
      S.g1 S.g1_admissible L hL cylinder isCompact_native_center_cylinder 2
  refine ⟨max 2 pBeta,le_max_left _ _,?_⟩
  intro p hp eps heps
  have hpBeta:pBeta ≤ p := (le_max_right _ _).trans hp
  let eta:ℝ := min eps (min (cover.radiusCeiling/2) 1)
  have heta:0 < eta := lt_min heps
    (lt_min (div_pos cover.radius_positive (by norm_num)) (by norm_num))
  have heta1:eta ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hetaEps:eta ≤ eps := min_le_left _ _
  have hetaRoom:eta < cover.radiusCeiling := by
    have hh:eta ≤ cover.radiusCeiling/2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith only [hh,cover.radius_positive]
  obtain ⟨RB,hRB,HBeta⟩ := HBetaP p hpBeta eta heta heta1
  refine ⟨RB,hRB,?_⟩
  intro Rstar hRs hRsBeta
  constructor
  · intro lambda hlam delta hd hd1 y hy
    have hAtRB := (HBeta lambda hlam delta hd hd1 y hy).2.1
    have hMono := referenceRadius_beta_sq_mono_scale S.g1 L lambda delta Rstar RB p y hd hRs hRB hRsBeta
    exact hMono.1.trans (hAtRB.trans hetaEps)
  · intro delta hd hd1 y hy
    have hAtRB := (HBeta 0 (by constructor <;> norm_num) delta hd hd1 y hy).2.2
    have hMono := referenceRadius_beta_sq_mono_scale S.g1 L 0 delta Rstar RB p y hd hRs hRB hRsBeta
    exact (hMono.2.trans hAtRB).trans_lt hetaRoom

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
