import Calderon.ActualHalfLiftSphereL2Budget
import Calderon.ActualNativeCutoffHalfLift
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
open ConnectionError ConformalDepth ActualFiniteHarmonicCore WeightedBaseSpectral
attribute [local irreducible] sphereSobolevInclusionL harmonicSphereSubspace nativeNormalizedCutoffPhysicalOperator

theorem exists_uniform_original_weighted_cutoff_output_budget
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics)
    (hD:DenseSphereHarmonics) (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L:ℝ)
    (cover:NativeNormalCover S L):
    ∃ C:ℝ,1 ≤ C ∧ ∀ chi:R3→ℝ,tsupport chi⊆interior cylinder →
      ∀ lambda∈Icc (0:ℝ) 1,∀ delta Rstar:ℝ,∀ p:ℕ,∀ Psi:R3→SphereSobolev (3/2:ℝ),
      ∀ (W:R3→SphereL2) (hW:Continuous W) (hWc:HasCompactSupport W),tsupport W⊆tsupport chi →
      ∀ D:ℝ,0 ≤ D →
      (∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        ∃ v:SphereSobolev (1/2:ℝ),‖v‖ ≤ D ∧
          sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) v=
          nativeNormalizedCutoffPhysicalOperator hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y) →
      (∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (W y))=
          nativeNormalizedCutoffPhysicalOperator hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y) →
      ‖referenceBaseLift S.g1 S.g1_admissible L lambda W hW hWc‖ ≤ C*D := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_referenceBaseLift_bound_of_half_lift_graph_budget
    hO hD S.g1 S.g1_admissible L 3
  refine ⟨C,hC,?_⟩
  intro chi hchi lambda hlam delta Rstar p Psi W hW hWc hSupp D hD0 hHalf hGraph
  have hBall:tsupport W⊆closedBall (0:R3) 3 := by
    intro y hy
    have hCyl:y∈cylinder := interior_subset (hchi (hSupp hy))
    rw [mem_closedBall_zero_iff]
    exact (norm_le_two_of_mem_cylinder y hCyl).trans (by norm_num)
  apply HC lambda hlam W hW hWc hBall D hD0
  intro y hy
  by_cases hys:y∈tsupport chi
  · have hyCyl:y∈cylinder := interior_subset (hchi hys)
    obtain ⟨i,hi⟩ := cover.covers_cylinder y hyCyl
    have hyRoom:y∈interior cylinder∩(cover.packet i).centers := ⟨hchi hys,hi⟩
    obtain ⟨v,hv,he⟩ := hHalf i y hyRoom
    exact ⟨v,hv,(hGraph i y hyRoom).trans he.symm⟩
  · have hz:W y=0 := image_eq_zero_of_notMem_tsupport (fun hh => hys (hSupp hh))
    refine ⟨0,by simpa only [norm_zero] using hD0,?_⟩
    simp only [hz,map_zero]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
