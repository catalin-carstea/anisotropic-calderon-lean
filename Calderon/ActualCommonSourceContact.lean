import Calderon.RadiusTwoSourcePointwiseEmbedding

set_option autoImplicit false
noncomputable section
open Set Metric Filter TopologicalSpace
open scoped Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature

theorem exists_radiusTwoSource_contact_and_tendsto
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (W : Set R3) (Psi : W → (radiusTwoOpens : Set R3))
    (hMatch : ∀ x : W,
      radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 (Psi x : R3) =
        radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 (x : R3))
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) (hpW : p ∈ closure W) :
    ∃ q : (radiusTwoOpens : Set R3),
      radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 (q : R3) =
        radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 p ∧
      Tendsto Psi (Filter.comap (Subtype.val : W → R3) (𝓝 p)) (𝓝 q) := by
  let I1 := radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1
  let I2 := radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2
  have hI1 : Continuous I1 := continuous_radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1
  have hI2 : Continuous I2 := continuous_radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2
  have hClosed : IsClosed (I1 '' closedBall (0 : R3) 2) :=
    ((isCompact_closedBall (0 : R3) 2).image hI1).isClosed
  have hKnown : W ⊆ I2 ⁻¹' (I1 '' closedBall (0 : R3) 2) := by
    intro x hx
    exact ⟨(Psi ⟨x,hx⟩ : R3), ball_subset_closedBall (Psi ⟨x,hx⟩).property,
      hMatch ⟨x,hx⟩⟩
  have hContact : I2 p ∈ I1 '' closedBall (0 : R3) 2 :=
    closure_minimal hKnown (hClosed.preimage hI2) hpW
  obtain ⟨q,hq,hqEq⟩ := hContact
  have hqInterior : q ∈ (radiusTwoOpens : Set R3) := by
    apply mem_ball_zero_iff.mpr
    by_contra h
    have hZero : I1 q = 0 :=
      radiusTwoSourceEvaluationFamily_eq_zero_of_norm_ge hreg hcalc g1 hg1 q
        (le_of_not_gt h)
    exact (radiusTwoSourceEvaluationFamily_ne_zero hreg hcalc hSep g2 hg2 p hp)
      (hqEq.symm.trans hZero)
  let qB : (radiusTwoOpens : Set R3) := ⟨q,hqInterior⟩
  refine ⟨qB,hqEq,?_⟩
  apply (isEmbedding_radiusTwoSourceEvaluationFamily hreg hcalc hSep g1 hg1).tendsto_nhds_iff.mpr
  have hLimit : Tendsto (fun x : W => I2 (x : R3))
      (Filter.comap (Subtype.val : W → R3) (𝓝 p)) (𝓝 (I2 p)) :=
    (hI2.tendsto p).comp Filter.tendsto_comap
  have hFunctions : (fun x : W => I1 (Psi x : R3)) = (fun x : W => I2 (x : R3)) :=
    funext hMatch
  change Tendsto (fun x : W => I1 (Psi x : R3))
    (Filter.comap (Subtype.val : W → R3) (𝓝 p)) (𝓝 (I1 q))
  rw [hFunctions,hqEq]
  exact hLimit

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSource_contact_and_tendsto
