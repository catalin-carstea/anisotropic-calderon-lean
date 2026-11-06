import Calderon.ActualFiniteCanonicalSourceJetMenu
import Calderon.ActualSourceChartContactIdentity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
open EnergyBridge DirichletFamily

lemma sum_smul_single_block
    {α β V : Type*} [Fintype α] [Fintype β] [DecidableEq α] [AddCommMonoid V] [Module ℝ V]
    (f : α → β → V) (a : β → ℝ) (p : α) :
    (∑ z : α × β, (if z.1 = p then a z.2 else 0) • f z.1 z.2) =
      ∑ j : β, a j • f p j := by
  classical
  rw [Fintype.sum_prod_type]
  have hRow (t : α) :
      (∑ j : β, (if t = p then a j else 0) • f t j) =
        if t = p then ∑ j : β, a j • f t j else 0 := by
    by_cases h : t = p <;>
      simp only [h, ite_true, ite_false, zero_smul, Finset.sum_const_zero]
  simp only [hRow, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma radiusTwoSourceEuclideanCoordinates_normalized_of_gradient_jets
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
    (q : R3) (hq : q ∈ (radiusTwoOpens : Set R3))
    (hJet : ∀ i : Fin 3,
      radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg q (f i) =
        compatibleSourceJetBasis g q (Sum.inr (Sum.inl i))) :
    radiusTwoSourceEuclideanCoordinates fixedDirichletRegularity fixedSobolevCalculus g hg f q = 0 ∧
    HasFDerivAt (radiusTwoSourceEuclideanCoordinates
      fixedDirichletRegularity fixedSobolevCalculus g hg f) (ContinuousLinearMap.id ℝ R3) q := by
  have hValue (i : Fin 3) :
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg (f i) q = 0 :=
    congrArg (fun J : RadiusTwoRawTwoJet => J.1) (hJet i)
  have hGradient (i : Fin 3) :
      fderiv ℝ (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
        g hg (f i)) q = EuclideanSpace.proj i :=
    congrArg (fun J : RadiusTwoRawTwoJet => J.2.1) (hJet i)
  constructor
  · rw [radiusTwoSourceEuclideanCoordinates_eq_sum_smul]
    simp only [hValue, zero_smul, Finset.sum_const_zero]
  · have h := hasFDerivAt_radiusTwoSourceEuclideanCoordinates_sum_smulRight g hg f q hq
    simp only [hGradient, sum_projection_smulRight_coordinateVector] at h
    exact h

theorem exists_flattened_finite_radiusTwoSource_canonicalJet_menu
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ (T : Finset {q : R3 // q ∈ closedBall (0 : R3) 1})
      (s : T → (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → 𝓓(fixedExteriorSourceOpens, ℝ)),
      ∀ q ∈ closedBall (0 : R3) 1,
        ∃ b : (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → (T × (Fin 1 ⊕ (Fin 3 ⊕ Fin 5))) → ℝ,
          (∀ k z, |b k z| < 2) ∧
          (∀ k, radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg q
            (∑ z, b k z • s z.1 z.2) = compatibleSourceJetBasis g q k) ∧
          radiusTwoSourceEuclideanCoordinates fixedDirichletRegularity fixedSobolevCalculus g hg
            (fun i : Fin 3 => ∑ z, b (Sum.inr (Sum.inl i)) z • s z.1 z.2) q = 0 ∧
          HasFDerivAt (radiusTwoSourceEuclideanCoordinates
            fixedDirichletRegularity fixedSobolevCalculus g hg
            (fun i : Fin 3 => ∑ z, b (Sum.inr (Sum.inl i)) z • s z.1 z.2))
            (ContinuousLinearMap.id ℝ R3) q := by
  classical
  obtain ⟨T, s, hMenu⟩ := exists_finite_radiusTwoSource_canonicalJet_menu g hg
  refine ⟨T, s, ?_⟩
  intro q hq
  obtain ⟨p, c, hc, hL1, hJets⟩ := hMenu q hq
  let b : (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → (T × (Fin 1 ⊕ (Fin 3 ⊕ Fin 5))) → ℝ :=
    fun k z => if z.1 = p then c k z.2 else 0
  have hSum (k : Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) :
      (∑ z, b k z • s z.1 z.2) = ∑ j, c k j • s p j :=
    sum_smul_single_block s (c k) p
  have hFullJets (k : Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) :
      radiusTwoSmoothSourceJet fixedDirichletRegularity fixedSobolevCalculus g hg q
        (∑ z, b k z • s z.1 z.2) = compatibleSourceJetBasis g q k := by
    rw [hSum k]
    exact hJets k
  have hqOpen : q ∈ (radiusTwoOpens : Set R3) := by
    change q ∈ ball (0 : R3) 2
    have hqNorm := mem_closedBall_zero_iff.mp hq
    exact mem_ball_zero_iff.mpr (by linarith)
  obtain ⟨hZero, hId⟩ := radiusTwoSourceEuclideanCoordinates_normalized_of_gradient_jets
    g hg (fun i : Fin 3 => ∑ z, b (Sum.inr (Sum.inl i)) z • s z.1 z.2) q hqOpen
      (fun i => hFullJets (Sum.inr (Sum.inl i)))
  refine ⟨b, ?_, hFullJets, hZero, hId⟩
  intro k z
  dsimp [b]
  by_cases h : z.1 = p
  · simpa only [h, ite_true] using hc k z.2
  · simp only [h, ite_false, abs_zero]
    norm_num

end OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
