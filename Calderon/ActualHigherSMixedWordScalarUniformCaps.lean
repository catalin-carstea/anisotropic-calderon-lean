import Calderon.ActualHigherSMixedWordScalarProducts
import Calderon.ProfileRadiusJets
import Calderon.ActualHigherSCoordinateWeightBounds

/-! Complete actual scalar first-jet producer for every207 mixed word.
Constants precede q/profile/base point; no jet/budget callback is a final premise.
Conditional own scalar-jet algebra11482bd5 and Words005 retain native/review holds.
Original ProfileRadiusJets observed source-byte qualification is retained explicitly
in the archived correspondence; no older receipt binding is newly asserted. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedWordScalarJets
open EnergyBridge ConnectionError ConformalDepth ReferenceWeightedApproximation
  ActualHigherSQuadraticZeroWords ActualNormalizedSecondMetricDrift SmoothMetricFrame MovingFrameConnection
  ActualHigherSLeadingBracketGain

def frameConnectionScalarJoint (g : MatrixField) (L : ℝ) (i a b : Fin 3) (z : ℝ × R3) : ℝ :=
  referenceFrameConnectionCoefficient g L z.1 z.2 (referenceMetricGramFrame g L z i) a b

lemma contDiff_frameConnectionScalarJoint (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (i a b : Fin 3) : ContDiff ℝ ∞ (frameConnectionScalarJoint g L i a b) := by
  have hX := contDiff_referenceMetricGramFrame g hg L i
  have hJ := ActualHorizontalNormBridge.contDiff_referenceFrameConnectionJoint g hg L
    (fun z : ℝ × R3 => referenceMetricGramFrame g L z i) hX a b
  have he : frameConnectionScalarJoint g L i a b =
      fun z => ActualHorizontalNormBridge.referenceFrameConnectionJoint g L
        (fun z : ℝ × R3 => referenceMetricGramFrame g L z i) z a b := by
    funext z
    exact (ActualHorizontalNormBridge.referenceFrameConnectionJoint_eq g hg L
      (fun z : ℝ × R3 => referenceMetricGramFrame g L z i) z a b).symm
  rw [he]
  exact hJ

attribute [local irreducible] actualWordCoefficient
  ActualHigherSLeadingBracketGain.firstCoordinateWeight referenceDensityPrincipalFrameCoefficient

theorem exists_actual_mixed_word_scalar_first_caps
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (y0 : R3) (rho : ℝ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ closedBall y0 rho,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ 1 →
      (∀ z : ZeroWord,
        ScalarPointJet (fun y => actualWordCoefficient g L g2 dr Ar p q y z) x
          (C*referenceRadius dr Ar p L x)
          (C*referenceRadius dr Ar p L x*actualReferenceBeta g L q dr Ar p x)) ∧
      (∀ k i : Fin 3, ∀ z : ZeroWord,
        ScalarPointJet (fun y => (referenceRadius dr Ar p L y)^2*
          firstCoordinateWeight g g2 L k i (ActualHigherSFormation.higherSParam L dr Ar p q y)*
            actualWordCoefficient g L g2 dr Ar p q y z) x
          (C*(referenceRadius dr Ar p L x)^3)
          (C*(referenceRadius dr Ar p L x)^3*actualReferenceBeta g L q dr Ar p x)) := by
  let S : Set (ℝ × R3) := Icc (0 : ℝ) 1 ×ˢ closedBall y0 rho
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨MQ, hMQ, hQ⟩ := exists_finite_joint_first_caps
    (fun ij : Fin 3 × Fin 3 => fun z : ℝ × R3 => referenceDensityPrincipalFrameCoefficient g g2 L z.1 z.2 ij.1 ij.2)
    (fun ij => contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L ij.1 ij.2) S hS
  obtain ⟨MG, hMG, hG⟩ := exists_finite_joint_first_caps
    (fun z : Fin 3 × (Fin 3 × Fin 3) => frameConnectionScalarJoint g L z.1 z.2.1 z.2.2)
    (fun z => contDiff_frameConnectionScalarJoint g hg L z.1 z.2.1 z.2.2) S hS
  obtain ⟨MX, hMX, hX⟩ := exists_finite_joint_first_caps
    (fun i : Fin 3 => fun z : ℝ × R3 => referenceMetricGramFrame g L z i)
    (fun i => contDiff_referenceMetricGramFrame g hg L i) S hS
  obtain ⟨MW, hMW, hW⟩ := ActualHigherSCoordinateWeightBounds.exists_physical_firstCoordinateWeight_uniform_first_caps
    g g2 hg hg2 L y0 rho
  obtain ⟨CR1, hCR1, hRad1⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL (closedBall y0 rho) (isCompact_closedBall _ _) 1
  obtain ⟨CR2, hCR2, hRad2⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL (closedBall y0 rho) (isCompact_closedBall _ _) 2
  let M := 1+MQ+MG+MX+MW+CR1+CR2
  have hMQ0 : 0 ≤ MQ := zero_le_one.trans hMQ
  have hMG0 : 0 ≤ MG := zero_le_one.trans hMG
  have hMX0 : 0 ≤ MX := zero_le_one.trans hMX
  have hMW0 : 0 ≤ MW := zero_le_one.trans hMW
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hQM : MQ ≤ M := by dsimp [M]; linarith
  have hGM : MG ≤ M := by dsimp [M]; linarith
  have hXM : MX ≤ M := by dsimp [M]; linarith
  have hWM : MW ≤ M := by dsimp [M]; linarith
  have hR1M : CR1 ≤ M := by dsimp [M]; linarith
  have hR2M : CR2 ≤ M := by dsimp [M]; linarith
  let Cw := scalarWordConstant M
  let Cs := 1+Cw*(3*M+2*M^2)
  let C := 1+Cw+Cs
  have hCw : 0 ≤ Cw := by dsimp [Cw, scalarWordConstant]; positivity
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCwC : Cw ≤ C := by dsimp [C]; linarith
  have hCsC : Cs ≤ C := by dsimp [C]; linarith
  have hProductValue : M*Cw ≤ Cs := by
    dsimp [Cs]
    nlinarith only [mul_nonneg hCw hM0,mul_nonneg hCw (sq_nonneg M)]
  have hProductDerivative : Cw*(2*M+2*M^2) ≤ Cs := by
    dsimp [Cs]
    nlinarith only [mul_nonneg hCw hM0]
  refine ⟨C, hC, ?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp x hx hb hs
  let R := referenceRadius dr Ar p L
  let r := R x
  let beta := actualReferenceBeta g L q dr Ar p x
  have hr : 0 ≤ r := (referenceRadius_pos dr Ar p L x hdr hAr).le
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hR : ContDiff ℝ ∞ R := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr
  have hqx : (q,x) ∈ S := ⟨hq,hx⟩
  have hR1 : ‖fderiv ℝ R x‖ ≤ M*r*beta := by
    have h := (hRad1 q hq dr hdr hdr1 Ar hAr p hp x hx).1
    have hh : ‖fderiv ℝ R x‖ ≤ CR1*r*beta := by
      simpa only [norm_iteratedFDeriv_one, ReferenceWeightedApproximation.actualReferenceBeta, pow_one, R, r, beta] using h
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR1M hr) hb0)
  have hR2 : ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ M*r*beta^2 := by
    have h := (hRad2 q hq dr hdr hdr1 Ar hAr p hp x hx).1
    have hh : ‖iteratedFDeriv ℝ 2 R x‖ ≤ CR2*r*beta^2 := by
      simpa only [ReferenceWeightedApproximation.actualReferenceBeta, R, r, beta] using h
    calc
      _ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ R) x‖ := (norm_iteratedFDeriv_one (fderiv ℝ R)).symm
      _ = ‖iteratedFDeriv ℝ 2 R x‖ := norm_iteratedFDeriv_fderiv
      _ ≤ CR2*r*beta^2 := hh
      _ ≤ M*r*beta^2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR2M hr) (sq_nonneg beta)
  have hQJet (i j : Fin 3) : ScalarPointJet
      (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x M M := by
    have hSm := contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j
    refine ⟨(hSm.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x, ?_, ?_⟩
    · have hVal : |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ MQ := by
        simpa only [Real.norm_eq_abs] using (hQ (i,j) (q,x) hqx).1
      exact hVal.trans hQM
    · exact ((norm_fderiv_fixed_slice_le _ hSm q x).trans (hQ (i,j) (q,x) hqx).2).trans hQM
  have hGJet (i a b : Fin 3) : ScalarPointJet
      (fun y => referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) a b) x M M := by
    have hSm := contDiff_frameConnectionScalarJoint g hg L i a b
    refine ⟨(hSm.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x, ?_, ?_⟩
    · have hVal : |referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) a b| ≤ MG := by
        simpa only [frameConnectionScalarJoint, Real.norm_eq_abs] using (hG (i,(a,b)) (q,x) hqx).1
      exact hVal.trans hGM
    · exact ((norm_fderiv_fixed_slice_le _ hSm q x).trans (hG (i,(a,b)) (q,x) hqx).2).trans hGM
  have hXJet (i : Fin 3) : DifferentiableAt ℝ (fun y => referenceMetricGramFrame g L (q,y) i) x ∧
      ‖referenceMetricGramFrame g L (q,x) i‖ ≤ M ∧
      ‖fderiv ℝ (fun y => referenceMetricGramFrame g L (q,y) i) x‖ ≤ M := by
    have hSm := contDiff_referenceMetricGramFrame g hg L i
    exact ⟨(hSm.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x,
      ((hX i (q,x) hqx).1).trans hXM,
      ((norm_fderiv_fixed_slice_le _ hSm q x).trans (hX i (q,x) hqx).2).trans hXM⟩
  have hLambda (z : ZeroWord) : ScalarPointJet
      (fun y => actualWordCoefficient g L g2 dr Ar p q y z) x (Cw*r) (Cw*r*beta) := by
    rw [actualWordCoefficient_eq_cleared g hg L g2 dr Ar p hdr hAr q z]
    exact scalarPointJet_clearedWordCoefficient R
      (fun i j y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j)
      (fun i y => referenceMetricGramFrame g L (q,y) i)
      (fun i a b y => referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) a b)
      hR x beta M hr hb hM hs hR1 hR2 hQJet hGJet hXJet z
  have hRJ : ScalarPointJet R x r (M*r*beta) :=
    ⟨hR.differentiable (by simp) x, by
      change |r| ≤ r
      exact le_of_eq (abs_of_nonneg hr), hR1⟩
  have hWJet (k i : Fin 3) : ScalarPointJet
      (fun y => firstCoordinateWeight g g2 L k i (ActualHigherSFormation.higherSParam L dr Ar p q y)) x M M := by
    have h := hW q hq x hx dr Ar p k i
    exact ⟨h.1.differentiable (by simp) x, h.2.1.trans hWM, h.2.2.trans hWM⟩
  have hMixed (k i : Fin 3) (z : ZeroWord) : ScalarPointJet
      (fun y => R y^2*firstCoordinateWeight g g2 L k i (ActualHigherSFormation.higherSParam L dr Ar p q y)*
        actualWordCoefficient g L g2 dr Ar p q y z) x (Cs*r^3) (Cs*r^3*beta) :=
    scalarPointJet_radius_sq_weight_word R
      (fun y => firstCoordinateWeight g g2 L k i (ActualHigherSFormation.higherSParam L dr Ar p q y))
      (fun y => actualWordCoefficient g L g2 dr Ar p q y z)
      x r beta M Cw Cs hr hb hM0 hCw hProductValue hProductDerivative hRJ (hWJet k i) (hLambda z)
  refine ⟨?_, ?_⟩
  · intro z
    exact (hLambda z).mono (mul_le_mul_of_nonneg_right hCwC hr)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCwC hr) hb0)
  · intro k i z
    exact (hMixed k i z).mono (mul_le_mul_of_nonneg_right hCsC (pow_nonneg hr 3))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsC (pow_nonneg hr 3)) hb0)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedWordScalarJets
