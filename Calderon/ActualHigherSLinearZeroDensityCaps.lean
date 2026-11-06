import Calderon.ActualHigherSLinearZero
import Calderon.ActualHigherSLinearZeroScalarCaps
import Calderon.ActualHigherSLeadingWeightedJetBounds
/-! Exact normalized coefficient/density derivative caps. UNCOMPILED own chain.
Full before-code expansion in linear-zero-density-upfront-v001. -/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSLinearZeroDensityCaps
open EnergyBridge ConnectionError ReferenceDensityBounds ReferenceWeightedApproximation
  ActualHigherSLinearZero ActualHigherSLinearZeroScalarCaps ActualHigherSCoordinateWeightBounds
  ActualHigherSLeadingWeightedJetBounds ConformalDepth
open SmoothMetricFrame MovingFrameConnection

def normalizedFrameDivergence (g : MatrixField) (L : ℝ) (i : Fin 3) (z : ℝ × R3) : ℝ :=
  (∑ j : Fin 3, familyDirectionalDeriv j
    (fun t => referenceDensityFamily g L t * referenceMetricGramFrame g L t i j) z) /
    referenceDensityFamily g L z

lemma normalizedFrameDivergence_eq (g : MatrixField) (L q : ℝ) (x : R3) (i : Fin 3) :
    normalizedFrameDivergence g L i (q,x) =
      referenceWeightedFrameDivergence g L q i x/referenceDensityFamily g L (q,x) := rfl

lemma contDiff_normalizedFrameDivergence (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (i : Fin 3) : ContDiff ℝ ∞ (normalizedFrameDivergence g L i) := by
  have hX (j : Fin 3) : ContDiff ℝ ∞ (fun z : ℝ × R3 => referenceMetricGramFrame g L z i j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp (contDiff_referenceMetricGramFrame g hg L i)
  have hsum : ContDiff ℝ ∞ (fun z : ℝ × R3 => ∑ j : Fin 3, familyDirectionalDeriv j
      (fun t => referenceDensityFamily g L t * referenceMetricGramFrame g L t i j) z) :=
    ContDiff.sum (fun j _ => contDiff_familyDirectionalDeriv j _
      ((contDiff_referenceDensityFamily g hg L).mul (hX j)))
  unfold normalizedFrameDivergence
  have hmu : ContDiff ℝ ∞ (referenceDensityFamily g L) :=
    contDiff_referenceDensityFamily g hg L
  have hquot : ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      (∑ j : Fin 3, familyDirectionalDeriv j
        (fun t => referenceDensityFamily g L t * referenceMetricGramFrame g L t i j) z) /
        referenceDensityFamily g L z) :=
    hsum.div hmu (fun z => (referenceDensityFamily_pos g hg L z).ne')
  exact hquot

/-- Product differentiation retains both radius factors and the Q derivative. -/
lemma radius_squared_scalar_first_cap (R Q : R3 → ℝ) (x : R3)
    (beta M M1 J : ℝ) (hb : 1 ≤ beta) (hM : 0 ≤ M) (hM1 : 0 ≤ M1) (hJ : 0 ≤ J)
    (hr : 0 ≤ R x) (hR : DifferentiableAt ℝ R x) (hQ : DifferentiableAt ℝ Q x)
    (hQ0 : ‖Q x‖ ≤ M) (hQ1 : ‖fderiv ℝ Q x‖ ≤ M1)
    (hR1 : ‖fderiv ℝ R x‖ ≤ J*R x*beta) :
    ‖fderiv ℝ (fun y => (R y)^2*Q y) x‖ ≤ (M1+2*J*M)*(R x)^2*beta := by
  have hrnorm : ‖R x‖=R x := by rw [Real.norm_eq_abs,abs_of_nonneg hr]
  have hr2norm : ‖(R x)^2‖=(R x)^2 := by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hR2 : ‖fderiv ℝ (fun y => (R y)^2) x‖ ≤ 2*R x*(J*R x*beta) := by
    have h := norm_fderiv_scalar_smul_le R R x hR hR
    have h0 : ‖fderiv ℝ (fun y => (R y)^2) x‖ ≤ 2*R x*‖fderiv ℝ R x‖ := by
      calc
        _ ≤ ‖R x‖*‖fderiv ℝ R x‖+‖fderiv ℝ R x‖*‖R x‖ := by
          simpa only [smul_eq_mul,pow_two] using h
        _ = _ := by rw [hrnorm]; ring
    exact h0.trans (mul_le_mul_of_nonneg_left hR1 (by positivity))
  have h := norm_fderiv_scalar_smul_le (fun y => (R y)^2) Q x (hR.pow 2) hQ
  have hM1b : M1 ≤ M1*beta := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hM1
  calc
    _ ≤ ‖(R x)^2‖*‖fderiv ℝ Q x‖+‖fderiv ℝ (fun y => (R y)^2) x‖*‖Q x‖ := by
      simpa only [smul_eq_mul] using h
    _ ≤ (R x)^2*(M1*beta)+(2*R x*(J*R x*beta))*M := by
      rw [hr2norm]
      exact add_le_add (mul_le_mul_of_nonneg_left (hQ1.trans hM1b) (sq_nonneg _))
        (mul_le_mul hR2 hQ0 (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- The exact positive-density normalization, without dividing Q. -/
lemma normalizedSecondCoefficientDerivative_eq (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (i j k : Fin 3) (x : R3) :
    normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j k x =
      fderiv ℝ (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j) x
        (referenceMetricGramFrame g L (q,x) k)+
      ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j x *
        normalizedFrameDivergence g L k (q,x) := by
  rw [normalizedSecondCoefficientDerivative,normalizedFrameDivergence_eq,
    ActualHigherSSecondAdjoint.densityDerivativeCoefficient]
  have hmu : referenceDensityFamily g L (q,x) ≠ 0 := (referenceDensityFamily_pos g hg L _).ne'
  field_simp [hmu]
  <;> ring

/-- Every constant precedes q/profile/base point; no smallness assumption is used. -/
theorem exists_normalized_second_derivative_cap
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L) (y0 : R3) (rho : ℝ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ D : ℝ,0 < D ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ,∀ hdr : 0 < dr,dr ≤ 1 → ∀ Ar : ℝ,0 < Ar → ∀ p : ℕ,1 ≤ p →
      ∀ x ∈ closedBall y0 rho,1 ≤ actualReferenceBeta g L q dr Ar p x → ∀ i j k : Fin 3,
      |normalizedSecondCoefficientDerivative g L g2 dr Ar p q i j k x| ≤
        D*(referenceRadius dr Ar p L x)^2*actualReferenceBeta g L q dr Ar p x := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall y0 rho) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨M,hM,hscalar⟩ := exists_word_scalar_caps g hg L hL y0 rho g2 hg2
  let Q : (Fin 3 × Fin 3) → (ℝ × R3) → ℝ := fun ij z =>
    referenceDensityPrincipalFrameCoefficient g g2 L z.1 z.2 ij.1 ij.2
  have hQ (ij : Fin 3 × Fin 3) : ContDiff ℝ ∞ (Q ij) :=
    contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L ij.1 ij.2
  obtain ⟨M1,hM1,hDQ⟩ := compact_family_cap _ hK (fun ij : Fin 3 × Fin 3 => fderiv ℝ (Q ij))
    (fun ij => ((hQ ij).fderiv_right (m := ∞) (by simp)).continuous.continuousOn)
  obtain ⟨V,hV,hdiv⟩ := compact_family_cap _ hK (normalizedFrameDivergence g L)
    (fun i => (contDiff_normalizedFrameDivergence g hg L i).continuous.continuousOn)
  obtain ⟨J,hJ,hjet⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL (closedBall y0 rho) (isCompact_closedBall _ _) 1
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hM10 : 0 ≤ M1 := zero_le_one.trans hM1
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  let A : ℝ := M1+2*J*M
  let D : ℝ := 1+A*M+M*V
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D,hD,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp x hx hb i j k
  let R := referenceRadius dr Ar p L
  let beta := actualReferenceBeta g L q dr Ar p x
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hr : 0 ≤ R x := (referenceRadius_pos dr Ar p L x hdr hAr).le
  have hsc := hscalar q hq dr hdr hdr1 Ar hAr p hp x hx hb
  have hQslice := (hQ (i,j)).comp
    (show ContDiff ℝ ∞ (fun y : R3 => (q,y)) from contDiff_const.prodMk contDiff_id)
  have hR : ContDiff ℝ ∞ R := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr
  have hR1 : ‖fderiv ℝ R x‖ ≤ J*R x*beta := by
    simpa only [norm_iteratedFDeriv_one,pow_one,R,beta,actualReferenceBeta] using
      (hjet q hq dr hdr hdr1 Ar hAr p hp x hx).1
  have hQ1 : ‖fderiv ℝ (fun y : R3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) x‖ ≤ M1 :=
    norm_fderiv_fixed_q_slice_le (Q (i,j)) (hQ (i,j)) q x M1 hM10 (hDQ (i,j) (q,x) ⟨hq,hx⟩)
  have ha1 : ‖fderiv ℝ (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j) x‖ ≤
      A*(R x)^2*beta := by
    exact radius_squared_scalar_first_cap R (fun y => referenceDensityPrincipalFrameCoefficient g g2 L q y i j)
      x beta M M1 J hb hM0 hM10 hJ.le hr (hR.differentiable (by simp) x)
      (hQslice.differentiable (by simp) x) (by simpa only [Real.norm_eq_abs] using hsc.1 i j) hQ1 hR1
  have ha0 : |ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j x| ≤ (R x)^2*M := by
    rw [ActualHigherSSecondAdjoint.secondCoefficient,abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hsc.1 i j) (sq_nonneg _)
  have hv : |normalizedFrameDivergence g L k (q,x)| ≤ V := by
    simpa only [Real.norm_eq_abs] using hdiv k (q,x) ⟨hq,hx⟩
  have hVb : V ≤ V*beta := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hV0
  rw [normalizedSecondCoefficientDerivative_eq g hg]
  calc
    _ ≤ |fderiv ℝ (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j) x
        (referenceMetricGramFrame g L (q,x) k)|+
      |ActualHigherSSecondAdjoint.secondCoefficient g g2 L q dr Ar p i j x *
        normalizedFrameDivergence g L k (q,x)| := abs_add_le _ _
    _ ≤ (A*(R x)^2*beta)*M+((R x)^2*M)*(V*beta) := by
      apply add_le_add
      · rw [← Real.norm_eq_abs]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul ha1 (hsc.2.2.2.1 k) (norm_nonneg _) (by positivity))
      · rw [abs_mul]
        exact mul_le_mul ha0 (hv.trans hVb) (abs_nonneg _) (by positivity)
    _ ≤ D*(R x)^2*beta := by
      have hrem : 0 ≤ (R x)^2*beta := mul_nonneg (sq_nonneg _) hb0
      dsimp only [D]
      nlinarith only [hrem]
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSLinearZeroDensityCaps
