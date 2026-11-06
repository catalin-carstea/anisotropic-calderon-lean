import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficientJets
import Calderon.ActualDensityPrincipalFrameCoefficientBound
import Calderon.ActualHorizontalSobolevConnection
import Calderon.ActualNativeMovingRadiusTrace
import Calderon.ActualNormalizedSecondDriftAngularAllocation

/-!
Original scalar word coefficients for all five actual S zero groups.
No assumed analytic cap, no finite-angular substitution for physical E outputs.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSZeroSWordBudget
open ConnectionError ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherLogFrameJets
  ActualReferenceDDHigherHCoframeJets ActualNormalizedSecondMetricDrift
  ActualNormalizedSecondDriftAngularAllocation ActualFiniteHarmonicModel
  SmoothMetricFrame MovingFrameConnection AmbientReferenceRaising
  ReferenceDensityBounds ReferenceWeightedApproximation ConformalDepth
  ActualHorizontalNormBridge NormalCoordinatesFrame

/-- Sum of the exact rotation coefficients of O_i, retaining the one-half. -/
def lowerSConnectionWordMass (g : MatrixField) (L q : ℝ) (i : Fin 3) (x : R3) : ℝ :=
  (1/2 : ℝ)*(∑ c : Fin 3, ∑ d : Fin 3,
    |referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) c d|)

/-- Literal scalar coefficients of the differentiated-E, connection, degree,
angular-coordinate and double-E groups. The frame norm counts the direction
of the first ordinary derivative primitive. -/
def lowerSZeroWordMass (g g2 : MatrixField) (L q dr Ar : ℝ) (p : ℕ) (x : R3) : ℝ :=
  let r := referenceRadius dr Ar p L x
  let f := fun i : Fin 3 => referenceRadiusHorizontalLogDerivative g L q
    (referenceRadius dr Ar p L) x i
  let QQ := fun a b : Fin 3 => |referenceDensityPrincipalFrameCoefficient g g2 L q x a b|
  r^2*(∑ a : Fin 3, ∑ b : Fin 3, QQ a b *
    (‖referenceMetricGramFrame g L (q,x) a‖ + 2*|f a|+|f b|+
      (∑ k : Fin 3, |referenceFrameConnectionCoefficient g L q x
        (referenceMetricGramFrame g L (q,x) a) k b|)+
      lowerSConnectionWordMass g L q a x+lowerSConnectionWordMass g L q b x)) +
  r^2*(∑ a : Fin 3, |normalizedSecondDriftFrameJoint g g2 L a (q,x)|) +
  2*r*(∑ a : Fin 3, ∑ b : Fin 3, QQ a b) +
  r^3*(∑ a : Fin 3, ∑ b : Fin 3, QQ a b)

theorem lowerSZeroWordMass_nonneg (g g2 : MatrixField) (L q dr Ar : ℝ)
    (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (x : R3) :
    0 ≤ lowerSZeroWordMass g g2 L q dr Ar p x := by
  have hr := (referenceRadius_pos dr Ar p L x hdr hAr).le
  unfold lowerSZeroWordMass lowerSConnectionWordMass
  positivity

private lemma horizontalLog_eq_frameLog (g : MatrixField) (L q dr Ar : ℝ)
    (p : ℕ) (x : R3) (i : Fin 3) :
    referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x i =
      referenceFrameDerivative g L q i (fun y => Real.log (referenceRadius dr Ar p L y)) x := by
  have hFrame : conformalReferenceGramFrameOperatorJoint g L (q,x) (coordinateVector i) =
      referenceMetricGramFrame g L (q,x) i :=
    (congrArg (fun T : R3 →L[ℝ] R3 => T (coordinateVector i))
      (conformalReferenceGramFrameOperatorJoint_eq_frameOperator g L (q,x))).trans
      ((frameOperator_coordinateVector _ i).trans
        (conformalReferenceGramFrame_eq_referenceMetricGramFrame g L q x i))
  unfold referenceRadiusHorizontalLogDerivative referenceFrameDerivative
  exact congrArg (fderiv ℝ (fun y => Real.log (referenceRadius dr Ar p L y)) x) hFrame

/-- All five original Q coefficient groups have a common scalar word budget
C_Q*r. Constants are fixed after the original metric pair and compact region,
before q and every profile. All primitive background caps are derived here. -/
theorem exists_lowerSZeroWordMass_uniform_profile_bound
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (y0 : R3) (rho : ℝ) :
    ∃ C_Q : ℝ, 0 < C_Q ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
      ∀ x ∈ closedBall y0 rho,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      lowerSZeroWordMass g g2 L q dr Ar p x ≤ C_Q*referenceRadius dr Ar p L x := by
  let K := closedBall y0 rho
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨MF,hMF,hFrame⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun i : Fin 3 => fun z : ℝ × R3 => referenceMetricGramFrame g L z i)
    (fun i => contDiff_referenceMetricGramFrame g hg L i) K hK 0
  obtain ⟨MG,hMG,hGamma⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 × Fin 3 => fun z : ℝ × R3 => referenceFrameConnectionJoint g L
      (fun v : ℝ × R3 => referenceMetricGramFrame g L v t.1) z t.2.1 t.2.2)
    (fun t => contDiff_referenceFrameConnectionJoint g hg L
      (fun v : ℝ × R3 => referenceMetricGramFrame g L v t.1)
      (contDiff_referenceMetricGramFrame g hg L t.1) t.2.1 t.2.2) K hK 0
  obtain ⟨MB,hMB,hDrift⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i)
    (fun i => contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i) K hK 0
  obtain ⟨MJ,hMJ,hLog⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds
    g hg L hL K hK 0
  let M := 1+MF+MG+MB+MJ
  have hM : 1 ≤ M := by dsimp only [M]; linarith
  have hMF' : MF ≤ M := by dsimp only [M]; linarith
  have hMG' : MG ≤ M := by dsimp only [M]; linarith
  have hMB' : MB ≤ M := by dsimp only [M]; linarith
  have hMJ' : MJ ≤ M := by dsimp only [M]; linarith
  let C_Q := 82+435*M
  refine ⟨C_Q,by dsimp only [C_Q]; positivity,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hs
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hb2 : 1 ≤ beta^2 := one_le_pow₀ hb
  have hr1 : r ≤ 1 := ((le_mul_of_one_le_right hr.le hb2).trans hs).trans heta1
  have hrb : r*beta ≤ 1 := by
    have hbSq : beta ≤ beta^2 := by nlinarith
    exact ((mul_le_mul_of_nonneg_left hbSq hr.le).trans hs).trans heta1
  have hr2 : r^2 ≤ r := by nlinarith
  have hr3 : r^3 ≤ r := by nlinarith [mul_le_mul_of_nonneg_left hr2 hr.le]
  have hr2b : r^2*beta ≤ r := by nlinarith [mul_le_mul_of_nonneg_left hrb hr.le]
  have hF (a : Fin 3) : ‖referenceMetricGramFrame g L (q,x) a‖ ≤ M := by
    apply le_trans _ hMF'
    simpa only [coordinateFieldWordPartial] using hFrame q hq x hx a [] (by simp)
  have hG (a c d : Fin 3) :
      |referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) a) c d| ≤ M := by
    apply le_trans _ hMG'
    simpa only [coordinateFieldWordPartial,Real.norm_eq_abs,
      referenceFrameConnectionJoint_eq g hg L] using hGamma q hq x hx (a,c,d) [] (by simp)
  have hB (a : Fin 3) : |normalizedSecondDriftFrameJoint g g2 L a (q,x)| ≤ M := by
    apply le_trans _ hMB'
    simpa only [coordinateFieldWordPartial,Real.norm_eq_abs] using hDrift q hq x hx a [] (by simp)
  have hJ (a : Fin 3) : |referenceRadiusHorizontalLogDerivative g L q
      (referenceRadius dr Ar p L) x a| ≤ M*beta := by
    rw [horizontalLog_eq_frameLog]
    have h := (hLog q hq dr hdr hdr1 Ar hAr p hp x hx hb [] (by simp)).1 a
    have h0 : |referenceFrameDerivative g L q a
        (fun y => Real.log (referenceRadius dr Ar p L y)) x| ≤ MJ*beta := by
      simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero,pow_one,beta,actualReferenceBeta] using h
    exact h0.trans (mul_le_mul_of_nonneg_right hMJ' hb0)
  have hConn (a : Fin 3) : lowerSConnectionWordMass g L q a x ≤ (9/2 : ℝ)*M := by
    unfold lowerSConnectionWordMass
    calc
      _ ≤ (1/2 : ℝ)*(∑ _c : Fin 3, ∑ _d : Fin 3, M) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ =>
          Finset.sum_le_sum (fun d _ => hG a c d))) (by norm_num)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
  have hTriple (a b : Fin 3) : (∑ k : Fin 3,
      |referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) a) k b|) ≤ 3*M := by
    exact (Finset.sum_le_sum (fun k _ => hG a k b)).trans_eq
      (by norm_num [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul])
  have hParent (a b : Fin 3) :
      ‖referenceMetricGramFrame g L (q,x) a‖ +
      2*|referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x a|+
      |referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x b|+
      (∑ k : Fin 3, |referenceFrameConnectionCoefficient g L q x
        (referenceMetricGramFrame g L (q,x) a) k b|)+
      lowerSConnectionWordMass g L q a x+lowerSConnectionWordMass g L q b x ≤ 16*M*beta := by
    have hMb : M ≤ M*beta := le_mul_of_one_le_right (by linarith) hb
    nlinarith [hF a,hJ a,hJ b,hTriple a b,hConn a,hConn b]
  have hQ (a b : Fin 3) : |referenceDensityPrincipalFrameCoefficient g g2 L q x a b| ≤ 3 :=
    abs_referenceDensityPrincipalFrameCoefficient_le_three g g2 hg hg2 L q x a b
  have hQsum : (∑ a : Fin 3, ∑ b : Fin 3,
      |referenceDensityPrincipalFrameCoefficient g g2 L q x a b|) ≤ 27 := by
    exact (Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hQ a b))).trans_eq
      (by norm_num [Fin.sum_univ_three])
  have hBsum : (∑ a : Fin 3, |normalizedSecondDriftFrameJoint g g2 L a (q,x)|) ≤ 3*M := by
    exact (Finset.sum_le_sum (fun a _ => hB a)).trans_eq
      (by norm_num [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul])
  have hMain : (∑ a : Fin 3, ∑ b : Fin 3,
      |referenceDensityPrincipalFrameCoefficient g g2 L q x a b| *
      (‖referenceMetricGramFrame g L (q,x) a‖ +
       2*|referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x a|+
       |referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x b|+
       (∑ k : Fin 3, |referenceFrameConnectionCoefficient g L q x
         (referenceMetricGramFrame g L (q,x) a) k b|)+
       lowerSConnectionWordMass g L q a x+lowerSConnectionWordMass g L q b x)) ≤ 432*M*beta := by
    calc
      _ ≤ ∑ _a : Fin 3, ∑ _b : Fin 3, 3*(16*M*beta) := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        exact mul_le_mul (hQ a b) (hParent a b) (by unfold lowerSConnectionWordMass; positivity) (by norm_num)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
  change r^2*(_)+r^2*(_)+2*r*(_)+r^3*(_) ≤ C_Q*r
  calc
    _ ≤ r^2*(432*M*beta)+r^2*(3*M)+2*r*27+r^3*27 := by
      exact add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hMain (sq_nonneg r))
        (mul_le_mul_of_nonneg_left hBsum (sq_nonneg r)))
        (mul_le_mul_of_nonneg_left hQsum (by positivity)))
        (mul_le_mul_of_nonneg_left hQsum (pow_nonneg hr.le 3))
    _ ≤ 432*M*r+3*M*r+54*r+27*r := by
      have hM0 : 0 ≤ M := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hr2b (by positivity : 0 ≤ 432*M),
        mul_le_mul_of_nonneg_left hr2 (by positivity : 0 ≤ 3*M)]
    _ ≤ C_Q*r := by dsimp only [C_Q]; nlinarith

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSZeroSWordBudget
