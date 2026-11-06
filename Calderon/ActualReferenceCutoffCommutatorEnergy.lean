import Calderon.ActualReferenceHorizontalHalfEnergy
import Calderon.ActualScaledHighFirstNativeRoomBounds
import Calderon.ActualRadiusScaledFirstActionNative
import Calderon.ActualScalarCutoffJointCoefficients
import Calderon.ActualDensityPrincipalFrameCoefficientBound
import Calderon.ActualLowerSSelfFormation

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift MetricOperator NormalCoordinatesFrame
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel SpectralWeightedGraph
  ReferenceDensityBounds ConformalDepth RadiusProfile

attribute [local irreducible] referenceHighAdjointCoordinateBoundaryFamily
  referenceHighAdjointJacobiBoundaryCorrectionFamily
  referenceAdjointThreeHalfRadialFamily
  referenceHighDensityFirstAction
  referenceHighHorizontalAction
  finiteCoreReferenceProfileEnergy

private lemma square_le_of_nonneg_le_product (a b c : ℝ) (ha : 0 ≤ a) (h : a ≤ b*c) :
    a^2 ≤ b^2*c^2 := by
  have hs := mul_self_le_mul_self ha h
  nlinarith only [hs]

private lemma norm_four_add_sq_le {V : Type*} [NormedAddCommGroup V] (a b c d : V) :
    ‖a+b+c+d‖^2 ≤ 4*(‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2) := by
  have hTriangle : ‖a+b+c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ :=
    (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _)))
      (le_refl _))
  have hSquare : ‖a+b+c+d‖^2 ≤ (‖a‖+‖b‖+‖c‖+‖d‖)^2 := by
    have hs := mul_self_le_mul_self (norm_nonneg (a+b+c+d)) hTriangle
    nlinarith only [hs]
  have hCauchy : (‖a‖+‖b‖+‖c‖+‖d‖)^2 ≤ 4*(‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2) := by
    nlinarith only [sq_nonneg (‖a‖-‖b‖), sq_nonneg (‖a‖-‖c‖),
      sq_nonneg (‖a‖-‖d‖), sq_nonneg (‖b‖-‖c‖), sq_nonneg (‖b‖-‖d‖),
      sq_nonneg (‖c‖-‖d‖)]
  exact hSquare.trans hCauchy

private lemma sum_three_norm_sq_le {V : Type*} [NormedAddCommGroup V] (v : Fin 3 → V) :
    (∑ i : Fin 3, ‖v i‖)^2 ≤ 3*(∑ i : Fin 3, ‖v i‖^2) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (‖v (0 : Fin 3)‖+(‖v (1 : Fin 3)‖+‖v (2 : Fin 3)‖))^2 ≤
    3*(‖v (0 : Fin 3)‖^2+(‖v (1 : Fin 3)‖^2+‖v (2 : Fin 3)‖^2))
  nlinarith only [sq_nonneg (‖v (0 : Fin 3)‖-‖v (1 : Fin 3)‖),
    sq_nonneg (‖v (0 : Fin 3)‖-‖v (2 : Fin 3)‖),
    sq_nonneg (‖v (1 : Fin 3)‖-‖v (2 : Fin 3)‖)]

private lemma norm_two_scalars_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a b M : ℝ) (hM : 0 ≤ M) (ha : |a| ≤ M) (hb : |b| ≤ M) (v : V) :
    ‖a • (b • v)‖ ≤ M^2*‖v‖ := by
  rw [smul_smul, norm_smul, Real.norm_eq_abs, abs_mul]
  have hprod : |a| * |b| ≤ M*M := mul_le_mul ha hb (abs_nonneg b) hM
  simpa only [pow_two] using mul_le_mul_of_nonneg_right hprod (norm_nonneg v)

private lemma cutoff_commutator_scalar_budget
    (M beta r U H Y Z E : ℝ)
    (hM : 1 ≤ M) (hb : 1 ≤ beta) (hr : 0 ≤ r)
    (hSmall : r*beta^2 ≤ 1) (hE : 0 ≤ E) (hU : 0 ≤ U) (_hH : 0 ≤ H)
    (hUE : beta*U ≤ E) (hHE : beta⁻¹*H ≤ E)
    (hY : Y ≤ 4*r^2*H+(24*M^2+12*M^4)*U)
    (hZ : Z ≤ 216*M^4*Y+288*M^4*r^2*U) :
    Z ≤ (10000*M^8/beta)*E := by
  have hbPos : 0 < beta := zero_lt_one.trans_le hb
  have hbNonneg : 0 ≤ beta := hbPos.le
  have hMNonneg : 0 ≤ M := zero_le_one.trans hM
  let t : ℝ := E/beta
  have ht : 0 ≤ t := div_nonneg hE hbNonneg
  have hUt : U ≤ t := by
    apply (le_div_iff₀ hbPos).2
    simpa only [mul_comm] using hUE
  have hHdiv : H/beta ≤ E := by
    simpa only [div_eq_mul_inv, mul_comm] using hHE
  have hHle : H ≤ E*beta := (div_le_iff₀ hbPos).1 hHdiv
  have hbSq : beta ≤ beta^2 := by
    nlinarith only [mul_nonneg hbNonneg (sub_nonneg.mpr hb)]
  have hbSqOne : 1 ≤ beta^2 := hb.trans hbSq
  have hrOne : r ≤ 1 := by
    calc
      r = r*1 := by ring
      _ ≤ r*beta^2 := mul_le_mul_of_nonneg_left hbSqOne hr
      _ ≤ 1 := hSmall
  have hrBeta : r*beta ≤ 1 := (mul_le_mul_of_nonneg_left hbSq hr).trans hSmall
  have hrBetaNonneg : 0 ≤ r*beta := mul_nonneg hr hbNonneg
  have hrBetaSq : (r*beta)^2 ≤ 1 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hrBeta)
      (add_nonneg zero_le_one hrBetaNonneg)]
  have hrScale : r^2*beta ≤ 1/beta := by
    apply (le_div_iff₀ hbPos).2
    calc
      (r^2*beta)*beta = (r*beta)^2 := by ring
      _ ≤ 1 := hrBetaSq
  have hRHt : r^2*H ≤ t := by
    calc
      r^2*H ≤ r^2*(E*beta) := mul_le_mul_of_nonneg_left hHle (sq_nonneg r)
      _ = (r^2*beta)*E := by ring
      _ ≤ (1/beta)*E := mul_le_mul_of_nonneg_right hrScale hE
      _ = t := by dsimp only [t]; ring
  have hrSqOne : r^2 ≤ 1 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hrOne) (add_nonneg zero_le_one hr)]
  have hRUt : r^2*U ≤ t := (mul_le_of_le_one_left hU hrSqOne).trans hUt
  have hMSqOne : 1 ≤ M^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hM) (add_nonneg hMNonneg zero_le_one)]
  have hMSqFourth : M^2 ≤ M^4 := by
    calc
      M^2 = M^2*1 := by ring
      _ ≤ M^2*M^2 := mul_le_mul_of_nonneg_left hMSqOne (sq_nonneg M)
      _ = M^4 := by ring
  have hMFourthOne : 1 ≤ M^4 := hMSqOne.trans hMSqFourth
  have hMFourthEighth : M^4 ≤ M^8 := by
    calc
      M^4 = M^4*1 := by ring
      _ ≤ M^4*M^4 := mul_le_mul_of_nonneg_left hMFourthOne (pow_nonneg hMNonneg 4)
      _ = M^8 := by ring
  have hMEighthNonneg : 0 ≤ M^8 := pow_nonneg hMNonneg 8
  have hYFirst : Y ≤ (4+24*M^2+12*M^4)*t := by
    calc
      Y ≤ 4*r^2*H+(24*M^2+12*M^4)*U := hY
      _ = 4*(r^2*H)+(24*M^2+12*M^4)*U := by ring
      _ ≤ 4*t+(24*M^2+12*M^4)*t := add_le_add
        (mul_le_mul_of_nonneg_left hRHt (by norm_num))
        (mul_le_mul_of_nonneg_left hUt (by positivity))
      _ = (4+24*M^2+12*M^4)*t := by ring
  have hYCoeff : 4+24*M^2+12*M^4 ≤ 40*M^4 := by
    linarith only [hMSqFourth, hMFourthOne]
  have hYScaled : Y ≤ 40*M^4*t :=
    hYFirst.trans (mul_le_mul_of_nonneg_right hYCoeff ht)
  have hFinalCoeff : 8640*M^8+288*M^4 ≤ 10000*M^8 := by
    linarith only [hMFourthEighth, hMEighthNonneg]
  calc
    Z ≤ 216*M^4*Y+288*M^4*r^2*U := hZ
    _ = 216*M^4*Y+288*M^4*(r^2*U) := by ring
    _ ≤ 216*M^4*(40*M^4*t)+288*M^4*t := add_le_add
      (mul_le_mul_of_nonneg_left hYScaled (by positivity))
      (mul_le_mul_of_nonneg_left hRUt (by positivity))
    _ = (8640*M^8+288*M^4)*t := by ring
    _ ≤ (10000*M^8)*t := mul_le_mul_of_nonneg_right hFinalCoeff ht
    _ = (10000*M^8/beta)*E := by dsimp only [t]; ring

private lemma norm_four_operator_combination_sq_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Q J A : V →L[ℝ] W) (v : V) (z : W) (r d M : ℝ)
    (hM : 0 ≤ M) (hr : 0 ≤ r) (hrOne : r ≤ 1)
    (hQ : ‖Q‖ ≤ M) (hJ : ‖J‖ ≤ M) (hA : ‖A‖ ≤ M) (hd : |d| ≤ M) :
    ‖r • z+Q v+r^2 • J v+d • A v‖^2 ≤
      4*(r^2*‖z‖^2+M^2*‖v‖^2+M^2*‖v‖^2+M^4*‖v‖^2) := by
  have hrSq : r^2 ≤ 1 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hrOne) (add_nonneg zero_le_one hr)]
  have hQval : ‖Q v‖ ≤ M*‖v‖ :=
    (Q.le_opNorm v).trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg v))
  have hJval : ‖r^2 • J v‖ ≤ M*‖v‖ := by
    calc
      ‖r^2 • J v‖ = r^2*‖J v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
      _ ≤ ‖J v‖ := mul_le_of_le_one_left (norm_nonneg (J v)) hrSq
      _ ≤ M*‖v‖ := (J.le_opNorm v).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg v))
  have hAval : ‖d • A v‖ ≤ M^2*‖v‖ := by
    calc
      ‖d • A v‖ = |d| * ‖A v‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ M*(M*‖v‖) := mul_le_mul hd
        ((A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg v)))
        (norm_nonneg (A v)) hM
      _ = M^2*‖v‖ := by ring
  have hQsq : ‖Q v‖^2 ≤ M^2*‖v‖^2 :=
    square_le_of_nonneg_le_product ‖Q v‖ M ‖v‖ (norm_nonneg (Q v)) hQval
  have hJsq : ‖r^2 • J v‖^2 ≤ M^2*‖v‖^2 :=
    square_le_of_nonneg_le_product ‖r^2 • J v‖ M ‖v‖ (norm_nonneg (r^2 • J v)) hJval
  have hAsq : ‖d • A v‖^2 ≤ M^4*‖v‖^2 := by
    have hs : ‖d • A v‖^2 ≤ (M^2)^2*‖v‖^2 :=
      square_le_of_nonneg_le_product ‖d • A v‖ (M^2) ‖v‖ (norm_nonneg (d • A v)) hAval
    nlinarith only [hs]
  have hRaw : ‖r • z‖^2 = r^2*‖z‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hFour := norm_four_add_sq_le (r • z) (Q v) (r^2 • J v) (d • A v)
  rw [hRaw] at hFour
  exact hFour.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add (le_refl _) hQsq) hJsq) hAsq) (by norm_num))

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

private lemma sum_scaled_first_action_sq_le
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (x : R3) (M : ℝ)
    (hM : 0 ≤ M) (hR : DifferentiableAt ℝ R x) (hr : 0 < R x) (hrOne : R x ≤ 1)
    (hDR : ‖fderiv ℝ R x‖ ≤ 1)
    (hQ : ∀ i : Fin 3, ‖referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(x,R x)) i‖ ≤ M)
    (hJ : ∀ i : Fin 3, ‖referenceHighAdjointJacobiBoundaryCorrectionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(x,R x)) i‖ ≤ M)
    (hA : ‖referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(x,R x))‖ ≤ M)
    (hv : ∀ i : Fin 3, ‖conformalReferenceGramFrameOperatorJoint g L (q,x)
      (NormalCoordinatesFrame.coordinateVector i)‖ ≤ M) :
    (∑ i : Fin 3, ‖R x • referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x i‖^2) ≤
      4*(R x)^2*(∑ i : Fin 3, ‖referenceHighHorizontalAction g L q u x i‖^2)+
        (24*M^2+12*M^4)*‖u x‖^2 := by
  let Q : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    fun i => referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(x,R x)) i
  let J : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    fun i => referenceHighAdjointJacobiBoundaryCorrectionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(x,R x)) i
  let A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(x,R x))
  have hEach (i : Fin 3) :
      ‖R x • referenceHighDensityFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x i‖^2 ≤
      4*((R x)^2*‖referenceHighHorizontalAction g L q u x i‖^2+
        M^2*‖u x‖^2+M^2*‖u x‖^2+M^4*‖u x‖^2) := by
    let v : R3 := conformalReferenceGramFrameOperatorJoint g L (q,x) (NormalCoordinatesFrame.coordinateVector i)
    have hCoeff : |fderiv ℝ R x v| ≤ M := by
      calc
        |fderiv ℝ R x v| = ‖fderiv ℝ R x v‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ R x‖*‖v‖ := (fderiv ℝ R x).le_opNorm v
        _ ≤ 1*M := mul_le_mul hDR (hv i) (norm_nonneg v) zero_le_one
        _ = M := one_mul M
    have hIdentity := radius_smul_referenceHighDensityFirstAction_eq_inverseFree
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x i hR hr.ne'
    calc
      _ = ‖R x • referenceHighHorizontalAction g L q u x i+Q i (u x)+
          (R x)^2 • J i (u x)+fderiv ℝ R x v • A (u x)‖^2 :=
        congrArg (fun z : SphereSobolev (1/2 : ℝ) => ‖z‖^2) hIdentity
      _ ≤ _ := norm_four_operator_combination_sq_le (Q i) (J i) A (u x)
        (referenceHighHorizontalAction g L q u x i) (R x) (fderiv ℝ R x v) M
        hM hr.le hrOne (hQ i) (hJ i) hA hCoeff
  calc
    _ ≤ ∑ i : Fin 3, 4*((R x)^2*‖referenceHighHorizontalAction g L q u x i‖^2+
        M^2*‖u x‖^2+M^2*‖u x‖^2+M^4*‖u x‖^2) :=
      Finset.sum_le_sum (fun i _ => hEach i)
    _ = _ := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      ring

private lemma norm_full_cutoff_commutator_le
    (g2 : MatrixField) (q : ℝ) (R theta : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (x : R3) (M : ℝ) (hM : 0 ≤ M) (hr : 0 ≤ R x)
    (hPrincipal : ∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ M)
    (hFirst : ∀ i : Fin 3, |referenceFrameScalarDerivative g L q theta x i| ≤ M)
    (hHessian : ∀ i j : Fin 3, |referenceFrameScalarHessian g L q theta x i j| ≤ M)
    (hDrift : ∀ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ M) :
    ‖referenceDensityScalarCutoffCommutator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R theta u x‖ ≤
    6*M^2*(∑ i : Fin 3, ‖R x • referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x i‖)+12*M^2*R x*‖u x‖ := by
  let r := R x
  let D := fun i : Fin 3 => referenceHighDensityFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x i
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let P := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q x i j
  let d := fun i : Fin 3 => referenceFrameScalarDerivative g L q theta x i
  let Hess := fun i j : Fin 3 => referenceFrameScalarHessian g L q theta x i j
  let drift := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,x)
  let TP := fun i j : Fin 3 => P i j • (d i • (r • D j))+
    P i j • (d j • (r • D i))+P i j • (Hess i j • (r • I (u x)))
  let TB := fun i : Fin 3 => drift i • (d i • (r • I (u x)))
  have hI : ‖r • I (u x)‖ ≤ r*‖u x‖ := by
    calc
      ‖r • I (u x)‖ = r*‖I (u x)‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
      _ ≤ r*‖u x‖ := mul_le_mul_of_nonneg_left
        ((I.le_opNorm (u x)).trans (mul_le_of_le_one_left (norm_nonneg _)
          (norm_sphereSobolevInclusionL_le (3/2 : ℝ) (1/2 : ℝ) (by norm_num)))) hr
  have hTP (i j : Fin 3) : ‖TP i j‖ ≤
      M^2*‖r • D j‖+M^2*‖r • D i‖+M^2*(r*‖u x‖) := by
    have h1 := norm_two_scalars_le (P i j) (d i) M hM (hPrincipal i j) (hFirst i) (r • D j)
    have h2 := norm_two_scalars_le (P i j) (d j) M hM (hPrincipal i j) (hFirst j) (r • D i)
    have h3 := norm_two_scalars_le (P i j) (Hess i j) M hM
      (hPrincipal i j) (hHessian i j) (r • I (u x))
    dsimp only [TP]
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add h1 h2))
      (h3.trans (mul_le_mul_of_nonneg_left hI (sq_nonneg M))))
  have hTB (i : Fin 3) : ‖TB i‖ ≤ M^2*(r*‖u x‖) :=
    (norm_two_scalars_le (drift i) (d i) M hM (hDrift i) (hFirst i) (r • I (u x))).trans
      (mul_le_mul_of_nonneg_left hI (sq_nonneg M))
  have hEquation : referenceDensityScalarCutoffCommutator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R theta u x =
      (∑ i : Fin 3, ∑ j : Fin 3, TP i j)+(∑ i : Fin 3, TB i) := by
    change r • ((∑ i : Fin 3, ∑ j : Fin 3, P i j •
      (d i • D j+d j • D i+Hess i j • I (u x)))+
      (∑ i : Fin 3, drift i • (d i • I (u x)))) = _
    simp only [smul_add, Finset.smul_sum]
    apply congrArg₂ (fun v z => v+z)
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [TP]
      module
    · apply Finset.sum_congr rfl
      intro i _
      dsimp only [TB]
      module
  rw [hEquation]
  calc
    _ ≤ ‖∑ i : Fin 3, ∑ j : Fin 3, TP i j‖+‖∑ i : Fin 3, TB i‖ := norm_add_le _ _
    _ ≤ (∑ i : Fin 3, ∑ j : Fin 3, ‖TP i j‖)+(∑ i : Fin 3, ‖TB i‖) :=
      add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _)))
        (norm_sum_le _ _)
    _ ≤ (∑ i : Fin 3, ∑ j : Fin 3,
        (M^2*‖r • D j‖+M^2*‖r • D i‖+M^2*(r*‖u x‖)))+
        (∑ _i : Fin 3, M^2*(r*‖u x‖)) := add_le_add
      (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hTP i j)))
      (Finset.sum_le_sum (fun i _ => hTB i))
    _ = _ := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      ring

/-- The actual full physical scalar commutator has an input-energy bound whose
constant precedes all later profiles and finite inputs. -/
theorem exists_referenceDensityScalarCutoffCommutator_referenceProfileEnergy_bound
    (hreg : FixedDirichletRegularity) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (theta : R3 → ℝ) (hTheta : ContDiff ℝ ∞ theta) :
    ∃ Ctheta : ℝ, 1 ≤ Ctheta ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ (R : R3 → ℝ) (x : R3), ‖x-y0‖ ≤ 4*ρ →
      DifferentiableAt ℝ R x → 0 < R x → R x ≤ 4*ρ → ‖fderiv ℝ R x‖ ≤ 1 →
      ∀ beta : ℝ, 1 ≤ beta → R x*beta^2 ≤ 1 →
      ∀ F : smoothCompactFiniteSphereCore hO hD,
      ‖referenceDensityScalarCutoffCommutator g L y0 Φ B ε C ρ H a w hData hg
        hcalc hF hO hD τ0 g2 q R theta (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) x‖^2 ≤
      (Ctheta/beta)*finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x := by
  obtain ⟨G, _hG, hGeometry⟩ := exists_actual_room_referenceScaledHighFirst_coefficients_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  obtain ⟨T, _hT, hCutoff⟩ := exists_compact_referenceDensity_cutoff_scalar_coefficients_bound
    g g2 hg hg2 L theta hTheta (closedBall y0 (4*ρ)) (isCompact_closedBall _ _)
  let M : ℝ := max 3 (max G T)
  have hGM : G ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hTM : T ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hM3 : 3 ≤ M := le_max_left _ _
  have hM1 : 1 ≤ M := by linarith only [hM3]
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hM2 : 1 ≤ M^2 := by nlinarith only [hM1, sq_nonneg (M-1)]
  have hM4 : 1 ≤ M^4 := by nlinarith only [hM2, sq_nonneg (M^2-1)]
  have hM8 : 1 ≤ M^8 := by nlinarith only [hM4, sq_nonneg (M^4-1)]
  refine ⟨10000*M^8, by linarith only [hM8], ?_⟩
  intro q hq R x hx hR hr hrRoom hDR beta hb hSmall F
  let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  let U : ℝ := ‖u x‖^2
  let HH : ℝ := ∑ i : Fin 3, ‖referenceHighHorizontalAction g L q u x i‖^2
  let Y : ℝ := ∑ i : Fin 3, ‖R x • referenceHighDensityFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x i‖^2
  let CC := referenceDensityScalarCutoffCommutator
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R theta u x
  let EE : ℝ := finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hb2 : 1 ≤ beta^2 := by nlinarith only [hb, sq_nonneg (beta-1)]
  have hrOne : R x ≤ 1 :=
    (show R x ≤ R x*beta^2 by nlinarith only [mul_le_mul_of_nonneg_left hb2 hr.le]).trans hSmall
  have hAbs : |R x| ≤ 4*ρ := by simpa only [abs_of_pos hr] using hrRoom
  have hGeom (i : Fin 3) := hGeometry q hq x hx (R x) hAbs i
  have hQ (i : Fin 3) := (hGeom i).1.trans hGM
  have hJ (i : Fin 3) := (hGeom i).2.1.trans hGM
  have hA := (hGeom 0).2.2.1.trans hGM
  have hv (i : Fin 3) := (hGeom i).2.2.2.2.2.trans hGM
  have hY : Y ≤ 4*(R x)^2*HH+(24*M^2+12*M^4)*U :=
    sum_scaled_first_action_sq_le g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      q R u x M hM0 hR hr hrOne hDR hQ hJ hA hv
  have hxBall : x ∈ closedBall y0 (4*ρ) := by simpa only [mem_closedBall, dist_eq_norm] using hx
  have hPrincipal (i j : Fin 3) : |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ M :=
    (abs_referenceDensityPrincipalFrameCoefficient_le_three g g2 hg hg2 L q x i j).trans hM3
  have hFirst (i : Fin 3) := (hCutoff q hq x hxBall i 0).1.trans hTM
  have hHessian (i j : Fin 3) := (hCutoff q hq x hxBall i j).2.1.trans hTM
  have hDrift (i : Fin 3) := (hCutoff q hq x hxBall i 0).2.2.trans hTM
  have hComm := norm_full_cutoff_commutator_le
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 q R theta u x M hM0 hr.le hPrincipal hFirst hHessian hDrift
  let S : ℝ := ∑ i : Fin 3, ‖R x • referenceHighDensityFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x i‖
  have hS : S^2 ≤ 3*Y := sum_three_norm_sq_le (fun i : Fin 3 =>
    R x • referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x i)
  have hCommSquare : ‖CC‖^2 ≤ (6*M^2*S+12*M^2*R x*‖u x‖)^2 := by
    have hs := mul_self_le_mul_self (norm_nonneg CC) hComm
    nlinarith only [hs]
  have hTwo : (6*M^2*S+12*M^2*R x*‖u x‖)^2 ≤
      2*(6*M^2*S)^2+2*(12*M^2*R x*‖u x‖)^2 := by
    nlinarith only [sq_nonneg (6*M^2*S-12*M^2*R x*‖u x‖)]
  have hZ : ‖CC‖^2 ≤ 216*M^4*Y+288*M^4*(R x)^2*U := by
    calc
      ‖CC‖^2 ≤ (6*M^2*S+12*M^2*R x*‖u x‖)^2 := hCommSquare
      _ ≤ 2*(6*M^2*S)^2+2*(12*M^2*R x*‖u x‖)^2 := hTwo
      _ = 72*M^4*S^2+288*M^4*(R x)^2*U := by dsimp only [U]; ring
      _ ≤ 216*M^4*Y+288*M^4*(R x)^2*U := by
        have hs := mul_le_mul_of_nonneg_left hS (show 0 ≤ 72*M^4 by positivity)
        nlinarith only [hs]
  have hUE : beta*U ≤ EE :=
    ActualLowerSSelfFormation.beta_mul_norm_higherSInput_sq_le_referenceProfileEnergy
      g L hg hO hD q beta hb0 F x
  have hHE : beta⁻¹*HH ≤ EE :=
    inv_beta_mul_sum_norm_referenceHighHorizontalAction_sq_le_referenceProfileEnergy
      hO hD g hg L q beta hb0 F x
  have hEE : 0 ≤ EE := finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q beta hb0 F x
  have hUNonneg : 0 ≤ U := sq_nonneg ‖u x‖
  have hHHNonneg : 0 ≤ HH := Finset.sum_nonneg
    (fun i _ => sq_nonneg ‖referenceHighHorizontalAction g L q u x i‖)
  have hBudget : ‖CC‖^2 ≤ (10000*M^8/beta)*EE :=
    cutoff_commutator_scalar_budget M beta (R x) U HH Y (‖CC‖^2) EE hM1 hb hr.le hSmall
      hEE hUNonneg hHHNonneg hUE hHE hY hZ
  change ‖CC‖^2 ≤ (10000*M^8/beta)*EE
  exact hBudget

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
