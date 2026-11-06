import Calderon.ActualOrdinaryOperatorRadialJets
import Calderon.NativePolynomialBallSobolev

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory MvPolynomial
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume ConnectionError DriftBootstrap

def polynomialEuclideanMap : (Fin 3 → ℝ) →L[ℝ] R3 :=
  ∑ i : Fin 3, (ContinuousLinearMap.proj i).smulRight (coordinateVector i)

theorem polynomialEuclideanMap_apply (x : Fin 3 → ℝ) (i : Fin 3) :
    polynomialEuclideanMap x i = x i := by
  classical
  simp [polynomialEuclideanMap,coordinateVector,Pi.single_apply,mul_ite]

theorem polynomialCoordinateMap_polynomialEuclideanMap (x : Fin 3 → ℝ) :
    polynomialCoordinateMap (polynomialEuclideanMap x) = x := by
  funext i
  exact polynomialEuclideanMap_apply x i

theorem polynomialEuclideanMap_polynomialCoordinateMap (x : R3) :
    polynomialEuclideanMap (polynomialCoordinateMap x) = x := by
  ext i
  exact polynomialEuclideanMap_apply (polynomialCoordinateMap x) i

theorem fderiv_polynomialEval_eq_pi (p : MvPolynomial (Fin 3) ℝ) (x v : R3) :
    fderiv ℝ (fun y : R3 => eval (polynomialCoordinateMap y) p) x v =
      fderiv ℝ (fun y : Fin 3 → ℝ => eval y p)
        (polynomialCoordinateMap x) (polynomialCoordinateMap v) := by
  rw [(hasFDerivAt_polynomialEval p x).fderiv,
    (GreenRadialTrace.hasFDerivAt_eval p (polynomialCoordinateMap x)).fderiv,
    ContinuousLinearMap.comp_apply]

def polynomialBallSobolevLinearMap (k : ℕ) :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] BallSobolev k where
  toFun := polynomialBallSobolev k
  map_add' := by
    intro p q
    apply TauCeti.Wkp.ext k
    rw [TauCeti.Wkp.value_add]
    apply Lp.ext
    filter_upwards [value_polynomialBallSobolev_ae k (p+q),
      value_polynomialBallSobolev_ae k p,value_polynomialBallSobolev_ae k q,
      Lp.coeFn_add (TauCeti.Wkp.value k (polynomialBallSobolev k p))
        (TauCeti.Wkp.value k (polynomialBallSobolev k q))] with x hsum hp hq hadd
    rw [hsum,hadd,Pi.add_apply,hp,hq,map_add]
  map_smul' := by
    intro c p
    apply TauCeti.Wkp.ext k
    rw [TauCeti.Wkp.value_smul]
    change TauCeti.Wkp.value k (polynomialBallSobolev k (c • p)) =
      c • TauCeti.Wkp.value k (polynomialBallSobolev k p)
    apply Lp.ext
    filter_upwards [value_polynomialBallSobolev_ae k (c • p),
      value_polynomialBallSobolev_ae k p,
      Lp.coeFn_smul c (TauCeti.Wkp.value k (polynomialBallSobolev k p))] with x hcp hp hsmul
    rw [hcp,hsmul,Pi.smul_apply,hp,MvPolynomial.smul_eval]
    rfl

theorem ordinaryLowerOrderCoordinateDerivativeL_polynomialBallSobolev
    (hcalc : FixedSobolevCalculus) (s : ℕ) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    ordinaryLowerOrderCoordinateDerivativeL hcalc s i (polynomialBallSobolev (s+2) p) =
      polynomialBallSobolev s (pderiv i p) := by
  change TauCeti.Wkp.lowerOrder s
    (unitBallCoordinateDerivativeL hcalc (s+1) i (polynomialBallSobolev (s+2) p)) = _
  rw [unitBallCoordinateDerivativeL_polynomialBallSobolev]
  exact lowerOrder_smoothBallSobolev s (smoothPolynomialData (pderiv i p))

theorem nativePolynomial_drift_operator
    (hcalc : FixedSobolevCalculus) (s : ℕ) (d : R3) (p : MvPolynomial (Fin 3) ℝ) :
    (∑ i : Fin 3, (d i) • ordinaryLowerOrderCoordinateDerivativeL hcalc s i)
      (polynomialBallSobolev (s+2) p) =
        polynomialBallSobolev s (GreenRadialTrace.driftDerivative (polynomialCoordinateMap d) p) := by
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply]
  simp_rw [ordinaryLowerOrderCoordinateDerivativeL_polynomialBallSobolev hcalc s]
  change (∑ i : Fin 3, (d i) • polynomialBallSobolevLinearMap s (pderiv i p)) =
    polynomialBallSobolevLinearMap s (GreenRadialTrace.driftDerivative (polynomialCoordinateMap d) p)
  rw [GreenRadialTrace.driftDerivative,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← MvPolynomial.smul_eq_C_mul,map_smul]
  rfl

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem referenceOrdinaryStrongDriftFamily_zero_polynomial
    (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (p : MvPolynomial (Fin 3) ℝ) :
    referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0)
      (polynomialBallSobolev (s+2) p) = -polynomialBallSobolev s (AngularPolynomial.laplacian p) := by
  rw [referenceOrdinaryStrongDriftFamily_zero_apply g L y0 Φ B ε C ρ H a w hData
    hcalc s q hq y hy]
  simp_rw [unitBallCoordinateDerivativeL_polynomialBallSobolev hcalc (s+1),
    unitBallCoordinateDerivativeL_polynomialBallSobolev hcalc s]
  change -(∑ i : Fin 3, polynomialBallSobolevLinearMap s (pderiv i (pderiv i p))) =
    -polynomialBallSobolevLinearMap s (AngularPolynomial.laplacian p)
  rw [AngularPolynomial.laplacian,map_sum]

theorem hasDerivAt_referenceOrdinaryStrongDriftFamily_polynomial_zero
    (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (p : MvPolynomial (Fin 3) ℝ) :
    HasDerivAt
      (fun r : ℝ => referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData
        hcalc s q (y,r) (polynomialBallSobolev (s+2) p))
      (-polynomialBallSobolev s (GreenRadialTrace.driftDerivative
        (polynomialCoordinateMap (referenceCenterDrift g L q y)) p)) 0 := by
  have hj := (hasDerivAt_referenceOrdinaryStrongDriftFamily_zero g L y0 Φ B ε C ρ H a w
    hData hcalc s q hq y hy).clm_apply (hasDerivAt_const (0 : ℝ) (polynomialBallSobolev (s+2) p))
  have hjet : HasDerivAt
      (fun r : ℝ => referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData
        hcalc s q (y,r) (polynomialBallSobolev (s+2) p))
      (-((∑ i : Fin 3, (referenceCenterDrift g L q y i) •
        ordinaryLowerOrderCoordinateDerivativeL hcalc s i)
          (polynomialBallSobolev (s+2) p))) 0 := by
    simpa only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.map_zero,add_zero] using hj
  rw [nativePolynomial_drift_operator hcalc s (referenceCenterDrift g L q y) p] at hjet
  exact hjet

theorem referenceOrdinaryStrongDriftFamily_driftFirstVariation_forcing
    (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (k : ℕ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p.IsHomogeneous k) (hΔ : AngularPolynomial.laplacian p = 0) :
    referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0)
      (polynomialBallSobolev (s+2) (GreenRadialTrace.driftFirstVariation k
        (polynomialCoordinateMap (referenceCenterDrift g L q y)) p)) =
      polynomialBallSobolev s (GreenRadialTrace.driftDerivative
        (polynomialCoordinateMap (referenceCenterDrift g L q y)) p) := by
  rw [referenceOrdinaryStrongDriftFamily_zero_polynomial g L y0 Φ B ε C ρ H a w hData
    hcalc s q hq y hy]
  let d := polynomialCoordinateMap (referenceCenterDrift g L q y)
  let u1 := GreenRadialTrace.driftFirstVariation k d p
  apply TauCeti.Wkp.ext s
  change TauCeti.Wkp.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (-polynomialBallSobolev s (AngularPolynomial.laplacian u1)) =
    TauCeti.Wkp.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (polynomialBallSobolev s (GreenRadialTrace.driftDerivative d p))
  rw [map_neg]
  simp only [TauCeti.Wkp.valueL_apply]
  apply Lp.ext
  filter_upwards [value_polynomialBallSobolev_ae s (AngularPolynomial.laplacian u1),
    value_polynomialBallSobolev_ae s (GreenRadialTrace.driftDerivative d p),
    Lp.coeFn_neg (TauCeti.Wkp.value s (polynomialBallSobolev s (AngularPolynomial.laplacian u1)))]
    with z hLap hDrift hNeg
  rw [hNeg,Pi.neg_apply,hLap,hDrift]
  have hCanon := GreenRadialTrace.cartesianLaplacian_driftFirstVariation hp hΔ d (fun i => z i)
  rw [GreenRadialTrace.cartesianLaplacian_eval,GreenRadialTrace.fderiv_eval_apply] at hCanon
  change -eval (fun i => z i) (AngularPolynomial.laplacian u1) =
    eval (fun i => z i) (GreenRadialTrace.driftDerivative d p)
  simp only [GreenRadialTrace.driftDerivative,map_sum,map_mul,eval_C]
  linarith

theorem polynomialEval_driftFirstVariation_zero_on_sphere
    (k : ℕ) (d : R3) (p : MvPolynomial (Fin 3) ℝ) (z : R3) (hz : ‖z‖ = 1) :
    eval (polynomialCoordinateMap z)
      (GreenRadialTrace.driftFirstVariation k (polynomialCoordinateMap d) p) = 0 := by
  have hs : ∑ i : Fin 3, (polynomialCoordinateMap z i)^2 = 1 := by
    simpa only [polynomialCoordinateMap_apply,hz,one_pow] using
      (EuclideanSpace.real_norm_sq_eq z).symm
  exact GreenRadialTrace.eval_driftFirstVariation_eq_zero k (polynomialCoordinateMap d) p
    (polynomialCoordinateMap z) hs

theorem fderiv_polynomialEval_driftFirstVariation_radial
    (k : ℕ) (hk : 1 ≤ k) (d : R3) (p : MvPolynomial (Fin 3) ℝ)
    (z : R3) (hz : ‖z‖ = 1) :
    fderiv ℝ (fun x : R3 => eval (polynomialCoordinateMap x)
      (GreenRadialTrace.driftFirstVariation k (polynomialCoordinateMap d) p)) z z =
      -(2*(k : ℝ)+1)⁻¹ * fderiv ℝ
        (fun x : R3 => eval (polynomialCoordinateMap x) p) z d := by
  have hs : ∑ i : Fin 3, (polynomialCoordinateMap z i)^2 = 1 := by
    simpa only [polynomialCoordinateMap_apply,hz,one_pow] using
      (EuclideanSpace.real_norm_sq_eq z).symm
  rw [fderiv_polynomialEval_eq_pi,fderiv_polynomialEval_eq_pi]
  exact GreenRadialTrace.fderiv_driftFirstVariation_three_at_sphere hk
    (polynomialCoordinateMap d) p (polynomialCoordinateMap z) hs

end OAI.AnisotropicCalderon.DirichletFamily
