import Calderon.ActualDensityCovariantGroupedNormalForm
import Calderon.ActualNativeLeadingCovariantRadiusCancellation
import Calderon.ScaledContinuousLinearMapThreeSum

/-! Ordered actual identity, with every native correction retained. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceDensityCovariantSecondAction
  referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceNativeMovingAdjointParametricCorrection referenceMetricGramFrame
  referenceFrameConnectionCoefficient sphereSobolevInclusionL
  sphereSobolevAngularCoordinateTransposeL referenceRadialEndpointInvertibleLocus

lemma referenceDensityCovariantSecondAction_leading_part
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (i j : Fin 3) (hr : R y ≠ 0) (hu : ContDiffAt ℝ ∞ u y)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let D : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => referenceHighWeightedHorizontalAction g L q R u x k
    let V : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => (R x)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k (u x)
    let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x =>
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) k (u x)) +
      R x • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k (u x)
    let Klo : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
          ((q,y),fderiv ℝ R y) i) +
      R y • referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
    referenceDensityCovariantSecondAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j =
      (referenceLowerWeightedHorizontalAction g L q R (D j) y i -
        ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j • sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (D k y)) +
      (R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j (D i y) +
      (R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D j y) +
      ((R y)⁻¹)^2 • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j (u y)) +
      referenceLowerWeightedHorizontalAction g L q R (K j) y i +
      (R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (K j y) +
      Klo (D j y) + Klo (V j y) + Klo (K j y) -
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j • sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (K k y) := by
  trace "COVARIANT_LEADING_ENTER"
  dsimp only
  let D : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => referenceHighWeightedHorizontalAction g L q R u x k
  let V : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => (R x)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k (u x)
  let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x =>
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) k (u x)) +
      R x • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k (u x)
  let Klo : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
          ((q,y),fderiv ℝ R y) i) +
      R y • referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  let F0 : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) k (u x))
  let E0 : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => R x • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k (u x)
  let W : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => D k x+V k x+K k x
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Alo := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) k
  let Gamma := fun k : Fin 3 => referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j
  change referenceDensityCovariantSecondAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j =
      (referenceLowerWeightedHorizontalAction g L q R (D j) y i -
        ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j • sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (D k y)) +
      (R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j (D i y) +
      (R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D j y) +
      ((R y)⁻¹)^2 • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j (u y)) +
      referenceLowerWeightedHorizontalAction g L q R (K j) y i +
      (R y)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (K j y) +
      Klo (D j y) + Klo (V j y) + Klo (K j y) -
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j • sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (K k y)
  have hGrouped := referenceDensityCovariantSecondAction_grouped_normal_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR u y hy i j hr hu hInv hp
  have hNormalGrouped : referenceDensityCovariantSecondAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j =
      referenceLowerWeightedHorizontalAction g L q R (W j) y i + (R y)⁻¹ • Alo i (W j y) + Klo (W j y) -
        ∑ k : Fin 3, Gamma k • Iout (W k y) := hGrouped.1
  have hDistribution : referenceLowerWeightedHorizontalAction g L q R (W j) y i =
      referenceLowerWeightedHorizontalAction g L q R (D j) y i + referenceLowerWeightedHorizontalAction g L q R (V j) y i + referenceLowerWeightedHorizontalAction g L q R (K j) y i := hGrouped.2
  trace "COVARIANT_LEADING_GROUPED_PARENT_READY"
  have hCancellation := referenceLeadingRadiusAngularAction_covariant_cancellation
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR y hy i j hr u
      (hu.differentiableAt (by simp))
  trace "COVARIANT_LEADING_CANCELLATION_PARENT_READY"
  have hCovariant : referenceLowerWeightedHorizontalAction g L q R (V j) y i -
      (∑ k : Fin 3, Gamma k • Iout (V k y)) = (R y)⁻¹ • Alo j (D i y) := by
    simpa only [D,V,Alo,Gamma,Iout,referenceLowerWeightedHorizontalAction,
      referenceHighWeightedHorizontalAction] using hCancellation
  have hCovariantAdd := (sub_eq_iff_eq_add).mp hCovariant
  trace "COVARIANT_LEADING_CANCELLATION_READY"
  have hAngular : (R y)⁻¹ • Alo i (W j y) =
      (R y)⁻¹ • Alo i (D j y) + (R y)⁻¹ • Alo i (V j y) +
        (R y)⁻¹ • Alo i (K j y) := by
    exact smul_map_add_add (Alo i) (R y)⁻¹ (D j y) (V j y) (K j y)
  trace "COVARIANT_LEADING_ANGULAR_DISTRIBUTION_READY"
  have hCorrection : Klo (W j y) = Klo (D j y)+Klo (V j y)+Klo (K j y) := by
    have hOuter := Klo.map_add (D j y+V j y) (K j y)
    have hInner := congrArg
      (fun z : SphereSobolev (-(1/2 : ℝ)) => z+Klo (K j y))
      (Klo.map_add (D j y) (V j y))
    exact hOuter.trans hInner
  trace "COVARIANT_LEADING_CORRECTION_DISTRIBUTION_READY"
  have hConnection : (∑ k : Fin 3, Gamma k • Iout (W k y)) =
      (∑ k : Fin 3, Gamma k • Iout (D k y)) +
      (∑ k : Fin 3, Gamma k • Iout (V k y)) +
      (∑ k : Fin 3, Gamma k • Iout (K k y)) := by
    have hPoint (k : Fin 3) : Gamma k • Iout (W k y) =
        Gamma k • Iout (D k y)+Gamma k • Iout (V k y)+Gamma k • Iout (K k y) := by
      exact smul_map_add_add Iout (Gamma k) (D k y) (V k y) (K k y)
    have hSum : (∑ k : Fin 3, Gamma k • Iout (W k y)) =
        ∑ k : Fin 3, (Gamma k • Iout (D k y)+Gamma k • Iout (V k y)+Gamma k • Iout (K k y)) :=
      Finset.sum_congr rfl (fun k _ => hPoint k)
    trace "COVARIANT_LEADING_CONNECTION_POINT_SUM_READY"
    let fD : Fin 3 → SphereSobolev (-(1/2 : ℝ)) := fun k => Gamma k • Iout (D k y)
    let fV : Fin 3 → SphereSobolev (-(1/2 : ℝ)) := fun k => Gamma k • Iout (V k y)
    let fK : Fin 3 → SphereSobolev (-(1/2 : ℝ)) := fun k => Gamma k • Iout (K k y)
    have hOuter : (∑ k : Fin 3, ((fD k+fV k)+fK k)) =
        (∑ k : Fin 3, (fD k+fV k))+(∑ k : Fin 3, fK k) :=
      Finset.sum_add_distrib
    trace "COVARIANT_LEADING_CONNECTION_SUM_OUTER_READY"
    have hInner : (∑ k : Fin 3, (fD k+fV k)) =
        (∑ k : Fin 3, fD k)+(∑ k : Fin 3, fV k) :=
      Finset.sum_add_distrib
    trace "COVARIANT_LEADING_CONNECTION_SUM_INNER_READY"
    have hInnerAdded := congrArg
      (fun z : SphereSobolev (-(1/2 : ℝ)) => z+(∑ k : Fin 3, fK k)) hInner
    exact hSum.trans (hOuter.trans hInnerAdded)
  trace "COVARIANT_LEADING_CONNECTION_DISTRIBUTION_READY"
  have hDouble : (R y)⁻¹ • Alo i (V j y) =
      ((R y)⁻¹)^2 • Alo i (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j (u y)) := by
    have hMap := (Alo i).map_smul (R y)⁻¹
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j (u y))
    have hScaled := congrArg
      (fun z : SphereSobolev (-(1/2 : ℝ)) => (R y)⁻¹ • z) hMap
    have hScalar (c : ℝ) (z : SphereSobolev (-(1/2 : ℝ))) :
        c • (c • z) = c^2 • z :=
      (smul_smul c c z).trans
        (congrArg (fun a : ℝ => a • z) (pow_two c).symm)
    exact hScaled.trans (hScalar (R y)⁻¹
      (Alo i (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j (u y))))
  trace "COVARIANT_LEADING_DOUBLE_RAISING_READY"
  trace "COVARIANT_LEADING_MAP_EXPANSIONS_READY"
  have hExpanded := congrArg₂
    (fun x z : SphereSobolev (-(1/2 : ℝ)) => x-z)
    (congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z)
      (congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z)
        hDistribution hAngular) hCorrection) hConnection
  trace "COVARIANT_LEADING_FINAL_EXPANDED_EQUALITY_READY"
  have hReplaced := congrArg₂
    (fun v a : SphereSobolev (-(1/2 : ℝ)) =>
      (referenceLowerWeightedHorizontalAction g L q R (D j) y i + v +
        referenceLowerWeightedHorizontalAction g L q R (K j) y i) +
      ((R y)⁻¹ • Alo i (D j y) + a + (R y)⁻¹ • Alo i (K j y)) +
      (Klo (D j y) + Klo (V j y) + Klo (K j y)) -
      ((∑ k : Fin 3, Gamma k • Iout (D k y)) +
       (∑ k : Fin 3, Gamma k • Iout (V k y)) +
       (∑ k : Fin 3, Gamma k • Iout (K k y)))) hCovariantAdd hDouble
  trace "COVARIANT_LEADING_FINAL_REPLACED_EQUALITY_READY"
  have hArrange (a b c d e f g h i j k l : SphereSobolev (-(1/2 : ℝ))) :
      ((a+(b+j))+c)+((d+e)+f)+((g+h)+i)-((k+j)+l) =
      (a-k)+b+d+e+c+f+g+h+i-l := by abel
  trace "COVARIANT_LEADING_FINAL_ABSTRACT_ARRANGEMENT_READY"
  exact hNormalGrouped.trans (hExpanded.trans (hReplaced.trans
    (hArrange
      (referenceLowerWeightedHorizontalAction g L q R (D j) y i)
      ((R y)⁻¹ • Alo j (D i y))
      (referenceLowerWeightedHorizontalAction g L q R (K j) y i)
      ((R y)⁻¹ • Alo i (D j y))
      (((R y)⁻¹)^2 • Alo i
        (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j (u y)))
      ((R y)⁻¹ • Alo i (K j y))
      (Klo (D j y)) (Klo (V j y)) (Klo (K j y))
      (∑ k : Fin 3, Gamma k • Iout (V k y))
      (∑ k : Fin 3, Gamma k • Iout (D k y))
      (∑ k : Fin 3, Gamma k • Iout (K k y)))))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityCovariantSecondAction_leading_part
