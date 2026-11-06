import Calderon.ActualDensityCovariantLeadingPart
import Calderon.ActualDensityRadiusPrincipalContraction
import Calderon.ActualPhysicalDensityOperator

/-! Before-source: actual-physical-full-allocation-author-oct16-v001/
EXPANSION-physical-leading-contraction-v016.md and
actual-covariant-leading-algebra-author-oct16-v001/EXPANSION-physical-leading-correspondence-v009.md.
Literal physical P, retaining every K remainder and original drift endpoint. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referencePhysicalDensityOperator referenceDensityCovariantSecondAction
  referenceHighDensityFirstAction referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceNativeMovingAdjointParametricCorrection referenceMetricGramFrame
  referenceFrameConnectionCoefficient referenceDensityPrincipalFrameCoefficient
  sphereSobolevInclusionL sphereSobolevAngularCoordinateTransposeL
  referenceRadialEndpointInvertibleLocus normalizedSecondDriftFrameJoint

lemma add_add_add_add_add_assoc {E : Type*} [AddCommGroup E]
    (l c0 m0 d0 a0 k0 : E) :
    (l+c0+m0)+(d0+a0+k0) = l+c0+m0+d0+a0+k0 := by abel

lemma referencePhysicalDensityOperator_eq_principal_add_drift
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) :
    referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y =
    R y • (∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
        referenceDensityCovariantSecondAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j) +
    R y • (∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) •
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighDensityFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i)) := by
  unfold referencePhysicalDensityOperator
  exact smul_add (R y)
    (∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
        referenceDensityCovariantSecondAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j)
    (∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) •
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighDensityFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i))

lemma referencePhysicalDensityOperator_principal_part_leading_decomposition
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (hr : R y ≠ 0) (hu : ContDiffAt ℝ ∞ u y)
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
    let Klo : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun i =>
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
          ((q,y),fderiv ℝ R y) i) +
      R y • referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
    let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Ahi := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
    let Alo := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
    let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
    let sigma := fun i j : Fin 3 => Q i j - if i=j then (1 : ℝ) else 0
    let b := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
    let Gamma := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j
    let CovD := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (D j) y i -
      ∑ k : Fin 3, Gamma i j k • Iout (D k y)
    let Rem := fun i j : Fin 3 =>
      referenceLowerWeightedHorizontalAction g L q R (K j) y i + (R y)⁻¹ • Alo i (K j y) +
      Klo i (D j y) + Klo i (V j y) + Klo i (K j y) -
      ∑ k : Fin 3, Gamma i j k • Iout (K k y)
    let XX := fun i j : Fin 3 => referenceDensityCovariantSecondAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j
    R y • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • XX i j) =
    (2 : ℝ) • (∑ i : Fin 3, Alo i (D i y)) +
    (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (D j y)) +
    (R y)⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (Ahi j (u y))) +
    R y • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j) +
    R y • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Rem i j) := by
  dsimp only
  let D : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => referenceHighWeightedHorizontalAction g L q R u x k
  let V : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => (R x)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k (u x)
  let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x =>
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) k (u x)) +
      R x • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k (u x)
  let Klo : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun i =>
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
          ((q,y),fderiv ℝ R y) i) +
      R y • referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Ahi := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
  let Alo := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
  let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let sigma := fun i j : Fin 3 => Q i j - if i=j then (1 : ℝ) else 0
  let b := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
  let Gamma := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j
  let CovD := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (D j) y i -
      ∑ k : Fin 3, Gamma i j k • Iout (D k y)
  let Rem := fun i j : Fin 3 =>
      referenceLowerWeightedHorizontalAction g L q R (K j) y i + (R y)⁻¹ • Alo i (K j y) +
      Klo i (D j y) + Klo i (V j y) + Klo i (K j y) -
      ∑ k : Fin 3, Gamma i j k • Iout (K k y)
  let r := R y
  let Princ := fun i j : Fin 3 => r⁻¹ • (Alo i (D j y)+Alo j (D i y)) +
    (r⁻¹)^2 • Alo i (Ahi j (u y))
  let X := fun i : Fin 3 => referenceHighDensityFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i
  let XX := fun i j : Fin 3 => referenceDensityCovariantSecondAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j
  let LC : SphereSobolev (-(1/2 : ℝ)) :=
    (2 : ℝ) • (∑ i : Fin 3, Alo i (D i y)) +
    (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (D j y)) +
    r⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (Ahi j (u y)))
  have hScaleThree (s : ℝ) (a0 b0 c0 : SphereSobolev (-(1/2 : ℝ))) :
      s • (a0+b0+c0) = s • a0+s • b0+s • c0 := by
    rw [smul_add,smul_add]
  have hSumTwoThree (f0 f1 f2 : Fin 3 → Fin 3 → SphereSobolev (-(1/2 : ℝ))) :
      (∑ i : Fin 3, ∑ j : Fin 3, (f0 i j+f1 i j+f2 i j)) =
      (∑ i : Fin 3, ∑ j : Fin 3, f0 i j)+
      (∑ i : Fin 3, ∑ j : Fin 3, f1 i j)+
      (∑ i : Fin 3, ∑ j : Fin 3, f2 i j) := by
    simp only [Finset.sum_add_distrib]
  have hOrder (a0 b0 c0 : SphereSobolev (-(1/2 : ℝ))) : a0+b0+c0=b0+a0+c0 := by abel
  have hRegroup (s : ℝ) (c0 x0 z0 a0 m0 n0 o0 p0 t0 gamma0 : SphereSobolev (-(1/2 : ℝ))) :
      c0+s⁻¹ • z0+s⁻¹ • x0+a0+m0+n0+o0+p0+t0-gamma0 =
      c0+(s⁻¹ • (x0+z0)+a0)+(m0+n0+o0+p0+t0-gamma0) := by
    have hAdd (b0 d0 : SphereSobolev (-(1/2 : ℝ))) :
        c0+d0+b0+a0+m0+n0+o0+p0+t0-gamma0 =
        c0+((b0+d0)+a0)+(m0+n0+o0+p0+t0-gamma0) := by abel
    have hSlot := congrArg
      (fun v : SphereSobolev (-(1/2 : ℝ)) =>
        c0+(v+a0)+(m0+n0+o0+p0+t0-gamma0))
      (smul_add s⁻¹ x0 z0).symm
    exact (hAdd (s⁻¹ • x0) (s⁻¹ • z0)).trans hSlot
  trace "PHYSICAL_LEADING_ABSTRACT_ALGEBRA_READY"
  have hPoint (i j : Fin 3) : XX i j = CovD i j+Princ i j+Rem i j := by
    have hRaw := referenceDensityCovariantSecondAction_leading_part
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR u y hy i j hr hu hInv hp
    exact hRaw.trans (hRegroup r (CovD i j) (Alo i (D j y)) (Alo j (D i y))
      ((r⁻¹)^2 • Alo i (Ahi j (u y)))
      (referenceLowerWeightedHorizontalAction g L q R (K j) y i)
      (r⁻¹ • Alo i (K j y)) (Klo i (D j y)) (Klo i (V j y)) (Klo i (K j y))
      (∑ k : Fin 3, Gamma i j k • Iout (K k y)))
  have hWeightedPoint (i j : Fin 3) : Q i j • XX i j =
      Q i j • CovD i j+Q i j • Princ i j+Q i j • Rem i j :=
    (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => Q i j • z) (hPoint i j)).trans
      (hScaleThree (Q i j) (CovD i j) (Princ i j) (Rem i j))
  have hWeightedRaw : (∑ i : Fin 3, ∑ j : Fin 3, Q i j • XX i j) =
      ∑ i : Fin 3, ∑ j : Fin 3, (Q i j • CovD i j+Q i j • Princ i j+Q i j • Rem i j) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hWeightedPoint i j))
  have hWeighted := hWeightedRaw.trans (hSumTwoThree
    (fun i j => Q i j • CovD i j) (fun i j => Q i j • Princ i j) (fun i j => Q i j • Rem i j))
  have hPrincipalScaled := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => r • z) hWeighted
  have hPrincipalSplit := hPrincipalScaled.trans (hScaleThree r
    (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j)
    (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Princ i j)
    (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Rem i j))
  trace "PHYSICAL_LEADING_SECOND_SUM_READY"
  have hRadius := sum_referenceDensityPrincipalFrameCoefficient_radius_angular_part
    g g2 hg2 L q y hF hO hD r hr (fun i => D i y) (u y)
  have hPrincipalSlot := congrArg
    (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j)+z+
      r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Rem i j)) hRadius
  have hPrincipal : r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • XX i j) =
      LC+r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j)+
      r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Rem i j) :=
    (hPrincipalSplit.trans hPrincipalSlot).trans (hOrder
      (r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j)) LC
      (r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Rem i j)))
  trace "PHYSICAL_LEADING_RADIUS_CONTRACTION_READY"
  exact hPrincipal

lemma referencePhysicalDensityOperator_drift_part_leading_decomposition
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (hr : R y ≠ 0) :
    let D : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => referenceHighWeightedHorizontalAction g L q R u x k
    let V : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => (R x)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k (u x)
    let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x =>
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) k (u x)) +
      R x • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k (u x)
    let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Ahi := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
    let b := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
    let X := fun i : Fin 3 => referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i
    R y • (∑ i : Fin 3, b i • Iout (X i)) =
    R y • (∑ i : Fin 3, b i • Iout (D i y)) +
    (∑ i : Fin 3, b i • Iout (Ahi i (u y))) +
    R y • (∑ i : Fin 3, b i • Iout (K i y)) := by
  dsimp only
  let D : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => referenceHighWeightedHorizontalAction g L q R u x k
  let V : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => (R x)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k (u x)
  let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x =>
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) k (u x)) +
      R x • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k (u x)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Ahi := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
  let b := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
  let X := fun i : Fin 3 => referenceHighDensityFirstAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i
  let r := R y
  have hScaleThree (s : ℝ) (a0 b0 c0 : SphereSobolev (-(1/2 : ℝ))) :
      s • (a0+b0+c0) = s • a0+s • b0+s • c0 := by
    rw [smul_add,smul_add]
  have hSumThree (f0 f1 f2 : Fin 3 → SphereSobolev (-(1/2 : ℝ))) :
      (∑ i : Fin 3, (f0 i+f1 i+f2 i)) =
      (∑ i : Fin 3, f0 i)+(∑ i : Fin 3, f1 i)+(∑ i : Fin 3, f2 i) := by
    simp only [Finset.sum_add_distrib]
  have hSignedScalar (s t : ℝ) (hs : s ≠ 0) (z : SphereSobolev (-(1/2 : ℝ))) :
      s • (t • (s⁻¹ • z)) = t • z := by
    have hMul : s*(t*s⁻¹)=t := by
      calc
        s*(t*s⁻¹)=t*(s*s⁻¹) := by ring
        _ = t := by rw [mul_inv_cancel₀ hs,mul_one]
    simp only [smul_smul,hMul]
  have hFirst (i : Fin 3) : X i = D i y+V i y+K i y := by
    have hRaw := referenceHighDensityFirstAction_normal_form
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i hr
    exact hRaw.trans (add_assoc (D i y+V i y)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,y),fderiv ℝ R y) i (u y)))
      (r • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i (u y)))
  have hDriftPoint (i : Fin 3) : r • (b i • Iout (X i)) =
      r • (b i • Iout (D i y))+b i • Iout (Ahi i (u y))+r • (b i • Iout (K i y)) := by
    have hStart := congrArg
      (fun z : SphereSobolev (1/2 : ℝ) => r • (b i • Iout z)) (hFirst i)
    have hMap := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => r • z)
      (smul_map_add_add Iout (b i) (D i y) (V i y) (K i y))
    have hSplit := hScaleThree r (b i • Iout (D i y)) (b i • Iout (V i y)) (b i • Iout (K i y))
    have hInclusion := congrArg
      (fun z : SphereSobolev (-(1/2 : ℝ)) => r • (b i • z))
      (Iout.map_smul r⁻¹ (Ahi i (u y)))
    have hV := hInclusion.trans (hSignedScalar r (b i) hr (Iout (Ahi i (u y))))
    have hReplace := congrArg
      (fun z : SphereSobolev (-(1/2 : ℝ)) =>
        r • (b i • Iout (D i y))+z+r • (b i • Iout (K i y))) hV
    exact ((hStart.trans hMap).trans hSplit).trans hReplace
  have hDriftScale : r • (∑ i : Fin 3, b i • Iout (X i)) =
      ∑ i : Fin 3, r • (b i • Iout (X i)) := Finset.smul_sum
  have hDriftSum : (∑ i : Fin 3, r • (b i • Iout (X i))) =
      ∑ i : Fin 3, (r • (b i • Iout (D i y))+b i • Iout (Ahi i (u y))+r • (b i • Iout (K i y))) :=
    Finset.sum_congr rfl (fun i _ => hDriftPoint i)
  have hDriftSplit := ((hDriftScale.trans hDriftSum).trans (hSumThree
    (fun i => r • (b i • Iout (D i y))) (fun i => b i • Iout (Ahi i (u y)))
    (fun i => r • (b i • Iout (K i y)))))
  have hDScale : r • (∑ i : Fin 3, b i • Iout (D i y)) =
      ∑ i : Fin 3, r • (b i • Iout (D i y)) := Finset.smul_sum
  have hKScale : r • (∑ i : Fin 3, b i • Iout (K i y)) =
      ∑ i : Fin 3, r • (b i • Iout (K i y)) := Finset.smul_sum
  have hDrift : r • (∑ i : Fin 3, b i • Iout (X i)) =
      r • (∑ i : Fin 3, b i • Iout (D i y))+
      (∑ i : Fin 3, b i • Iout (Ahi i (u y)))+
      r • (∑ i : Fin 3, b i • Iout (K i y)) :=
    hDriftSplit.trans (congrArg₂
      (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+(∑ i : Fin 3, b i • Iout (Ahi i (u y)))+z)
      hDScale.symm hKScale.symm)
  trace "PHYSICAL_LEADING_DRIFT_READY"
  exact hDrift

lemma referencePhysicalDensityOperator_leading_decomposition
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (hr : R y ≠ 0) (hu : ContDiffAt ℝ ∞ u y)
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
    let Klo : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun i =>
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
          ((q,y),fderiv ℝ R y) i) +
      R y • referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
    let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Ahi := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
    let Alo := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
    let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
    let sigma := fun i j : Fin 3 => Q i j - if i=j then (1 : ℝ) else 0
    let b := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
    let Gamma := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j
    let CovD := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (D j) y i -
      ∑ k : Fin 3, Gamma i j k • Iout (D k y)
    let Rem := fun i j : Fin 3 =>
      referenceLowerWeightedHorizontalAction g L q R (K j) y i + (R y)⁻¹ • Alo i (K j y) +
      Klo i (D j y) + Klo i (V j y) + Klo i (K j y) -
      ∑ k : Fin 3, Gamma i j k • Iout (K k y)
    referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y =
    (2 : ℝ) • (∑ i : Fin 3, Alo i (D i y)) +
    (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (D j y)) +
    (R y)⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (Ahi j (u y))) +
    R y • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j) +
    R y • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Rem i j) +
    R y • (∑ i : Fin 3, b i • Iout (D i y)) +
    (∑ i : Fin 3, b i • Iout (Ahi i (u y))) +
    R y • (∑ i : Fin 3, b i • Iout (K i y)) := by
  dsimp only
  let D : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => referenceHighWeightedHorizontalAction g L q R u x k
  let V : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => (R x)⁻¹ • sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k (u x)
  let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x =>
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ)
          ((q,x),fderiv ℝ R x) k (u x)) +
      R x • referenceHighAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k (u x)
  let Klo : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun i =>
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ)
          ((q,y),fderiv ℝ R y) i) +
      R y • referenceLowerAdjointMovingDifferenceQuotient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Ahi := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
  let Alo := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
  let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let sigma := fun i j : Fin 3 => Q i j - if i=j then (1 : ℝ) else 0
  let b := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
  let Gamma := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j
  let CovD := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (D j) y i -
      ∑ k : Fin 3, Gamma i j k • Iout (D k y)
  let Rem := fun i j : Fin 3 =>
      referenceLowerWeightedHorizontalAction g L q R (K j) y i + (R y)⁻¹ • Alo i (K j y) +
      Klo i (D j y) + Klo i (V j y) + Klo i (K j y) -
      ∑ k : Fin 3, Gamma i j k • Iout (K k y)
  let r := R y
  let Princ := fun i j : Fin 3 => r⁻¹ • (Alo i (D j y)+Alo j (D i y)) +
    (r⁻¹)^2 • Alo i (Ahi j (u y))
  let X := fun i : Fin 3 => referenceHighDensityFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i
  let XX := fun i j : Fin 3 => referenceDensityCovariantSecondAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j
  let LC : SphereSobolev (-(1/2 : ℝ)) :=
    (2 : ℝ) • (∑ i : Fin 3, Alo i (D i y)) +
    (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (D j y)) +
    r⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (Ahi j (u y)))
  have hPrincipal := referencePhysicalDensityOperator_principal_part_leading_decomposition
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 hreg q hq R hR u y hy hr hu hInv hp
  trace "PHYSICAL_LEADING_COMPILED_PRINCIPAL_READY"
  have hDrift := referencePhysicalDensityOperator_drift_part_leading_decomposition
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y hr
  trace "PHYSICAL_LEADING_COMPILED_DRIFT_READY"
  have hTop := referencePhysicalDensityOperator_eq_principal_add_drift
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y
  trace "PHYSICAL_LEADING_TOP_LEVEL_READY"
  have hTogether := hTop.trans (congrArg₂
    (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z) hPrincipal hDrift)
  trace "PHYSICAL_LEADING_TOGETHER_READY"
  trace "PHYSICAL_LEADING_FINAL_ASSEMBLY_ENTER"
  exact hTogether.trans (add_add_add_add_add_assoc LC
    (r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j))
    (r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Rem i j))
    (r • (∑ i : Fin 3, b i • Iout (D i y)))
    (∑ i : Fin 3, b i • Iout (Ahi i (u y)))
    (r • (∑ i : Fin 3, b i • Iout (K i y))))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.add_add_add_add_add_assoc
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensityOperator_eq_principal_add_drift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensityOperator_principal_part_leading_decomposition
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensityOperator_drift_part_leading_decomposition
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensityOperator_leading_decomposition
