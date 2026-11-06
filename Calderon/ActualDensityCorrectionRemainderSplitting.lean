import Calderon.ActualDensityFirstNormalFormSummandSmoothness
import Calderon.ActualWeightedHorizontalRadiusProduct
import Calderon.ActualNativeMovingLocalRemainderCompatibility

/-! Full before-source: actual-covariant-leading-algebra-author-oct16-v001/
EXPANSION-actual-correction-remainder-FE-v014.md.
Literal actual F/E products, native endpoints and signed radii. -/
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

attribute [local irreducible] referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceNativeMovingAdjointParametricCorrection referenceMetricGramFrame
  referenceFrameConnectionCoefficient referenceRadiusHorizontalLogDerivative
  sphereSobolevInclusionL sphereSobolevAngularCoordinateTransposeL
  referenceRadialEndpointInvertibleLocus normalizedSecondDriftFrameJoint

lemma referenceLowerWeightedHorizontalAction_correction_remainder_split
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i j : Fin 3)
    (hr : R y ≠ 0) (hu : ContDiffAt ℝ ∞ u y)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Fh := fun (k : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) k
    let Eh := fun (k : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k
    let F : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Iin (Fh k x (u x))
    let E : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Eh k x (u x)
    let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => F k x+R x • E k x
    referenceLowerWeightedHorizontalAction g L q R (K j) y i =
      referenceLowerWeightedHorizontalAction g L q R (F j) y i +
      R y • referenceLowerWeightedHorizontalAction g L q R (E j) y i +
      (R y * referenceRadiusHorizontalLogDerivative g L q R y i) • Iout (E j y) := by
  dsimp only
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Fh := fun (k : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) k
  let Eh := fun (k : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k
  let F : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Iin (Fh k x (u x))
  let E : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Eh k x (u x)
  let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => F k x+R x • E k x
  have hTerms := contDiffAt_referenceHighDensityFirstAction_normal_form_summands
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R u y j
      hR.contDiffAt hr hu hInv hp
  have hF0 : DifferentiableAt ℝ (F j) y := hTerms.2.2.1.differentiableAt (by simp)
  have hQuotient := contDiffAt_referenceHighAdjointMovingDifferenceQuotient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R y j
      hR.contDiffAt hr hInv hp
  have hE0 : ContDiffAt ℝ ∞ (E j) y := hQuotient.clm_apply hu
  have hRemainder : DifferentiableAt ℝ (fun x => R x • E j x) y :=
    (hR.contDiffAt.smul hE0).differentiableAt (by simp)
  have hAdd := referenceLowerWeightedHorizontalAction_add g L q R (F j)
    (fun x => R x • E j x) y i hF0 hRemainder
  have hRadius := referenceLowerWeightedHorizontalAction_radius_smul
    g L q R hR (E j) y i hr (hE0.differentiableAt (by simp))
  have hSlot := congrArg
    (fun z : SphereSobolev (-(1/2 : ℝ)) => referenceLowerWeightedHorizontalAction g L q R (F j) y i+z)
    hRadius
  have hAssoc (a0 b0 c0 : SphereSobolev (-(1/2 : ℝ))) : a0+(b0+c0)=a0+b0+c0 :=
    (add_assoc a0 b0 c0).symm
  exact (hAdd.trans hSlot).trans (hAssoc
    (referenceLowerWeightedHorizontalAction g L q R (F j) y i)
    (R y • referenceLowerWeightedHorizontalAction g L q R (E j) y i)
    ((R y * referenceRadiusHorizontalLogDerivative g L q R y i) • Iout (E j y)))

lemma referenceMovingCorrectionRemainder_products_split
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ))
    (y : R3) (i j : Fin 3) (hr : R y ≠ 0) :
    let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Fh := fun (k : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) k
    let Fl := fun k : Fin 3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) k
    let Eh := fun (k : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k
    let El := fun k : Fin 3 => referenceLowerAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y k
    let F : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Iin (Fh k x (u x))
    let E : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Eh k x (u x)
    let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => F k x+R x • E k x
    let MF := fun k : Fin 3 => Iout.comp (Fl k)
    let ME := El
    let Klo := fun k : Fin 3 => MF k+R y • ME k
    let D := fun (k : Fin 3) (x : R3) => referenceHighWeightedHorizontalAction g L q R u x k
    let Ahi := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k
    let Alo := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) k
    let V := fun (k : Fin 3) (x : R3) => (R x)⁻¹ • Ahi k (u x)
    ((R y)⁻¹ • Alo i (K j y) = (R y)⁻¹ • Alo i (F j y)+Alo i (E j y)) ∧
    ((Klo i) (D j y) = MF i (D j y)+R y • ME i (D j y)) ∧
    ((Klo i) (V j y) = (R y)⁻¹ • MF i (Ahi j (u y))+ME i (Ahi j (u y))) ∧
    ((Klo i) (K j y) = MF i (F j y)+R y • MF i (E j y)+
      R y • ME i (F j y)+(R y)^2 • ME i (E j y)) := by
  dsimp only
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Fh := fun (k : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) k
  let Fl := fun k : Fin 3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) k
  let Eh := fun (k : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k
  let El := fun k : Fin 3 => referenceLowerAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y k
  let F : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Iin (Fh k x (u x))
  let E : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Eh k x (u x)
  let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => F k x+R x • E k x
  let MF := fun k : Fin 3 => Iout.comp (Fl k)
  let ME := El
  let Klo := fun k : Fin 3 => MF k+R y • ME k
  let D := fun (k : Fin 3) (x : R3) => referenceHighWeightedHorizontalAction g L q R u x k
  let Ahi := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k
  let Alo := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) k
  let V := fun (k : Fin 3) (x : R3) => (R x)⁻¹ • Ahi k (u x)
  let r := R y
  have hLeftCancel {Z : Type} [AddCommGroup Z] [Module ℝ Z]
      (s : ℝ) (hs : s ≠ 0) (x z : Z) : s⁻¹ • (x+s • z)=s⁻¹ • x+z := by
    simp only [smul_add,smul_smul,inv_mul_cancel₀ hs,one_smul]
  have hRightCancel {Z : Type} [AddCommGroup Z] [Module ℝ Z]
      (s : ℝ) (hs : s ≠ 0) (x z : Z) : s⁻¹ • x+s • (s⁻¹ • z)=s⁻¹ • x+z := by
    simp only [smul_smul,mul_inv_cancel₀ hs,one_smul]
  have hFour {Z : Type} [AddCommGroup Z] [Module ℝ Z]
      (s : ℝ) (a0 b0 c0 d0 : Z) :
      (a0+s • b0)+s • (c0+s • d0)=a0+s • b0+s • c0+s^2 • d0 := by
    simp only [smul_add,smul_smul,pow_two]
    abel
  have hEval (v : SphereSobolev (1/2 : ℝ)) : (Klo i) v = MF i v+r • ME i v := rfl
  have hMap (T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :
      T (K j y)=T (F j y)+r • T (E j y) :=
    (T.map_add (F j y) (r • E j y)).trans
      (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => T (F j y)+z)
        (T.map_smul r (E j y)))
  have hAngular := (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => r⁻¹ • z)
    (hMap (Alo i))).trans (hLeftCancel r hr (Alo i (F j y)) (Alo i (E j y)))
  have hD := hEval (D j y)
  have hVmaps := congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+r • z)
    ((MF i).map_smul r⁻¹ (Ahi j (u y))) ((ME i).map_smul r⁻¹ (Ahi j (u y)))
  have hV := ((hEval (V j y)).trans hVmaps).trans
    (hRightCancel r hr (MF i (Ahi j (u y))) (ME i (Ahi j (u y))))
  have hKmaps := congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+r • z)
    (hMap (MF i)) (hMap (ME i))
  have hK := ((hEval (K j y)).trans hKmaps).trans
    (hFour r (MF i (F j y)) (MF i (E j y)) (ME i (F j y)) (ME i (E j y)))
  exact ⟨hAngular,hD,hV,hK⟩

lemma referenceMovingCorrectionRemainder_covector_sum_split
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ))
    (y : R3) (i j : Fin 3) :
    let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Fh := fun (k : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) k
    let Eh := fun (k : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k
    let F : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Iin (Fh k x (u x))
    let E : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Eh k x (u x)
    let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => F k x+R x • E k x
    let Gamma := fun k : Fin 3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j
    (∑ k : Fin 3, Gamma k • Iout (K k y)) =
      (∑ k : Fin 3, Gamma k • Iout (F k y)) +
      R y • (∑ k : Fin 3, Gamma k • Iout (E k y)) := by
  dsimp only
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Fh := fun (k : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) k
  let Eh := fun (k : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k
  let F : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Iin (Fh k x (u x))
  let E : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Eh k x (u x)
  let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => F k x+R x • E k x
  let Gamma := fun k : Fin 3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j
  let r := R y
  have hScalar {Z : Type} [AddCommGroup Z] [Module ℝ Z]
      (s t : ℝ) (x z : Z) : s • (x+t • z)=s • x+t • (s • z) :=
    (smul_add s x (t • z)).trans
      (congrArg (fun v : Z => s • x+v) (smul_comm s t z))
  have hPoint (k : Fin 3) : Gamma k • Iout (K k y) =
      Gamma k • Iout (F k y)+r • (Gamma k • Iout (E k y)) := by
    have hMap := (Iout.map_add (F k y) (r • E k y)).trans
      (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => Iout (F k y)+z)
        (Iout.map_smul r (E k y)))
    exact (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => Gamma k • z) hMap).trans
      (hScalar (Gamma k) r (Iout (F k y)) (Iout (E k y)))
  have hSum : (∑ k : Fin 3, Gamma k • Iout (K k y)) =
      ∑ k : Fin 3, (Gamma k • Iout (F k y)+r • (Gamma k • Iout (E k y))) :=
    Finset.sum_congr rfl (fun k _ => hPoint k)
  have hAdd : (∑ k : Fin 3, (Gamma k • Iout (F k y)+r • (Gamma k • Iout (E k y)))) =
      (∑ k : Fin 3, Gamma k • Iout (F k y))+
      (∑ k : Fin 3, r • (Gamma k • Iout (E k y))) := Finset.sum_add_distrib
  have hScale : r • (∑ k : Fin 3, Gamma k • Iout (E k y)) =
      ∑ k : Fin 3, r • (Gamma k • Iout (E k y)) := Finset.smul_sum
  have hUnscaled := (hSum.trans hAdd).trans
    (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      (∑ k : Fin 3, Gamma k • Iout (F k y))+z) hScale.symm)
  exact hUnscaled

lemma referenceMovingCorrectionRemainder_drift_sum_split
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) :
    let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Fh := fun (k : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) k
    let Eh := fun (k : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k
    let F : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Iin (Fh k x (u x))
    let E : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Eh k x (u x)
    let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => F k x+R x • E k x
    let b := fun k : Fin 3 => normalizedSecondDriftFrameJoint g g2 L k (q,y)
    R y • (∑ k : Fin 3, b k • Iout (K k y)) =
      R y • (∑ k : Fin 3, b k • Iout (F k y)) +
      (R y)^2 • (∑ k : Fin 3, b k • Iout (E k y)) := by
  dsimp only
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Fh := fun (k : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) k
  let Eh := fun (k : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k
  let F : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Iin (Fh k x (u x))
  let E : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Eh k x (u x)
  let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => F k x+R x • E k x
  let b := fun k : Fin 3 => normalizedSecondDriftFrameJoint g g2 L k (q,y)
  let r := R y
  have hScalar {Z : Type} [AddCommGroup Z] [Module ℝ Z]
      (s t : ℝ) (x z : Z) : s • (x+t • z)=s • x+t • (s • z) :=
    (smul_add s x (t • z)).trans
      (congrArg (fun v : Z => s • x+v) (smul_comm s t z))
  have hPoint (k : Fin 3) : b k • Iout (K k y) =
      b k • Iout (F k y)+r • (b k • Iout (E k y)) := by
    have hMap := (Iout.map_add (F k y) (r • E k y)).trans
      (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => Iout (F k y)+z)
        (Iout.map_smul r (E k y)))
    exact (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => b k • z) hMap).trans
      (hScalar (b k) r (Iout (F k y)) (Iout (E k y)))
  have hSum : (∑ k : Fin 3, b k • Iout (K k y)) =
      ∑ k : Fin 3, (b k • Iout (F k y)+r • (b k • Iout (E k y))) :=
    Finset.sum_congr rfl (fun k _ => hPoint k)
  have hAdd : (∑ k : Fin 3, (b k • Iout (F k y)+r • (b k • Iout (E k y)))) =
      (∑ k : Fin 3, b k • Iout (F k y))+
      (∑ k : Fin 3, r • (b k • Iout (E k y))) := Finset.sum_add_distrib
  have hScale : r • (∑ k : Fin 3, b k • Iout (E k y)) =
      ∑ k : Fin 3, r • (b k • Iout (E k y)) := Finset.smul_sum
  have hUnscaled := (hSum.trans hAdd).trans
    (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      (∑ k : Fin 3, b k • Iout (F k y))+z) hScale.symm)
  have hSquare {Z : Type} [AddCommGroup Z] [Module ℝ Z]
      (s : ℝ) (x z : Z) : s • (x+s • z)=s • x+s^2 • z := by
    simp only [smul_add,smul_smul,pow_two]
  exact (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => r • z) hUnscaled).trans
    (hSquare r (∑ k : Fin 3, b k • Iout (F k y)) (∑ k : Fin 3, b k • Iout (E k y)))

lemma referenceDensityCovariantCorrectionRemainder_split
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i j : Fin 3)
    (hr : R y ≠ 0) (hu : ContDiffAt ℝ ∞ u y)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Fh := fun (k : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) k
    let Fl := fun k : Fin 3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) k
    let Eh := fun (k : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k
    let El := fun k : Fin 3 => referenceLowerAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y k
    let F : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Iin (Fh k x (u x))
    let E : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Eh k x (u x)
    let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => F k x+R x • E k x
    let MF := fun k : Fin 3 => Iout.comp (Fl k)
    let ME := El
    let Klo := fun k : Fin 3 => MF k+R y • ME k
    let D := fun (k : Fin 3) (x : R3) => referenceHighWeightedHorizontalAction g L q R u x k
    let Ahi := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k
    let Alo := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) k
    let V := fun (k : Fin 3) (x : R3) => (R x)⁻¹ • Ahi k (u x)
    let Gamma := fun k : Fin 3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j
    let f := referenceRadiusHorizontalLogDerivative g L q R y i
    R y • (referenceLowerWeightedHorizontalAction g L q R (K j) y i +
      (R y)⁻¹ • Alo i (K j y)+(Klo i) (D j y)+(Klo i) (V j y)+(Klo i) (K j y)-
      ∑ k : Fin 3, Gamma k • Iout (K k y)) =
    (Alo i (F j y)+MF i (Ahi j (u y))) +
    R y • (referenceLowerWeightedHorizontalAction g L q R (F j) y i + MF i (D j y) -
      (∑ k : Fin 3, Gamma k • Iout (F k y))+MF i (F j y)) +
    (R y)^2 • (referenceLowerWeightedHorizontalAction g L q R (E j) y i + ME i (D j y) +
      f • Iout (E j y)-(∑ k : Fin 3, Gamma k • Iout (E k y))) +
    R y • (Alo i (E j y)+ME i (Ahi j (u y))) +
    (R y)^2 • (MF i (E j y)+ME i (F j y)) +
    (R y)^3 • ME i (E j y) := by
  dsimp only
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Fh := fun (k : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) k
  let Fl := fun k : Fin 3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) k
  let Eh := fun (k : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x k
  let El := fun k : Fin 3 => referenceLowerAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y k
  let F : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Iin (Fh k x (u x))
  let E : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => Eh k x (u x)
  let K : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun k x => F k x+R x • E k x
  let MF := fun k : Fin 3 => Iout.comp (Fl k)
  let ME := El
  let Klo := fun k : Fin 3 => MF k+R y • ME k
  let D := fun (k : Fin 3) (x : R3) => referenceHighWeightedHorizontalAction g L q R u x k
  let Ahi := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k
  let Alo := fun k : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) k
  let V := fun (k : Fin 3) (x : R3) => (R x)⁻¹ • Ahi k (u x)
  let Gamma := fun k : Fin 3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j
  let f := referenceRadiusHorizontalLogDerivative g L q R y i
  let r := R y
  have hAlgebra {Z : Type} [AddCommGroup Z] [Module ℝ Z]
      (s t : ℝ) (hs : s ≠ 0)
      (df de ie af ae fd ed fa ea ff fe ef ee gf ge : Z) :
      s • ((df+s • de+(s*t) • ie)+(s⁻¹ • af+ae)+(fd+s • ed)+
        (s⁻¹ • fa+ea)+(ff+s • fe+s • ef+s^2 • ee)-(gf+s • ge)) =
      (af+fa)+s • (df+fd-gf+ff)+s^2 • (de+ed+t • ie-ge)+
      s • (ae+ea)+s^2 • (fe+ef)+s^3 • ee := by
    have hInv : s*s⁻¹=1 := mul_inv_cancel₀ hs
    simp only [smul_add,smul_sub,smul_smul,hInv,one_smul]
    module
  have hDerivative := referenceLowerWeightedHorizontalAction_correction_remainder_split
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R hR u y i j hr hu hInv hp
  have hProducts := referenceMovingCorrectionRemainder_products_split
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j hr
  have hConnection := referenceMovingCorrectionRemainder_covector_sum_split
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j
  have hFirstPair := congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z)
    hDerivative hProducts.1
  have hWithD := congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z)
    hFirstPair hProducts.2.1
  have hWithV := congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z)
    hWithD hProducts.2.2.1
  have hWithK := congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z)
    hWithV hProducts.2.2.2
  have hWithConnection := congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x-z)
    hWithK hConnection
  have hScaled := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => r • z) hWithConnection
  exact hScaled.trans (hAlgebra r f hr
    (referenceLowerWeightedHorizontalAction g L q R (F j) y i)
    (referenceLowerWeightedHorizontalAction g L q R (E j) y i) (Iout (E j y))
    (Alo i (F j y)) (Alo i (E j y)) (MF i (D j y)) (ME i (D j y))
    (MF i (Ahi j (u y))) (ME i (Ahi j (u y)))
    (MF i (F j y)) (MF i (E j y)) (ME i (F j y)) (ME i (E j y))
    (∑ k : Fin 3, Gamma k • Iout (F k y)) (∑ k : Fin 3, Gamma k • Iout (E k y)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerWeightedHorizontalAction_correction_remainder_split
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceMovingCorrectionRemainder_products_split
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceMovingCorrectionRemainder_covector_sum_split
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceMovingCorrectionRemainder_drift_sum_split
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityCovariantCorrectionRemainder_split
