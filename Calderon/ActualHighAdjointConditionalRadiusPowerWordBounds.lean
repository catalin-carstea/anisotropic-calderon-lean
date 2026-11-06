import Calderon.ActualHighAdjointRadiusPowerWordDictionary
import Calderon.ActualHighAdjointWeightedCorrectionOpenRoom
import Calderon.ActualHighAdjointStaticThirdWordBounds
import Calderon.OrderedCompositionRadiusPowerWordBounds
import Calderon.ActualReferenceDDHigherLogFrameJets
import Calderon.ActualJacobiCoefficientTubeCover
import Calderon.ActualFinitePairedRadialQuarticDomain
import Calderon.ActualHorizontalSobolevConnection
import Calderon.ActualHighAdjointPrimitiveJetPointWordBounds

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
  ConformalDepth RadiusProfile ReferenceWeightedApproximation
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  ActualReferenceLocalCoordinateWordJets ActualReferenceDDHigherGeometryJets
  ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherLogFrameJets
  ActualReferenceDecomposition PrincipalCommutator ReferenceDensityBounds
  AmbientReferenceRaising NormalCoordinatesFrame SmoothMetricFrame MovingFrameConnection

local instance referenceHighConditionalRadiusPowerWordsHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceHighConditionalRadiusPowerWordsOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
  infer_instance

local instance referenceHighConditionalRadiusPowerWordsIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

local instance referenceHighConditionalRadiusPowerWordsEndIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

attribute [local irreducible] referenceHighAdjointMovingDifferenceQuotient
  referenceAdjointThreeHalfRadialFamily referenceHighAdjointCoordinateBoundaryFamily
  referenceRadialEndpointInvertibleLocus secondTaylorRemainder
  nativeThreeHalfCoefficientMulL referenceJacobiBoundaryThreeHalfCoefficientFamily
  sphereSobolevLinearCoordinateMulL referenceRadiusHorizontalLogDerivative

lemma exists_referenceHighAdjointMovingDifferenceQuotient_conditional_radiusPower_coordinate_word_bounds
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (hg : IsAdmissibleMetric g) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (hKgeom : K ⊆ closedBall y0 ρ) :
    let T2 : (ℝ × (R3 × ℝ)) → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun z =>
      secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    let N2 : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
        SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun i j z =>
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j z)
    ∃ B0 F0 m0 : ℝ, 0 ≤ B0 ∧ 0 < F0 ∧ 1 ≤ m0 ∧
      ∀ dGeom : ℝ, 0 < dGeom → dGeom ≤ ρ → dGeom ≤ 1 →
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dGeom) dGeom) ⊆
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) →
      ∀ Cscaled : ℝ, 0 ≤ Cscaled → ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 < eta → eta ≤ 1 → ∀ A : ℝ, 0 < A →
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ x ∈ K,
        let beta := actualReferenceBeta g L q delta A p x
        referenceRadius delta A p L x ≤ dGeom → 1 ≤ beta →
        (∀ a : ℕ, 1 ≤ a → a ≤ 3 → ∀ order : ℕ, order ≤ 3 →
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (referenceRadius delta A p L y)^a •
              T2 (q,(y,referenceRadius delta A p L y))) x‖ ≤
            Cscaled*eta^a*beta^order/beta^(2*a) ∧
          ∀ i j : Fin 3,
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (referenceRadius delta A p L y)^a •
              N2 i j (q,(y,referenceRadius delta A p L y))) x‖ ≤
            Cscaled*eta^a*beta^order/beta^(2*a)) →
        ∀ power : ℕ, 1 ≤ power → power ≤ 2 →
        ∀ i : Fin 3, ∀ word : List (Fin 3), word.length ≤ 3 →
          ‖coordinateFieldWordPartial word
            (fun y : R3 => (referenceRadius delta A p L y)^power •
              referenceHighAdjointMovingDifferenceQuotient
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q
                  (referenceRadius delta A p L) y i) x‖ ≤
            (Cscaled*m0+24*B0*Cscaled+24*B0*m0*Cscaled+
              24*Cscaled^2*m0+8*F0*Cscaled)*eta^power*beta^word.length/beta^(2*power) := by
  classical
  intro T2 N2
  have hStatic := exists_referenceHighAdjoint_staticEndpoint_third_coordinate_word_bound
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  rcases hStatic with ⟨B0,hB0,hStaticBounds⟩
  have hLog := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds
    g hg L hL K hK 3
  rcases hLog with ⟨F0,hF0,hLogBounds⟩
  let M0 : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun j =>
    sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)
  let m0 : ℝ := 1+∑ j : Fin 3, ‖M0 j‖
  have hm01 : 1 ≤ m0 := by
    dsimp only [m0]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => norm_nonneg (M0 j)))
  have hM0 (j : Fin 3) : ‖M0 j‖ ≤ m0 := by
    have hsum : ‖M0 j‖ ≤ ∑ k : Fin 3, ‖M0 k‖ :=
      Finset.single_le_sum (fun k _ => norm_nonneg (M0 k)) (Finset.mem_univ j)
    dsimp only [m0]
    linarith only [hsum]
  refine ⟨B0,F0,m0,hB0,hF0,hm01,?_⟩
  intro dGeom hdGeom hdGeomρ hdGeom1 hRoom Cscaled hC0 p hp1 eta heta heta1 A hA
  intro q hq delta hdelta hdelta1 x hx beta hRbound hbeta hRaw power hpower1 hpower2 i word hw
  have hpower3 : power ≤ 3 := hpower2.trans (by norm_num)
  have hnext1 : 1 ≤ power+1 := by omega
  have hnext3 : power+1 ≤ 3 := by omega
  let R : R3 → ℝ := referenceRadius delta A p L
  have hRpos (y : R3) : 0 < R y := referenceRadius_pos delta A p L y hdelta hA
  have hLogR : ContDiff ℝ ∞ (fun y => Real.log (R y)) :=
    contDiff_log_referenceRadius_profile delta A L p hdelta hA
  have hR : ContDiff ℝ ∞ R := by
    have hExp : (fun y => Real.exp (Real.log (R y))) = R :=
      funext (fun y => Real.exp_log (hRpos y))
    exact hExp ▸ Real.contDiff_exp.comp hLogR
  let Ω := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let SegΩ : Set (ℝ × (R3 × ℝ)) :=
    {z | ∀ θ ∈ Icc (0 : ℝ) 1, (z.1,(z.2.1,θ*z.2.2)) ∈ Ω}
  let V : Set (ℝ × (R3 × ℝ)) := {z | ∀ ξ : UnitSphere,
    (referenceFramedNormalizedJacobian g L Φ (z.1,(z.2,ξ.val))).IsInvertible}
  let χ : R3 → ℝ × (R3 × ℝ) := fun y => (q,(y,R y))
  let U : Set R3 := {y | R y ≠ 0 ∧ χ y ∈ SegΩ ∧ χ y ∈ V}
  let f : Fin 3 → R3 → ℝ := fun k y => referenceRadiusHorizontalLogDerivative g L q R y k
  have hxBall : x ∈ closedBall y0 ρ := hKgeom hx
  have hxSegment : χ x ∈ SegΩ := by
    intro θ hθ
    have hθr : |θ * R x| ≤ dGeom := by
      rw [abs_mul,abs_of_nonneg hθ.1,abs_of_pos (hRpos x)]
      exact (mul_le_mul_of_nonneg_right hθ.2 (hRpos x).le).trans
        (by simpa only [one_mul] using hRbound)
    exact hRoom ⟨hq,hxBall,abs_le.mp hθr⟩
  have hCover := referenceFramedNormalizedJacobian_isInvertible_on_actual_coefficient_tube
    g L y0 Φ B ε C ρ H a w hData dGeom hdGeom hdGeomρ
  have hxInv : χ x ∈ V := hCover (χ x) ⟨hq,hxBall,
    ⟨(neg_nonpos.mpr hdGeom.le).trans (hRpos x).le,hRbound⟩⟩
  have hxU : x ∈ U := ⟨(hRpos x).ne',hxSegment,hxInv⟩
  have hfEq : f i = referenceFrameDerivative g L q i (fun y => Real.log (R y)) := by
    funext y
    have hFrame : conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i) =
        referenceMetricGramFrame g L (q,y) i :=
      (congrArg (fun A : R3 →L[ℝ] R3 => A (coordinateVector i))
        (conformalReferenceGramFrameOperatorJoint_eq_frameOperator g L (q,y))).trans
        ((frameOperator_coordinateVector _ i).trans
          (conformalReferenceGramFrame_eq_referenceMetricGramFrame g L q y i))
    dsimp only [f]
    unfold referenceRadiusHorizontalLogDerivative referenceFrameDerivative
    exact congrArg (fderiv ℝ (fun y => Real.log (R y)) y) hFrame
  have hfBound : HasCoordinateWordJetBound 3 (f i) x F0 beta 1 := by
    intro v hv
    rw [hfEq]
    have h := (hLogBounds q hq delta hdelta hdelta1 A hA p hp1 x hx hbeta v hv).1 i
    simpa only [Real.norm_eq_abs,R,beta,actualReferenceBeta] using h
  have hPointApply := norm_referenceHighAdjointMovingDifferenceQuotient_radiusPower_coordinate_word_le_of_primitive_jets
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  exact hPointApply x hxBall hxU Cscaled B0 F0 m0 beta eta hC0 hB0 hF0.le hM0
    hbeta heta.le heta1 i hRaw
    (fun j => (hStaticBounds q hq x hxBall beta hbeta j).1)
    (hStaticBounds q hq x hxBall beta hbeta i).2 hfBound
    power hpower1 hpower2 word hw

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceHighAdjointMovingDifferenceQuotient_conditional_radiusPower_coordinate_word_bounds
