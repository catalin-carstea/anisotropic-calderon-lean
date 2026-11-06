import Calderon.ActualReferenceGaugeReciprocalRotationJets
import Calderon.ActualReferenceGaugeTangentDivergenceEndpoints

/-! Full upfront: actual-gauge-tangent-operator-author-oct15-v001/actual-reciprocal-tangent-author-v001/
EXPANSION-actual-skew-residual-v002.md. Same actual reciprocal, true pivot skew part. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier

attribute [local irreducible] nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  nativeThreeHalfCoefficientMulL sphereSobolevInclusionL sphereLowerDistributionalTranspose
  ContinuousLinearMap.inverse

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Q : Set (ℝ × (R3 × ℝ))) (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)

def referenceGaugeTangentReciprocalResidualCoefficient
    (p : (ℝ × (R3 × ℝ)) × R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    referenceGaugeTangentSecondRotationCoefficient g L Φ a i j p * R.rotationCoefficient i j p

lemma referenceGaugeTangentReciprocalResidualCoefficient_same_jet_values
    (n : ℕ) (p : ℝ × (R3 × ℝ)) (z : R3) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      coefficientValue n (referenceGaugeTangentSecondRotationJetsFamily
        g L y0 Φ B ε C ρ H a w hData hg n i j p) z * coefficientValue n (R.rotationJets n i j p) z) =
    referenceGaugeTangentReciprocalResidualCoefficient g L Φ a Q R (p,z) := by
  simp_rw [coefficientValue_referenceGaugeTangentSecondRotationJetsFamily,R.coefficientValue_rotationJets]
  rfl

def referenceGaugeTangentReciprocalResidualThreeHalfFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 3 i j p)).comp
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (R.rotationJets 3 i j p))

def referenceGaugeTangentReciprocalResidualHalfFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p)).comp
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (R.rotationJets 2 i j p))

def referenceGaugeTangentReciprocalResidualNegativeFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p)).comp
      (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (R.rotationJets 2 i j p))

lemma referenceGaugeTangentReciprocalResidual_high_half_compatibility (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
      (referenceGaugeTangentReciprocalResidualThreeHalfFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p) =
    (referenceGaugeTangentReciprocalResidualHalfFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [referenceGaugeTangentReciprocalResidualThreeHalfFamily,
    referenceGaugeTangentReciprocalResidualHalfFamily,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  let F3 := referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 3 i j p
  let F2 := referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p
  let H3 := R.rotationJets 3 i j p
  let H2 := R.rotationJets 2 i j p
  have hForward := congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      T (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 H3 u))
    (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 F3 F2 (by
      funext z
      rw [coefficientValue_referenceGaugeTangentSecondRotationJetsFamily,
        coefficientValue_referenceGaugeTangentSecondRotationJetsFamily]))
  have hH := congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T u)
    (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 H3 H2 (by
      funext z
      rw [R.coefficientValue_rotationJets,R.coefficientValue_rotationJets]))
  simp only [ContinuousLinearMap.comp_apply] at hForward hH
  exact hForward.trans (congrArg (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F2) hH)

lemma referenceGaugeTangentReciprocalResidual_half_negative_compatibility (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceGaugeTangentReciprocalResidualHalfFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p) =
    (referenceGaugeTangentReciprocalResidualNegativeFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p).comp
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [referenceGaugeTangentReciprocalResidualHalfFamily,
    referenceGaugeTangentReciprocalResidualNegativeFamily,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  let F2 := referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p
  let H2 := R.rotationJets 2 i j p
  have hForward := congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      T (nativeHalfCoefficientMulL hcalc hF hO hD τ0 H2 u))
    (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 F2)
  have hH := congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T u)
    (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 H2)
  simp only [ContinuousLinearMap.comp_apply] at hForward hH
  exact hForward.trans (congrArg (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F2) hH)

lemma contDiff_referenceGaugeTangentReciprocalResidualThreeHalfFamily :
    ContDiff ℝ ∞ (referenceGaugeTangentReciprocalResidualThreeHalfFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R) := by
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact (contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 _
    (contDiff_referenceGaugeTangentSecondRotationCoefficient g L y0 Φ B ε C ρ H a w hData hg i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentSecondRotationCoefficient_support g L y0 Φ B ε C ρ H a w hData i j)).clm_comp
      (contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 _
        (R.contDiff_rotationCoefficient i j) R.spatialSupport R.supportCompact (R.rotationCoefficient_support i j))

lemma exists_compact_referenceGaugeTangentReciprocalResidualThreeHalfFamily_bounds
    (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (referenceGaugeTangentReciprocalResidualThreeHalfFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R) p‖ ≤ M :=
  exists_compact_uniform_iteratedFDeriv_bound _
    (contDiff_referenceGaugeTangentReciprocalResidualThreeHalfFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R) K hK N

lemma contDiff_referenceGaugeTangentReciprocalResidualHalfFamily :
    ContDiff ℝ ∞ (referenceGaugeTangentReciprocalResidualHalfFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R) := by
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact (contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 _
    (contDiff_referenceGaugeTangentSecondRotationCoefficient g L y0 Φ B ε C ρ H a w hData hg i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentSecondRotationCoefficient_support g L y0 Φ B ε C ρ H a w hData i j)).clm_comp
      (contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 _
        (R.contDiff_rotationCoefficient i j) R.spatialSupport R.supportCompact (R.rotationCoefficient_support i j))

lemma exists_compact_referenceGaugeTangentReciprocalResidualHalfFamily_bounds
    (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (referenceGaugeTangentReciprocalResidualHalfFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R) p‖ ≤ M :=
  exists_compact_uniform_iteratedFDeriv_bound _
    (contDiff_referenceGaugeTangentReciprocalResidualHalfFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R) K hK N

lemma contDiff_referenceGaugeTangentReciprocalResidualNegativeFamily :
    ContDiff ℝ ∞ (referenceGaugeTangentReciprocalResidualNegativeFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R) := by
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact (contDiff_nativeNegativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 _
    (contDiff_referenceGaugeTangentSecondRotationCoefficient g L y0 Φ B ε C ρ H a w hData hg i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentSecondRotationCoefficient_support g L y0 Φ B ε C ρ H a w hData i j)).clm_comp
      (contDiff_nativeNegativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 _
        (R.contDiff_rotationCoefficient i j) R.spatialSupport R.supportCompact (R.rotationCoefficient_support i j))

lemma exists_compact_referenceGaugeTangentReciprocalResidualNegativeFamily_bounds
    (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (referenceGaugeTangentReciprocalResidualNegativeFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R) p‖ ≤ M :=
  exists_compact_uniform_iteratedFDeriv_bound _
    (contDiff_referenceGaugeTangentReciprocalResidualNegativeFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R) K hK N

def referenceGaugeTangentReciprocalSkewFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  nativeLowerRightMultiplierSkewPart hcalc hF hO hD τ0
    (referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) (R.jets 2 p)

lemma sphereSobolevDualPairing_referenceGaugeTangentReciprocalSkew
    (p : ℝ × (R3 × ℝ)) (u v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) v (referenceGaugeTangentReciprocalSkewFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p u) =
      -sphereSobolevDualPairing (1/2 : ℝ) u (referenceGaugeTangentReciprocalSkewFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p v) :=
  sphereSobolevDualPairing_nativeLowerRightMultiplierSkewPart hcalc hF hO hD τ0 _ _ u v

lemma referenceGaugeTangentReciprocalSkewFamily_eq_explicit (p : ℝ × (R3 × ℝ)) :
    referenceGaugeTangentReciprocalSkewFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p =
    (referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp (R.halfMultiplier hcalc hF hO hD τ0 p) -
      (R.negativeMultiplier hcalc hF hO hD τ0 p).comp
        (referenceGaugeTangentSecondAdjointEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) := by
  let A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let At : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    referenceGaugeTangentSecondAdjointEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let Mplus : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    R.halfMultiplier hcalc hF hO hD τ0 p
  let Mminus : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    R.negativeMultiplier hcalc hF hO hD τ0 p
  have hRight : sphereLowerDistributionalTranspose (A.comp Mplus) =
      Mminus.comp (sphereLowerDistributionalTranspose A) :=
    sphereLowerDistributionalTranspose_comp_nativeHalfCoefficientMulL hcalc hF hO hD τ0 A (R.jets 2 p)
  have hAdj : sphereLowerDistributionalTranspose A = At :=
    referenceGaugeTangentSecond_distributionalTranspose_eq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  have hTranspose : sphereLowerDistributionalTranspose (A.comp Mplus) = Mminus.comp At :=
    hRight.trans (congrArg
      (fun K : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Mminus.comp K) hAdj)
  apply ContinuousLinearMap.ext
  intro u
  have hValue : sphereLowerDistributionalTranspose (A.comp Mplus) u = Mminus (At u) :=
    congrArg (fun K : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => K u) hTranspose
  have hDef : referenceGaugeTangentReciprocalSkewFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p u =
        A (Mplus u)-sphereLowerDistributionalTranspose (A.comp Mplus) u := rfl
  exact hDef.trans
    (congrArg (fun v : SphereSobolev (-(1/2 : ℝ)) => A (Mplus u)-v) hValue)

lemma contDiff_referenceGaugeTangentReciprocalSkewFamily :
    ContDiff ℝ ∞ (referenceGaugeTangentReciprocalSkewFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R) := by
  have hEq : referenceGaugeTangentReciprocalSkewFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R = fun p =>
      (referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp (R.halfMultiplier hcalc hF hO hD τ0 p) -
        (R.negativeMultiplier hcalc hF hO hD τ0 p).comp
          (referenceGaugeTangentSecondAdjointEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) := by
    funext p
    exact referenceGaugeTangentReciprocalSkewFamily_eq_explicit g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p
  rw [hEq]
  exact ((contDiff_referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0).clm_comp
    (R.contDiff_halfMultiplier hcalc hF hO hD τ0)).sub
      ((R.contDiff_negativeMultiplier hcalc hF hO hD τ0).clm_comp
        (contDiff_referenceGaugeTangentSecondAdjointEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0))

lemma exists_compact_referenceGaugeTangentReciprocalSkewFamily_bounds
    (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (referenceGaugeTangentReciprocalSkewFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R) p‖ ≤ M :=
  exists_compact_uniform_iteratedFDeriv_bound _
    (contDiff_referenceGaugeTangentReciprocalSkewFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R) K hK N

lemma referenceGaugeTangentSecond_commutator_reciprocal_eq_residual (p : ℝ × (R3 × ℝ)) :
    (referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp (R.halfMultiplier hcalc hF hO hD τ0 p) -
      (R.negativeMultiplier hcalc hF hO hD τ0 p).comp (referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) =
    (referenceGaugeTangentReciprocalResidualNegativeFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p).comp
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) := by
  let F := fun i j => referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p
  let Hn := fun i j => R.rotationJets 2 i j p
  have hActual : referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p =
      nativeCoefficientRotationFieldL hcalc hF hO hD τ0 F := by
    rw [referenceGaugeTangentSecondEndpointFamily_eq_rotation]
    rfl
  rw [hActual]
  exact nativeCoefficientRotationField_commutator_nativeMultiplier hcalc hF hO hD τ0 F (R.jets 2 p) Hn (by
    intro i j x
    have hGValue : coefficientValue 2 (R.jets 2 p) = fun z : R3 => R.scalar (p,z) := by
      funext z
      exact R.coefficientValue_jets 2 p z
    rw [hGValue]
    exact (R.coefficientValue_rotationJets 2 i j p x.val).trans
      (R.rotationCoefficient_eq_rotation i j p x.val))

lemma referenceGaugeTangentSecond_right_inverse_defect_eq_skew_add_residual
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ R.parameterRoom) :
    ((referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) -
      sphereLowerDistributionalTranspose (referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)).comp
      (referenceGaugeNormalHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse =
    referenceGaugeTangentReciprocalSkewFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p +
      (referenceGaugeTangentReciprocalResidualNegativeFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p).comp
        (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) := by
  have hGraph := (referenceGaugeNormalReciprocalRoom_native_inverse_graph
    g L Φ y0 B ε C ρ H a w hData hg R hcalc hF hO hD τ0 p hp).1
  rw [hGraph]
  have hSplit := referenceGaugeTangentSecond_rightMultiplier_defect_eq_skew_add_commutator
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p (R.jets 2 p)
  exact hSplit.trans (congrArg
    (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      referenceGaugeTangentReciprocalSkewFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p+T)
    (referenceGaugeTangentSecond_commutator_reciprocal_eq_residual g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentReciprocalResidualCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentReciprocalResidualCoefficient_same_jet_values
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentReciprocalResidualThreeHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentReciprocalResidualHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentReciprocalResidualNegativeFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentReciprocalResidual_high_half_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentReciprocalResidual_half_negative_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentReciprocalResidualThreeHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_compact_referenceGaugeTangentReciprocalResidualThreeHalfFamily_bounds
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentReciprocalResidualHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_compact_referenceGaugeTangentReciprocalResidualHalfFamily_bounds
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentReciprocalResidualNegativeFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_compact_referenceGaugeTangentReciprocalResidualNegativeFamily_bounds
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentReciprocalSkewFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceGaugeTangentReciprocalSkew
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentReciprocalSkewFamily_eq_explicit
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentReciprocalSkewFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_compact_referenceGaugeTangentReciprocalSkewFamily_bounds
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecond_commutator_reciprocal_eq_residual
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecond_right_inverse_defect_eq_skew_add_residual
