import Calderon.ActualReferenceGaugeTangentReciprocalSkew
import Calderon.SphereSobolevTangentialEndpointCompatibility

set_option autoImplicit false
noncomputable section
open Set
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceGaugeTangentSecondHighEndpointFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p)).comp
        (sphereSobolevRotationL (3/2 : ℝ) j i)

def referenceGaugeTangentSecondAdjointHighEndpointFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    nativeCoefficientRotationAdjointEndpointL (3/2 : ℝ)
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 3 i j p)) j i

lemma referenceGaugeTangentSecondHighEndpointFamily_lower_graph (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceGaugeTangentSecondHighEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) =
    (referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let F (i j : Fin 3) := referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p
  have hTerm (i j : Fin 3) (u : SphereSobolev (3/2 : ℝ)) :
      J (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (F i j)
        (sphereSobolevRotationL (3/2 : ℝ) j i u)) =
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (F i j)
        (sphereSobolevRotationL (1/2 : ℝ) j i (I u)) := by
    have hM := congrArg
      (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
        T (sphereSobolevRotationL (3/2 : ℝ) j i u))
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 (F i j))
    have hR := congrArg
      (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T u)
      (sphereSobolevRotationL_threehalf_half_compatibility j i)
    exact hM.trans (congrArg (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (F i j)) hR)
  apply ContinuousLinearMap.ext
  intro u
  have hRotation := referenceGaugeTangentSecondEndpointFamily_eq_rotation g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  have hPoint := congrArg
    (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T (I u)) hRotation
  change J (referenceGaugeTangentSecondHighEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p u) =
    referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p (I u)
  rw [hPoint]
  simp only [referenceGaugeTangentSecondHighEndpointFamily,referenceGaugeTangentSecondRotationEndpointFamily,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hTerm i j u))

lemma referenceGaugeTangentSecondAdjointHighEndpointFamily_lower_graph (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceGaugeTangentSecondAdjointHighEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) =
    (referenceGaugeTangentSecondAdjointEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let F (n : ℕ) (i j : Fin 3) := referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg n i j p
  have hValue (i j : Fin 3) : coefficientValue 3 (F 3 i j) = coefficientValue 2 (F 2 i j) := by
    funext x
    exact (coefficientValue_referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 3 i j p x).trans
      (coefficientValue_referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p x).symm
  have hTerm (i j : Fin 3) (u : SphereSobolev (3/2 : ℝ)) :
      J (nativeCoefficientRotationAdjointEndpointL (3/2 : ℝ)
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (F 3 i j)) j i u) =
      nativeCoefficientRotationAdjointEndpointL (1/2 : ℝ)
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (F 2 i j)) j i (I u) :=
    by
      have hJOrder : sphereSobolevInclusionL (1/2 : ℝ) (-1/2 : ℝ) (by norm_num) = J := by
        have hDelta : (-1/2 : ℝ)-(1/2 : ℝ) = (-(1/2 : ℝ))-(1/2 : ℝ) := by norm_num
        apply ContinuousLinearMap.ext
        intro v
        apply lp.ext
        funext k
        have hLeft := sphereSobolevInclusionL_apply (1/2 : ℝ) (-1/2 : ℝ) (by norm_num) v k
        have hRight := sphereSobolevInclusionL_apply (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v k
        exact hLeft.trans ((congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight t k • v k) hDelta).trans hRight.symm)
      have hPoint := congrArg
        (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T u)
        (nativeCoefficientRotationAdjoint_high_half_compatibility hcalc hF hO hD τ0
          (F 3 i j) (F 2 i j) (hValue i j) j i)
      rw [hJOrder] at hPoint
      simpa only [ContinuousLinearMap.comp_apply,I] using hPoint
  apply ContinuousLinearMap.ext
  intro u
  simp only [referenceGaugeTangentSecondAdjointHighEndpointFamily,referenceGaugeTangentSecondAdjointEndpointFamily,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply,map_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hTerm i j u))

variable (Q : Set (ℝ × (R3 × ℝ))) (R : ReferenceGaugeNormalReciprocalRoom g L Φ a Q)

def referenceGaugeTangentReciprocalHighSkewFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (referenceGaugeTangentSecondHighEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp (R.threeHalfMultiplier hcalc hF hO hD τ0 p) -
    (R.halfMultiplier hcalc hF hO hD τ0 p).comp (referenceGaugeTangentSecondAdjointHighEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)

lemma referenceGaugeTangentReciprocalHighSkewFamily_lower_graph (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceGaugeTangentReciprocalHighSkewFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p) =
    (referenceGaugeTangentReciprocalSkewFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let AH := referenceGaugeTangentSecondHighEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let ADH := referenceGaugeTangentSecondAdjointHighEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let AL := referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let ADL := referenceGaugeTangentSecondAdjointEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let MH := R.threeHalfMultiplier hcalc hF hO hD τ0 p
  let ML := R.halfMultiplier hcalc hF hO hD τ0 p
  let MN := R.negativeMultiplier hcalc hF hO hD τ0 p
  have hA (u : SphereSobolev (3/2 : ℝ)) : J (AH u) = AL (I u) :=
    congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T u)
      (referenceGaugeTangentSecondHighEndpointFamily_lower_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)
  have hAD (u : SphereSobolev (3/2 : ℝ)) : J (ADH u) = ADL (I u) :=
    congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T u)
      (referenceGaugeTangentSecondAdjointHighEndpointFamily_lower_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)
  have hMH (u : SphereSobolev (3/2 : ℝ)) : I (MH u) = ML (I u) :=
    congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T u)
      (R.high_half_compatibility hcalc hF hO hD τ0 p)
  have hML (v : SphereSobolev (1/2 : ℝ)) : J (ML v) = MN (J v) :=
    congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T v)
      (R.half_negative_compatibility hcalc hF hO hD τ0 p)
  apply ContinuousLinearMap.ext
  intro u
  have hFirst : J (AH (MH u)) = AL (ML (I u)) := (hA (MH u)).trans (congrArg AL (hMH u))
  have hSecond : J (ML (ADH u)) = MN (ADL (I u)) := (hML (ADH u)).trans (congrArg MN (hAD u))
  have hSkew := congrArg
    (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T (I u))
    (referenceGaugeTangentReciprocalSkewFamily_eq_explicit g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q R p)
  change J (AH (MH u)-ML (ADH u)) = _
  exact (J.map_sub _ _).trans
    ((congrArg₂ (fun x y : SphereSobolev (-(1/2 : ℝ)) => x-y) hFirst hSecond).trans hSkew.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondHighEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondAdjointHighEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondHighEndpointFamily_lower_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondAdjointHighEndpointFamily_lower_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentReciprocalHighSkewFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentReciprocalHighSkewFamily_lower_graph
