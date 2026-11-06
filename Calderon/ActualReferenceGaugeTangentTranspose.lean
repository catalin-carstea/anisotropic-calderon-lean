import Calderon.ActualReferenceGaugeTangentOperator
import Calderon.NativeCoefficientRotationProductRule
import Calderon.NativeHalfCoefficientRotationDualAdjunction
import Calderon.NativeSmoothMultiplierCommonSupportJets
import Calderon.SphereSobolevCoordinateNegativeHalfOrder
import Calderon.ActualReferenceLowerBoundaryTranspose

/-! Full upfront: actual-gauge-tangent-operator-author-oct15-v001/
EXPANSION-transpose-v003.md. Genuine probability-L2 pivot transpose, actual scalar divergence. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeNegativeHalfCoefficientCoordinateProduct SmoothSphereRotation

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

def referenceGaugeTangentSecondRotationCoefficient (i j : Fin 3)
    (p : (ℝ × (R3 × ℝ)) × R3) : ℝ :=
  referenceGaugeTangentSecondRemainder g L Φ a i p * p.2 j

include hData hg in
lemma contDiff_referenceGaugeTangentSecondRotationCoefficient (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceGaugeTangentSecondRotationCoefficient g L Φ a i j) :=
  (contDiff_referenceGaugeTangentSecondRemainder g L Φ a y0 B ε C ρ H w hData hg i).mul
    ((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd)

include hData in
lemma referenceGaugeTangentSecondRotationCoefficient_support
    (i j : Fin 3) (p : ℝ × (R3 × ℝ)) (z : R3) (hz : z ∉ closedBall (0 : R3) 3) :
    referenceGaugeTangentSecondRotationCoefficient g L Φ a i j (p,z) = 0 := by
  unfold referenceGaugeTangentSecondRotationCoefficient
  rw [referenceGaugeTangentSecondRemainder_support g L Φ a y0 B ε C ρ H w hData i p z hz,zero_mul]

include hData hg in
def referenceGaugeTangentSecondRotationJetsFamily (n : ℕ) (i j : Fin 3) :
    (ℝ × (R3 × ℝ)) → SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (referenceGaugeTangentSecondRotationCoefficient g L Φ a i j)
    (contDiff_referenceGaugeTangentSecondRotationCoefficient g L y0 Φ B ε C ρ H a w hData hg i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentSecondRotationCoefficient_support g L y0 Φ B ε C ρ H a w hData i j)

lemma coefficientValue_referenceGaugeTangentSecondRotationJetsFamily
    (n : ℕ) (i j : Fin 3) (p : ℝ × (R3 × ℝ)) (z : R3) :
    coefficientValue n (referenceGaugeTangentSecondRotationJetsFamily
      g L y0 Φ B ε C ρ H a w hData hg n i j p) z =
      referenceGaugeTangentSecondRotationCoefficient g L Φ a i j (p,z) :=
  coefficientValue_commonSupportCoefficientFamily n _ _ _ _ _ p z

def referenceGaugeTangentSecondRotationDerivativeCoefficient (i j : Fin 3)
    (p : (ℝ × (R3 × ℝ)) × R3) : ℝ :=
  p.2 j * smoothMultiplierSpatialDerivative
    (referenceGaugeTangentSecondRotationCoefficient g L Φ a i j) i p -
  p.2 i * smoothMultiplierSpatialDerivative
    (referenceGaugeTangentSecondRotationCoefficient g L Φ a i j) j p

include hData hg in
lemma contDiff_referenceGaugeTangentSecondRotationDerivativeCoefficient (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceGaugeTangentSecondRotationDerivativeCoefficient g L Φ a i j) :=
  (((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd).mul
    (contDiff_smoothMultiplierSpatialDerivative _
      (contDiff_referenceGaugeTangentSecondRotationCoefficient g L y0 Φ B ε C ρ H a w hData hg i j) i)).sub
  (((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd).mul
    (contDiff_smoothMultiplierSpatialDerivative _
      (contDiff_referenceGaugeTangentSecondRotationCoefficient g L y0 Φ B ε C ρ H a w hData hg i j) j))

include hData hg in
lemma referenceGaugeTangentSecondRotationDerivativeCoefficient_eq_rotation
    (i j : Fin 3) (p : ℝ × (R3 × ℝ)) (z : R3) :
    referenceGaugeTangentSecondRotationDerivativeCoefficient g L Φ a i j (p,z) =
      sphereRotationDerivative j i
        (fun x : R3 => referenceGaugeTangentSecondRotationCoefficient g L Φ a i j (p,x)) z := by
  have hf := contDiff_referenceGaugeTangentSecondRotationCoefficient g L y0 Φ B ε C ρ H a w hData hg i j
  unfold referenceGaugeTangentSecondRotationDerivativeCoefficient
  rw [smoothMultiplierSpatialDerivative_eq_slice_gradient _ hf i,
    smoothMultiplierSpatialDerivative_eq_slice_gradient _ hf j]
  simp only [MetricVolume.gradient_coordinate,sphereRotationDerivative,rotationVector,
    map_sub,map_smul,smul_eq_mul,MetricVolume.coordinateVector]

include hData hg in
lemma referenceGaugeTangentSecondRotationDerivativeCoefficient_support
    (i j : Fin 3) (p : ℝ × (R3 × ℝ)) (z : R3) (hz : z ∉ closedBall (0 : R3) 3) :
    referenceGaugeTangentSecondRotationDerivativeCoefficient g L Φ a i j (p,z) = 0 := by
  have hf := contDiff_referenceGaugeTangentSecondRotationCoefficient g L y0 Φ B ε C ρ H a w hData hg i j
  have hs := referenceGaugeTangentSecondRotationCoefficient_support g L y0 Φ B ε C ρ H a w hData i j
  unfold referenceGaugeTangentSecondRotationDerivativeCoefficient
  rw [smoothMultiplierSpatialDerivative_zero_outside _ hf _ (isCompact_closedBall _ _) hs i p z hz,
    smoothMultiplierSpatialDerivative_zero_outside _ hf _ (isCompact_closedBall _ _) hs j p z hz]
  ring

include hData hg in
def referenceGaugeTangentSecondRotationDerivativeJetsFamily (n : ℕ) (i j : Fin 3) :
    (ℝ × (R3 × ℝ)) → SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (referenceGaugeTangentSecondRotationDerivativeCoefficient g L Φ a i j)
    (contDiff_referenceGaugeTangentSecondRotationDerivativeCoefficient g L y0 Φ B ε C ρ H a w hData hg i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentSecondRotationDerivativeCoefficient_support g L y0 Φ B ε C ρ H a w hData hg i j)

lemma coefficientValue_referenceGaugeTangentSecondRotationDerivativeJetsFamily
    (n : ℕ) (i j : Fin 3) (p : ℝ × (R3 × ℝ)) (z : R3) :
    coefficientValue n (referenceGaugeTangentSecondRotationDerivativeJetsFamily
      g L y0 Φ B ε C ρ H a w hData hg n i j p) z =
      referenceGaugeTangentSecondRotationDerivativeCoefficient g L Φ a i j (p,z) :=
  coefficientValue_commonSupportCoefficientFamily n _ _ _ _ _ p z

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceGaugeTangentSecondRotationEndpointFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p)).comp
        (sphereSobolevRotationL (1/2 : ℝ) j i)

lemma referenceGaugeTangentSecondEndpointFamily_eq_rotation (p : ℝ × (R3 × ℝ)) :
    referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p =
      referenceGaugeTangentSecondRotationEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p := by
  apply ContinuousLinearMap.ext
  intro u
  unfold referenceGaugeTangentSecondEndpointFamily referenceGaugeTangentSecondRotationEndpointFamily
    sphereTangentialDerivativeL
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hp := nativeNegativeHalfCoefficientMulL_coordinate_comp_eq hcalc hF hO hD τ0
    (referenceGaugeTangentSecondRemainderJetsFamily g L Φ a y0 B ε C ρ H w hData hg 2 i p)
    (referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p) j (by
      ext x
      change coefficientValue 2 (referenceGaugeTangentSecondRotationJetsFamily
        g L y0 Φ B ε C ρ H a w hData hg 2 i j p) x.val =
        coefficientValue 2 (referenceGaugeTangentSecondRemainderJetsFamily
          g L Φ a y0 B ε C ρ H w hData hg 2 i p) x.val * x.val j
      rw [coefficientValue_referenceGaugeTangentSecondRotationJetsFamily,
        coefficientValue_referenceGaugeTangentSecondRemainderJetsFamily]
      rfl)
  have ho := congrArg
    (fun M : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceGaugeTangentSecondRemainderJetsFamily g L Φ a y0 B ε C ρ H w hData hg 2 i p)
          (M (sphereSobolevRotationL (1/2 : ℝ) j i u)))
    (sphereSobolevLinearCoordinateMulL_negative_half_notation_eq hF hO hD (EuclideanSpace.single j 1))
  exact ho.trans (congrArg
    (fun M : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      M (sphereSobolevRotationL (1/2 : ℝ) j i u)) hp)

def referenceGaugeTangentSecondAdjointEndpointFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    nativeCoefficientRotationAdjointEndpointL (1/2 : ℝ)
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p)) j i

lemma sphereSobolevDualPairing_referenceGaugeTangentSecond_adjoint
    (p : ℝ × (R3 × ℝ)) (u v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) v
      (referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p u) =
    sphereSobolevDualPairing (1/2 : ℝ) u
      (referenceGaugeTangentSecondAdjointEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p v) := by
  rw [referenceGaugeTangentSecondEndpointFamily_eq_rotation]
  unfold referenceGaugeTangentSecondRotationEndpointFamily referenceGaugeTangentSecondAdjointEndpointFamily
  simp only [ContinuousLinearMap.sum_apply,sphereSobolevDualPairing,inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact sphereSobolevDualPairing_nativeHalfCoefficientRotation_adjoint hcalc hF hO hD τ0
    (referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p) j i u v

lemma referenceGaugeTangentSecond_distributionalTranspose_eq (p : ℝ × (R3 × ℝ)) :
    sphereLowerDistributionalTranspose
      (referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) =
      referenceGaugeTangentSecondAdjointEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_eq_of_dualPairing_eq (1/2 : ℝ)
  intro v
  exact (sphereSobolevDualPairing_lower_distributionalTranspose _ v u).symm.trans
    (sphereSobolevDualPairing_referenceGaugeTangentSecond_adjoint
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p v u)

def referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceGaugeTangentSecondRotationDerivativeJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p)

def referenceGaugeTangentSecondDivergenceHalfMultiplierFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceGaugeTangentSecondRotationDerivativeJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p)

lemma referenceGaugeTangentSecondAdjoint_eq_neg_add_divergence (p : ℝ × (R3 × ℝ)) :
    referenceGaugeTangentSecondAdjointEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p =
      -referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p -
      (referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
        (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) := by
  let F : Fin 3 → Fin 3 → SmoothCoefficientJets 2 := fun i j =>
    referenceGaugeTangentSecondRotationJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p
  let G : Fin 3 → Fin 3 → SmoothCoefficientJets 2 := fun i j =>
    referenceGaugeTangentSecondRotationDerivativeJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 i j p
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let P (i j : Fin 3) : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (F i j)).comp
      (sphereSobolevRotationL (1/2 : ℝ) j i)
  let Q (i j : Fin 3) : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (G i j)
  let A (i j : Fin 3) : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    nativeCoefficientRotationAdjointEndpointL (1/2 : ℝ)
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (F i j)) j i
  have hDerivative (i j : Fin 3) (x : UnitSphere) : coefficientValue 2 (G i j) x.val =
      sphereRotationDerivative j i (coefficientValue 2 (F i j)) x.val := by
    have hFValue : coefficientValue 2 (F i j) = fun z : R3 =>
        referenceGaugeTangentSecondRotationCoefficient g L Φ a i j (p,z) :=
      funext (fun z => coefficientValue_referenceGaugeTangentSecondRotationJetsFamily
        g L y0 Φ B ε C ρ H a w hData hg 2 i j p z)
    have hRotate : sphereRotationDerivative j i (fun z : R3 =>
        referenceGaugeTangentSecondRotationCoefficient g L Φ a i j (p,z)) x.val =
        sphereRotationDerivative j i (coefficientValue 2 (F i j)) x.val :=
      congrArg (fun f : R3 → ℝ => sphereRotationDerivative j i f x.val) hFValue.symm
    exact (coefficientValue_referenceGaugeTangentSecondRotationDerivativeJetsFamily
      g L y0 Φ B ε C ρ H a w hData hg 2 i j p x.val).trans
      ((referenceGaugeTangentSecondRotationDerivativeCoefficient_eq_rotation
        g L y0 Φ B ε C ρ H a w hData hg i j p x.val).trans hRotate)
  have hTerm (i j : Fin 3) : A i j = -P i j-(Q i j).comp I := by
    have hp : (sphereSobolevRotationL (1/2 : ℝ) j i).comp
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (F i j)) = P i j+(Q i j).comp I :=
      sphereSobolevRotationL_nativeCoefficient_product_rule hcalc hF hO hD τ0
        (F i j) (G i j) j i (hDerivative i j)
    have hDef : A i j = -((sphereSobolevRotationL (1/2 : ℝ) j i).comp
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (F i j))) := rfl
    have hNeg : -((sphereSobolevRotationL (1/2 : ℝ) j i).comp
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (F i j))) = -(P i j+(Q i j).comp I) :=
      congrArg (fun K : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => -K) hp
    exact hDef.trans (hNeg.trans (by abel))
  have hAdjDef : referenceGaugeTangentSecondAdjointEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p = ∑ i : Fin 3, ∑ j : Fin 3, A i j := rfl
  have hRotDef : referenceGaugeTangentSecondRotationEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p = ∑ i : Fin 3, ∑ j : Fin 3, P i j := rfl
  have hDivDef : referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p = ∑ i : Fin 3, ∑ j : Fin 3, Q i j := rfl
  have hComp : (∑ i : Fin 3, ∑ j : Fin 3, Q i j).comp I =
      ∑ i : Fin 3, ∑ j : Fin 3, (Q i j).comp I := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply]
  have hSum : (∑ i : Fin 3, ∑ j : Fin 3, A i j) =
      -(∑ i : Fin 3, ∑ j : Fin 3, P i j)-(∑ i : Fin 3, ∑ j : Fin 3, Q i j).comp I := by
    have hTerms : (∑ i : Fin 3, ∑ j : Fin 3, A i j) =
        ∑ i : Fin 3, ∑ j : Fin 3, (-P i j-(Q i j).comp I) :=
      Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => hTerm i j))
    have hDistrib : (∑ i : Fin 3, ∑ j : Fin 3, (-P i j-(Q i j).comp I)) =
        -(∑ i : Fin 3, ∑ j : Fin 3, P i j)-(∑ i : Fin 3, ∑ j : Fin 3, (Q i j).comp I) := by
      simp only [Finset.sum_sub_distrib,Finset.sum_neg_distrib]
    exact hTerms.trans (hDistrib.trans
      (congrArg (fun K : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
        -(∑ i : Fin 3, ∑ j : Fin 3, P i j)-K) hComp.symm))
  have hT : referenceGaugeTangentSecondEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p = ∑ i : Fin 3, ∑ j : Fin 3, P i j :=
    (referenceGaugeTangentSecondEndpointFamily_eq_rotation
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).trans hRotDef
  have hOutput : -(∑ i : Fin 3, ∑ j : Fin 3, P i j)-(∑ i : Fin 3, ∑ j : Fin 3, Q i j).comp I =
      -referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p-
      (referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp I :=
    congrArg₂ (fun K : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      fun Z : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => -K-Z.comp I)
      hT.symm hDivDef.symm
  exact hAdjDef.trans (hSum.trans hOutput)

lemma referenceGaugeTangentSecond_sub_transpose_eq_firstOrder_add_zeroOrder
    (p : ℝ × (R3 × ℝ)) :
    referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p -
      sphereLowerDistributionalTranspose
        (referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) =
      2 • referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p +
      (referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
        (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) := by
  let T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    referenceGaugeTangentSecondAdjointEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let D : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    (referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num))
  have hTranspose : sphereLowerDistributionalTranspose T = A :=
    referenceGaugeTangentSecond_distributionalTranspose_eq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  have hAdj : A = -T-D := referenceGaugeTangentSecondAdjoint_eq_neg_add_divergence
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  have hFirst : T-sphereLowerDistributionalTranspose T = T-A :=
    congrArg (fun K : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T-K) hTranspose
  have hSecond : T-A = T-(-T-D) :=
    congrArg (fun K : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T-K) hAdj
  have hAlg : T-(-T-D) = (2 : ℕ) • T+D := by
    rw [two_nsmul]
    abel
  exact hFirst.trans (hSecond.trans hAlg)

lemma contDiff_referenceGaugeTangentSecondAdjointEndpointFamily :
    ContDiff ℝ ∞ (referenceGaugeTangentSecondAdjointEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) := by
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact (contDiff_const.clm_comp
    (contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 _
      (contDiff_referenceGaugeTangentSecondRotationCoefficient g L y0 Φ B ε C ρ H a w hData hg i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (referenceGaugeTangentSecondRotationCoefficient_support g L y0 Φ B ε C ρ H a w hData i j))).neg

lemma contDiff_referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily :
    ContDiff ℝ ∞ (referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) := by
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact contDiff_nativeNegativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 _
    (contDiff_referenceGaugeTangentSecondRotationDerivativeCoefficient g L y0 Φ B ε C ρ H a w hData hg i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentSecondRotationDerivativeCoefficient_support g L y0 Φ B ε C ρ H a w hData hg i j)

lemma contDiff_referenceGaugeTangentSecondDivergenceHalfMultiplierFamily :
    ContDiff ℝ ∞ (referenceGaugeTangentSecondDivergenceHalfMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) := by
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 _
    (contDiff_referenceGaugeTangentSecondRotationDerivativeCoefficient g L y0 Φ B ε C ρ H a w hData hg i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentSecondRotationDerivativeCoefficient_support g L y0 Φ B ε C ρ H a w hData hg i j)

lemma exists_compact_referenceGaugeTangentSecondAdjointEndpointFamily_parameter_jets
    (Q : Set (ℝ × (R3 × ℝ))) (hQ : IsCompact Q) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ Q,
      ‖iteratedFDeriv ℝ k (referenceGaugeTangentSecondAdjointEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) p‖ ≤ M :=
  exists_compact_uniform_iteratedFDeriv_bound _
    (contDiff_referenceGaugeTangentSecondAdjointEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) Q hQ N

lemma exists_compact_referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily_parameter_jets
    (Q : Set (ℝ × (R3 × ℝ))) (hQ : IsCompact Q) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ Q,
      ‖iteratedFDeriv ℝ k (referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) p‖ ≤ M :=
  exists_compact_uniform_iteratedFDeriv_bound _
    (contDiff_referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) Q hQ N

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondRotationCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentSecondRotationCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondRotationCoefficient_support
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondRotationJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceGaugeTangentSecondRotationJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondRotationDerivativeCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentSecondRotationDerivativeCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondRotationDerivativeCoefficient_eq_rotation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondRotationDerivativeCoefficient_support
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondRotationDerivativeJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceGaugeTangentSecondRotationDerivativeJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondRotationEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondEndpointFamily_eq_rotation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondAdjointEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceGaugeTangentSecond_adjoint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecond_distributionalTranspose_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondDivergenceHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondAdjoint_eq_neg_add_divergence
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecond_sub_transpose_eq_firstOrder_add_zeroOrder
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentSecondAdjointEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentSecondDivergenceHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_compact_referenceGaugeTangentSecondAdjointEndpointFamily_parameter_jets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_compact_referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily_parameter_jets
