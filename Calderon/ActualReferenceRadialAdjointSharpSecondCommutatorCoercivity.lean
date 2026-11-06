import Calderon.ActualReferenceHighSkewReciprocalDictionaryTransferJointRegularity
import Calderon.ActualReferenceGaugeReciprocalProductJets
import Calderon.ActualReferenceGaugeReciprocalRotationJets
import Calderon.ActualReferenceSmoothMultiplierFirstRadialJet
import Calderon.SignedTaylorIncludedCommutatorTransport
import Calderon.ActualReferenceCompletedRotationSecondRemainderGraph
import Calderon.NativeThreeHalfRotationMultiplierProductRule
import Calderon.NativeThreeHalfCoefficientProduct
import Calderon.NativeThreeHalfCoefficientCommutation
import Calderon.NativeThreeHalfBoundaryMultiplierLocalSmoothness
import Calderon.NativeBoundaryMultiplierLocalSmoothness
import Calderon.ActualAdjointRadialSmoothMultiplierNegativeFactor

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  SmoothSphereRotation NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion

local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local instance : CompleteSpace Half := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance : CompleteSpace Neg := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))))

/-- Literal twice the actual tangent coefficient times the same reciprocal. -/
def referenceRadialSkewProductCoefficient (i j : Fin 3) (z : Pphys × R3) : ℝ :=
  2 * referenceGaugeTangentSecondRotationCoefficient g L Φ a i j z * Room.scalar z
local notation "cfield" => referenceRadialSkewProductCoefficient g L y0 Φ ρ a Room

include hData hg in
lemma contDiff_referenceRadialSkewProductCoefficient (i j : Fin 3) :
    ContDiff ℝ ∞ (cfield i j) := by
  exact ((contDiff_const.mul
    (contDiff_referenceGaugeTangentSecondRotationCoefficient
      g L y0 Φ B ε C ρ H a w hData hg i j)).mul Room.smooth)

include hData in
lemma referenceRadialSkewProductCoefficient_support
    (i j : Fin 3) (p : Pphys) (x : R3) (hx : x ∉ closedBall (0 : R3) 3) :
    cfield i j (p,x) = 0 := by
  unfold referenceRadialSkewProductCoefficient
  rw [referenceGaugeTangentSecondRotationCoefficient_support
    g L y0 Φ B ε C ρ H a w hData i j p x hx]
  ring

/-- Minus the same ordered rotation of the unscaled actual product n*m. -/
def referenceRadialSkewDerivativeCoefficient (i j : Fin 3) (z : Pphys × R3) : ℝ :=
  -(z.2 j * smoothMultiplierSpatialDerivative
      (fun z : Pphys × R3 =>
        referenceGaugeTangentSecondRotationCoefficient g L Φ a i j z * Room.scalar z) i z -
    z.2 i * smoothMultiplierSpatialDerivative
      (fun z : Pphys × R3 =>
        referenceGaugeTangentSecondRotationCoefficient g L Φ a i j z * Room.scalar z) j z)
local notation "dfield" => referenceRadialSkewDerivativeCoefficient g L y0 Φ ρ a Room

include hData hg in
lemma contDiff_referenceRadialSkewDerivativeCoefficient (i j : Fin 3) :
    ContDiff ℝ ∞ (dfield i j) := by
  have hp : ContDiff ℝ ∞ (fun z : Pphys × R3 =>
      referenceGaugeTangentSecondRotationCoefficient g L Φ a i j z * Room.scalar z) :=
    (contDiff_referenceGaugeTangentSecondRotationCoefficient
      g L y0 Φ B ε C ρ H a w hData hg i j).mul Room.smooth
  exact ((((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd).mul
    (contDiff_smoothMultiplierSpatialDerivative _ hp i)).sub
    (((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd).mul
      (contDiff_smoothMultiplierSpatialDerivative _ hp j))).neg

include hData hg in
lemma referenceRadialSkewDerivativeCoefficient_support
    (i j : Fin 3) (p : Pphys) (x : R3) (hx : x ∉ closedBall (0 : R3) 3) :
    dfield i j (p,x) = 0 := by
  let f : Pphys × R3 → ℝ := fun z =>
    referenceGaugeTangentSecondRotationCoefficient g L Φ a i j z * Room.scalar z
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_referenceGaugeTangentSecondRotationCoefficient
      g L y0 Φ B ε C ρ H a w hData hg i j).mul Room.smooth
  have hs (p : Pphys) (x : R3) (hx : x ∉ closedBall (0 : R3) 3) : f (p,x) = 0 := by
    change referenceGaugeTangentSecondRotationCoefficient g L Φ a i j (p,x) * Room.scalar (p,x) = 0
    rw [referenceGaugeTangentSecondRotationCoefficient_support
      g L y0 Φ B ε C ρ H a w hData i j p x hx,zero_mul]
  unfold referenceRadialSkewDerivativeCoefficient
  rw [smoothMultiplierSpatialDerivative_zero_outside f hf _ (isCompact_closedBall _ _) hs i p x hx,
    smoothMultiplierSpatialDerivative_zero_outside f hf _ (isCompact_closedBall _ _) hs j p x hx]
  ring

include hData hg in
lemma referenceRadialSkewDerivativeCoefficient_eq_rotation
    (i j : Fin 3) (p : Pphys) (x : R3) :
    dfield i j (p,x) = -sphereRotationDerivative j i
      (fun x : R3 => referenceGaugeTangentSecondRotationCoefficient g L Φ a i j (p,x) *
        Room.scalar (p,x)) x := by
  let f : Pphys × R3 → ℝ := fun z =>
    referenceGaugeTangentSecondRotationCoefficient g L Φ a i j z * Room.scalar z
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_referenceGaugeTangentSecondRotationCoefficient
      g L y0 Φ B ε C ρ H a w hData hg i j).mul Room.smooth
  unfold referenceRadialSkewDerivativeCoefficient
  rw [smoothMultiplierSpatialDerivative_eq_slice_gradient f hf i,
    smoothMultiplierSpatialDerivative_eq_slice_gradient f hf j]
  simp only [MetricVolume.gradient_coordinate,sphereRotationDerivative,rotationVector,
    map_sub,map_smul,smul_eq_mul,MetricVolume.coordinateVector]
  rfl

def referenceRadialSkewProductJets (n : ℕ) (i j : Fin 3) : Pphys → SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (cfield i j)
    (contDiff_referenceRadialSkewProductCoefficient g L y0 Φ B ε C ρ H a w hData hg Room i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRadialSkewProductCoefficient_support g L y0 Φ B ε C ρ H a w hData Room i j)

def referenceRadialSkewDerivativeJets (n : ℕ) (i j : Fin 3) : Pphys → SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (dfield i j)
    (contDiff_referenceRadialSkewDerivativeCoefficient g L y0 Φ B ε C ρ H a w hData hg Room i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRadialSkewDerivativeCoefficient_support g L y0 Φ B ε C ρ H a w hData hg Room i j)

lemma coefficientValue_referenceRadialSkewProductJets
    (n : ℕ) (i j : Fin 3) (p : Pphys) (x : R3) :
    coefficientValue n (referenceRadialSkewProductJets
      g L y0 Φ B ε C ρ H a w hData hg Room n i j p) x = cfield i j (p,x) :=
  coefficientValue_commonSupportCoefficientFamily n _ _ _ _ _ p x

lemma coefficientValue_referenceRadialSkewDerivativeJets
    (n : ℕ) (i j : Fin 3) (p : Pphys) (x : R3) :
    coefficientValue n (referenceRadialSkewDerivativeJets
      g L y0 Φ B ε C ρ H a w hData hg Room n i j p) x = dfield i j (p,x) :=
  coefficientValue_commonSupportCoefficientFamily n _ _ _ _ _ p x

local notation "Dl" => referenceNormalizedAdjointHalfDefectFamily
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))) Room
local notation "Dh" => referenceNormalizedAdjointHighDefectFamily
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))) Room
local notation "Sh" => referenceSharpRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Sl" => referenceLowerRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Vh" => referenceGaugeTangentReciprocalHighSkewFamily
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))) Room
local notation "Vl" => referenceGaugeTangentReciprocalSkewFamily
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))) Room

def referenceNormalizedAdjointNegativeDefectFamily (p : Pphys) : Neg →L[ℝ] Neg :=
  -realHalfOperatorAdjointL (Dl p)
local notation "Dn" => referenceNormalizedAdjointNegativeDefectFamily
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room

lemma referenceNormalizedAdjointNegativeDefectFamily_inclusion
    (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hRoom : (q,(y,r)) ∈ Room.parameterRoom) :
    (Dn (q,(y,r))).comp (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) =
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp (Dl (q,(y,r))) := by
  let p := (q,(y,r))
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Z := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Q : Half → Neg → ℝ := fun v z => sphereSobolevDualPairing (1/2 : ℝ) v z
  let QN : Neg → Half → ℝ := fun z v => sphereSobolevDualPairing (-(1/2 : ℝ)) z v
  have hFlip (v : Half) (z : Neg) : Q v z = QN z v := by
    change ⟪v,z⟫_ℝ = ⟪z,v⟫_ℝ
    exact (real_inner_comm v z).symm
  have hJPair (v z : Half) : Q v (J z) = ⟪Z v,Z z⟫_ℝ :=
    (hFlip v (J z)).trans
      ((sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num) z v).trans
        (real_inner_comm (Z z) (Z v)).symm)
  have hJSymm (v z : Half) : Q v (J z) = Q z (J v) :=
    (hJPair v z).trans ((real_inner_comm (Z v) (Z z)).symm.trans (hJPair z v).symm)
  have hNeg (v : Half) (z : Neg) : Q v (-z) = -Q v z := by
    change ⟪v,-z⟫_ℝ = -⟪v,z⟫_ℝ
    exact inner_neg_right v z
  have hy2 : ‖y-y0‖ ≤ 2*ρ := by linarith [hData.1.2.1]
  have hSkew (u z : Half) : Q z (J (Dl p u)) = -Q u (J (Dl p z)) :=
    (hFlip z (J (Dl p u))).trans
      ((sphereSobolevDualPairing_referenceNormalizedAdjointHalfDefect_skew
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))) Room hKernel
          q hq y hy2 r hSegment hRoom u z).trans
            (congrArg Neg.neg (hFlip u (J (Dl p z))).symm))
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_eq_of_dualPairing_eq (1/2 : ℝ)
  intro z
  have hAdj : Q (Dl p z) (J u) = Q z (realHalfOperatorAdjointL (Dl p) (J u)) :=
    sphereSobolevDualPairing_realHalfOperatorAdjoint (Dl p) z (J u)
  change Q z (-(realHalfOperatorAdjointL (Dl p) (J u))) = Q z (J (Dl p u))
  exact (hNeg z _).trans
    ((congrArg Neg.neg hAdj.symm).trans
      ((congrArg Neg.neg (hJSymm (Dl p z) u)).trans (hSkew u z).symm))

attribute [local irreducible] referenceAdjointThreeHalfRadialFamily
  referenceSharpRadialTraceSecondRemainder referenceGaugeTangentReciprocalHighSkewFamily
  referenceNormalizedAdjointHighDefectFamily referenceRadialEndpointInvertibleLocus
  referenceLowerRadialTraceSecondRemainder referenceAdjointHalfRadialFamily
  referenceGaugeTangentReciprocalSkewFamily referenceNormalizedAdjointHalfDefectFamily
  secondTaylorRemainder

def referenceRadialDefectSecondCommutator (q : ℝ) (y : R3) (r : ℝ) : Half →L[ℝ] Neg :=
  (Dn (q,(y,r))).comp (Sl q y r) - (Sl q y r).comp (Dl (q,(y,r)))

lemma referenceRadialDefectSecondCommutator_graph
    (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hRoom : (q,(y,r)) ∈ Room.parameterRoom)
    (hAgree : (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp (Dh (q,(y,r))) =
      (Dl (q,(y,r))).comp (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)))
    (u : Hi) :
    referenceRadialDefectSecondCommutator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) =
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (Dl (q,(y,r)) (Sh q y r u)) -
      Sl q y r (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (Dh (q,(y,r)) u)) := by
  let p := (q,(y,r))
  let I : Hi →L[ℝ] Half := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : Half →L[ℝ] Neg := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let S : Half →L[ℝ] Neg := Sl q y r
  let D : Half →L[ℝ] Half := Dl p
  let Dhi : Hi →L[ℝ] Hi := Dh p
  let DN : Neg →L[ℝ] Neg := Dn p
  have hS : S (I u) = J (Sh q y r u) :=
    (congrArg (fun A : Hi →L[ℝ] Neg => A u)
      (referenceSharpRadialTraceSecondRemainder_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment)).symm
  have hAgreeTyped : I.comp Dhi = D.comp I := by
    simpa only [I,Dhi,D,p] using hAgree
  have hAgreement : D (I u) = I (Dhi u) := by
    have hPoint := congrArg (fun A : Hi →L[ℝ] Half => A u) hAgreeTyped
    simpa only [ContinuousLinearMap.comp_apply] using hPoint.symm
  have hDn : DN (J (Sh q y r u)) = J (D (Sh q y r u)) :=
    congrArg (fun A : Half →L[ℝ] Neg => A (Sh q y r u))
      (referenceNormalizedAdjointNegativeDefectFamily_inclusion
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hKernel
          q hq y hy r hSegment hRoom)
  have hFirst : DN (S (I u)) = J (D (Sh q y r u)) :=
    (congrArg (fun z : Neg => DN z) hS).trans hDn
  have hSecond : S (D (I u)) = S (I (Dhi u)) :=
    congrArg (fun z : Half => S z) hAgreement
  change DN (S (I u))-S (D (I u)) = J (D (Sh q y r u))-S (I (Dhi u))
  exact congrArg₂ (fun a b : Neg => a-b) hFirst hSecond

local notation "CJ" => referenceRadialSkewProductJets
  g L y0 Φ B ε C ρ H a w hData hg Room
local notation "DJ" => referenceRadialSkewDerivativeJets
  g L y0 Φ B ε C ρ H a w hData hg Room

/-- Actual native scalar algebra extracted from the measured physical caller. -/
lemma nativeThreeHalfCoefficientMulL_smul_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (c : ℝ) (F : SmoothCoefficientJets 3) (u : SphereSobolev (3/2 : ℝ)) :
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (c • F) u =
      c • nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F u := by
  let MH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
  let T := nativeThreeHalfValueTraceL hcalc hF hO hD τ0
  let Lift := harmonicLiftCompletion hF
  have hCoeff := congrArg (fun A : BallSobolev 2 →L[ℝ] BallSobolev 2 => T (A (Lift u)))
    (coefficientMultiplier_smul hcalc 2 c F)
  change T (coefficientMultiplier hcalc 2 (c • F) (Lift u)) = _
  exact hCoeff.trans (T.map_smul c (coefficientMultiplier hcalc 2 F (Lift u)))

/-- The same actual coefficient value identity, without a new analytic hypothesis. -/
lemma nativeThreeHalfCoefficientMulL_add_products_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F₁ G₁ F₂ G₂ Q : SmoothCoefficientJets 3)
    (hValue : ∀ x : R3, coefficientValue 3 Q x =
      coefficientValue 3 F₁ x * coefficientValue 3 G₁ x +
        coefficientValue 3 F₂ x * coefficientValue 3 G₂ x)
    (u : SphereSobolev (3/2 : ℝ)) :
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q u =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F₁
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G₁ u) +
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F₂
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G₂ u) := by
  let MH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
  let T := nativeThreeHalfValueTraceL hcalc hF hO hD τ0
  let Lift := harmonicLiftCompletion hF
  have hBulk (U : BallSobolev 2) : coefficientMultiplier hcalc 2 Q U =
      coefficientMultiplier hcalc 2 F₁ (coefficientMultiplier hcalc 2 G₁ U) +
        coefficientMultiplier hcalc 2 F₂ (coefficientMultiplier hcalc 2 G₂ U) := by
    apply TauCeti.Wkp.ext 2
    rw [TauCeti.Wkp.value_add]
    apply Lp.ext
    filter_upwards [coefficientMultiplier_value_ae hcalc 2 Q U,
      coefficientMultiplier_value_ae hcalc 2 F₁ (coefficientMultiplier hcalc 2 G₁ U),
      coefficientMultiplier_value_ae hcalc 2 G₁ U,
      coefficientMultiplier_value_ae hcalc 2 F₂ (coefficientMultiplier hcalc 2 G₂ U),
      coefficientMultiplier_value_ae hcalc 2 G₂ U,
      Lp.coeFn_add
        (TauCeti.Wkp.value 2 (coefficientMultiplier hcalc 2 F₁ (coefficientMultiplier hcalc 2 G₁ U)))
        (TauCeti.Wkp.value 2 (coefficientMultiplier hcalc 2 F₂ (coefficientMultiplier hcalc 2 G₂ U)))]
      with x hQ hF₁ hG₁ hF₂ hG₂ hadd
    rw [hQ,hadd]
    simp only [Pi.add_apply]
    rw [hF₁,hG₁,hF₂,hG₂,hValue x]
    ring
  have hTrace (F G : SmoothCoefficientJets 3) :
      T (coefficientMultiplier hcalc 2 F (coefficientMultiplier hcalc 2 G (Lift u))) =
        MH F (MH G u) := by
    have hRaw := nativeThreeHalfValueTraceL_coefficientMultiplier hcalc hF hO hD τ0 F
      (coefficientMultiplier hcalc 2 G (Lift u))
    change T (coefficientMultiplier hcalc 2 F (coefficientMultiplier hcalc 2 G (Lift u))) =
      MH F (T (coefficientMultiplier hcalc 2 G (Lift u))) at hRaw
    have hInner : T (coefficientMultiplier hcalc 2 G (Lift u)) = MH G u := by
      simp only [MH,nativeThreeHalfCoefficientMulL,ContinuousLinearMap.comp_apply,T,Lift]
    exact hRaw.trans (congrArg (MH F) hInner)
  change T (coefficientMultiplier hcalc 2 Q (Lift u)) = _
  exact (congrArg T (hBulk (Lift u))).trans
    ((T.map_add _ _).trans (congrArg₂ (fun a b : Hi => a+b) (hTrace F₁ G₁) (hTrace F₂ G₂)))

/-- The actual Half product law, obtained from the same high native multipliers. -/
lemma nativeHalfCoefficientMulL_double_product_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (N3 M3 C3 : SmoothCoefficientJets 3) (N2 M2 : SmoothCoefficientJets 2)
    (hNValue : coefficientValue 3 N3 = coefficientValue 2 N2)
    (hMValue : coefficientValue 3 M3 = coefficientValue 2 M2)
    (hCValue : ∀ x : R3, coefficientValue 3 C3 x =
      coefficientValue 3 N3 x * coefficientValue 3 M3 x +
        coefficientValue 3 N3 x * coefficientValue 3 M3 x)
    (u : SphereSobolev (1/2 : ℝ)) :
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets C3) u =
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 N2
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 M2 u) +
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 N2
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 M2 u) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let MH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
  let ML := nativeHalfCoefficientMulL hcalc hF hO hD τ0
  let C2 := smoothMultiplierLowerJets C3
  have hHigh (z : Hi) : MH C3 z = MH N3 (MH M3 z)+MH N3 (MH M3 z) :=
    nativeThreeHalfCoefficientMulL_add_products_apply
      hcalc hF hO hD τ0 N3 M3 N3 M3 C3 hCValue z
  have hNC (z : Hi) : I (MH N3 z) = ML N2 (I z) :=
    congrArg (fun A : Hi →L[ℝ] Half => A z)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 N3 N2 hNValue)
  have hMC (z : Hi) : I (MH M3 z) = ML M2 (I z) :=
    congrArg (fun A : Hi →L[ℝ] Half => A z)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 M3 M2 hMValue)
  have hCC (z : Hi) : I (MH C3 z) = ML C2 (I z) :=
    congrArg (fun A : Hi →L[ℝ] Half => A z)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 C3 C2
        (coefficientValue_smoothMultiplierLowerJets C3).symm)
  let A : Half →L[ℝ] Half := ML C2
  let B : Half →L[ℝ] Half := (ML N2).comp (ML M2)+(ML N2).comp (ML M2)
  have hTest (z : Hi) : A (I z) = B (I z) :=
    (hCC z).symm.trans ((congrArg I (hHigh z)).trans
      ((I.map_add _ _).trans (congrArg₂ (fun a b : Half => a+b)
        ((hNC (MH M3 z)).trans (congrArg (ML N2) (hMC z)))
        ((hNC (MH M3 z)).trans (congrArg (ML N2) (hMC z))))))
  have hAll := (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).equalizer
    A.continuous B.continuous (funext hTest)
  have hPoint := congrFun hAll u
  change ML C2 u = ML N2 (ML M2 u)+ML N2 (ML M2 u) at hPoint
  exact hPoint

/-- Exact rotation-left form at the high endpoint; its low version follows below. -/
lemma referenceGaugeTangentReciprocalHighSkewFamily_rotation_left (p : Pphys) :
    Vh p = ∑ i : Fin 3, ∑ j : Fin 3,
      ((sphereSobolevRotationL (3/2 : ℝ) j i).comp
          (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (CJ 3 i j p)) +
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
          (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (DJ 3 i j p))) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let MH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
  let ML := nativeHalfCoefficientMulL hcalc hF hO hD τ0
  let T := nativeThreeHalfValueTraceL hcalc hF hO hD τ0
  let Lift := harmonicLiftCompletion hF
  have hScale := nativeThreeHalfCoefficientMulL_smul_apply hcalc hF hO hD τ0
  have hTwoProducts := nativeThreeHalfCoefficientMulL_add_products_apply hcalc hF hO hD τ0
  have hTerm (i j : Fin 3) (u : Hi) :
      let N3 := referenceGaugeTangentSecondRotationJetsFamily
        g L y0 Φ B ε C ρ H a w hData hg 3 i j p
      let N2 := referenceGaugeTangentSecondRotationJetsFamily
        g L y0 Φ B ε C ρ H a w hData hg 2 i j p
      ML N2 (sphereSobolevRotationL (3/2 : ℝ) j i (Room.threeHalfMultiplier hcalc hF hO hD τ0 p u)) +
        Room.halfMultiplier hcalc hF hO hD τ0 p (sphereSobolevRotationL (3/2 : ℝ) j i (MH N3 u)) =
      sphereSobolevRotationL (3/2 : ℝ) j i (MH (CJ 3 i j p) u) + I (MH (DJ 3 i j p) u) := by
    intro N3 N2
    let NP3 := referenceGaugeTangentSecondRotationDerivativeJetsFamily
      g L y0 Φ B ε C ρ H a w hData hg 3 i j p
    let NP2 := referenceGaugeTangentSecondRotationDerivativeJetsFamily
      g L y0 Φ B ε C ρ H a w hData hg 2 i j p
    let M3 := Room.jets 3 p
    let M2 := Room.jets 2 p
    let MP3 := Room.rotationJets 3 i j p
    let MP2 := Room.rotationJets 2 i j p
    let C3 := CJ 3 i j p
    let C2 := smoothMultiplierLowerJets C3
    let D3 := DJ 3 i j p
    let RH := sphereSobolevRotationL (3/2 : ℝ) j i
    change ML N2 (RH (MH M3 u))+ML M2 (RH (MH N3 u)) =
      RH (MH C3 u)+I (MH D3 u)
    have hNValue : coefficientValue 3 N3 = coefficientValue 2 N2 := by
      funext x
      exact (coefficientValue_referenceGaugeTangentSecondRotationJetsFamily
        g L y0 Φ B ε C ρ H a w hData hg 3 i j p x).trans
        (coefficientValue_referenceGaugeTangentSecondRotationJetsFamily
          g L y0 Φ B ε C ρ H a w hData hg 2 i j p x).symm
    have hNPValue : coefficientValue 3 NP3 = coefficientValue 2 NP2 := by
      funext x
      exact (coefficientValue_referenceGaugeTangentSecondRotationDerivativeJetsFamily
        g L y0 Φ B ε C ρ H a w hData hg 3 i j p x).trans
        (coefficientValue_referenceGaugeTangentSecondRotationDerivativeJetsFamily
          g L y0 Φ B ε C ρ H a w hData hg 2 i j p x).symm
    have hMValue : coefficientValue 3 M3 = coefficientValue 2 M2 := by
      funext x
      rw [Room.coefficientValue_jets,Room.coefficientValue_jets]
    have hMPValue : coefficientValue 3 MP3 = coefficientValue 2 MP2 := by
      funext x
      rw [Room.coefficientValue_rotationJets,Room.coefficientValue_rotationJets]
    have hNPDerivative (x : UnitSphere) : coefficientValue 2 NP2 x.val =
        sphereRotationDerivative j i (coefficientValue 2 N2) x.val := by
      have hFun : coefficientValue 2 N2 = fun x =>
          referenceGaugeTangentSecondRotationCoefficient g L Φ a i j (p,x) :=
        funext (coefficientValue_referenceGaugeTangentSecondRotationJetsFamily
          g L y0 Φ B ε C ρ H a w hData hg 2 i j p)
      rw [hFun]
      exact (coefficientValue_referenceGaugeTangentSecondRotationDerivativeJetsFamily
        g L y0 Φ B ε C ρ H a w hData hg 2 i j p x.val).trans
        (referenceGaugeTangentSecondRotationDerivativeCoefficient_eq_rotation
          g L y0 Φ B ε C ρ H a w hData hg i j p x.val)
    have hMPDerivative (x : UnitSphere) : coefficientValue 2 MP2 x.val =
        sphereRotationDerivative j i (coefficientValue 2 M2) x.val := by
      have hFun : coefficientValue 2 M2 = fun x => Room.scalar (p,x) :=
        funext (Room.coefficientValue_jets 2 p)
      rw [hFun]
      exact (Room.coefficientValue_rotationJets 2 i j p x.val).trans
        (Room.rotationCoefficient_eq_rotation i j p x.val)
    have hRN (v : Hi) : RH (MH N3 v) = ML N2 (RH v)+I (MH NP3 v) :=
      congrArg (fun A : Hi →L[ℝ] Half => A v)
        (sphereSobolevRotationL_nativeThreeHalfCoefficient_product_rule
          hcalc hF hO hD τ0 N3 NP3 N2 NP2 hNValue hNPValue j i hNPDerivative)
    have hRM (v : Hi) : RH (MH M3 v) = ML M2 (RH v)+I (MH MP3 v) :=
      congrArg (fun A : Hi →L[ℝ] Half => A v)
        (sphereSobolevRotationL_nativeThreeHalfCoefficient_product_rule
          hcalc hF hO hD τ0 M3 MP3 M2 MP2 hMValue hMPValue j i hMPDerivative)
    have hCValue (x : R3) : coefficientValue 3 C3 x =
        coefficientValue 3 N3 x * coefficientValue 3 M3 x +
          coefficientValue 3 N3 x * coefficientValue 3 M3 x := by
      rw [coefficientValue_referenceRadialSkewProductJets,
        coefficientValue_referenceGaugeTangentSecondRotationJetsFamily,Room.coefficientValue_jets]
      unfold referenceRadialSkewProductCoefficient
      ring
    have hC (v : Hi) : MH C3 v = MH N3 (MH M3 v)+MH N3 (MH M3 v) :=
      hTwoProducts N3 M3 N3 M3 C3 hCValue v
    let nf : SmoothData := nativeH2CoefficientSmoothData N3
    let mf : SmoothData := nativeH2CoefficientSmoothData M3
    have hnfun : nf.1 = fun x => referenceGaugeTangentSecondRotationCoefficient g L Φ a i j (p,x) :=
      funext (coefficientValue_referenceGaugeTangentSecondRotationJetsFamily
        g L y0 Φ B ε C ρ H a w hData hg 3 i j p)
    have hmfun : mf.1 = fun x => Room.scalar (p,x) := funext (Room.coefficientValue_jets 3 p)
    have hProductRotation (x : R3) :
        sphereRotationDerivative j i (fun x => nf.1 x * mf.1 x) x =
          nf.1 x * sphereRotationDerivative j i mf.1 x +
            sphereRotationDerivative j i nf.1 x * mf.1 x :=
      sphereRotationDerivative_mul_smooth nf mf j i x
    have hDValue (x : R3) : coefficientValue 3 ((-1 : ℝ) • D3) x =
        coefficientValue 3 NP3 x * coefficientValue 3 M3 x +
          coefficientValue 3 N3 x * coefficientValue 3 MP3 x := by
      rw [coefficientValue_smul]
      simp only [Pi.smul_apply,smul_eq_mul]
      rw [coefficientValue_referenceRadialSkewDerivativeJets,
        referenceRadialSkewDerivativeCoefficient_eq_rotation
          g L y0 Φ B ε C ρ H a w hData hg Room i j p x,
        coefficientValue_referenceGaugeTangentSecondRotationDerivativeJetsFamily,
        coefficientValue_referenceGaugeTangentSecondRotationJetsFamily,
        Room.coefficientValue_jets,Room.coefficientValue_rotationJets,
        referenceGaugeTangentSecondRotationDerivativeCoefficient_eq_rotation
          g L y0 Φ B ε C ρ H a w hData hg i j p x,
        Room.rotationCoefficient_eq_rotation]
      have hp := hProductRotation x
      rw [hnfun,hmfun] at hp
      rw [hp]
      ring
    have hDsum (v : Hi) : -(MH D3 v) = MH NP3 (MH M3 v)+MH N3 (MH MP3 v) := by
      have hScaled := hScale (-1) D3 v
      change MH ((-1 : ℝ) • D3) v = (-1 : ℝ) • MH D3 v at hScaled
      have hMinus : MH ((-1 : ℝ) • D3) v = -(MH D3 v) :=
        hScaled.trans (neg_one_smul ℝ (MH D3 v))
      have hProduct := hTwoProducts NP3 M3 N3 MP3 ((-1 : ℝ) • D3) hDValue v
      change MH ((-1 : ℝ) • D3) v = MH NP3 (MH M3 v)+MH N3 (MH MP3 v) at hProduct
      exact hMinus.symm.trans hProduct
    have hNC (v : Hi) : I (MH N3 v) = ML N2 (I v) :=
      congrArg (fun A : Hi →L[ℝ] Half => A v)
        (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 N3 N2 hNValue)
    have hMC (v : Hi) : I (MH M3 v) = ML M2 (I v) :=
      congrArg (fun A : Hi →L[ℝ] Half => A v)
        (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 M3 M2 hMValue)
    have hCC (v : Hi) : I (MH C3 v) = ML C2 (I v) :=
      congrArg (fun A : Hi →L[ℝ] Half => A v)
        (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 C3 C2
          (coefficientValue_smoothMultiplierLowerJets C3).symm)
    have hCL (v : Half) : ML C2 v = ML N2 (ML M2 v)+ML N2 (ML M2 v) :=
      nativeHalfCoefficientMulL_double_product_apply
        hcalc hF hO hD τ0 N3 M3 C3 N2 M2 hNValue hMValue hCValue v
    have hDerivativeC (x : UnitSphere) :
        coefficientValue 2 (smoothMultiplierLowerJets ((-2 : ℝ) • D3)) x.val =
          sphereRotationDerivative j i (coefficientValue 2 C2) x.val := by
      let pf : SmoothData := ⟨fun x => nf.1 x * mf.1 x,nf.2.mul mf.2⟩
      let twof : SmoothData := ⟨fun _ : R3 => (2 : ℝ),contDiff_const⟩
      have hcFun : coefficientValue 2 C2 = fun x => (twof.1 x)*(pf.1 x) := by
        funext z
        rw [coefficientValue_smoothMultiplierLowerJets,
          coefficientValue_referenceRadialSkewProductJets]
        unfold referenceRadialSkewProductCoefficient
        change 2*referenceGaugeTangentSecondRotationCoefficient g L Φ a i j (p,z)*Room.scalar (p,z) =
          2*(nf.1 z*mf.1 z)
        rw [congrFun hnfun z,congrFun hmfun z]
        ring
      have hRotTwo : sphereRotationDerivative j i twof.1 x.val = 0 := by
        change (fderiv ℝ (fun _ : R3 => (2 : ℝ)) x.val) (rotationVector j i x.val) = 0
        rw [fderiv_const_apply]
        rfl
      have hRot := sphereRotationDerivative_mul_smooth twof pf j i x.val
      rw [hRotTwo,zero_mul,add_zero] at hRot
      change sphereRotationDerivative j i (fun z : R3 => twof.1 z*pf.1 z) x.val =
        twof.1 x.val*sphereRotationDerivative j i pf.1 x.val at hRot
      rw [coefficientValue_smoothMultiplierLowerJets,coefficientValue_smul]
      simp only [Pi.smul_apply,smul_eq_mul]
      rw [coefficientValue_referenceRadialSkewDerivativeJets,
        referenceRadialSkewDerivativeCoefficient_eq_rotation
          g L y0 Φ B ε C ρ H a w hData hg Room i j p x.val,hcFun]
      rw [hRot]
      change (-2 : ℝ)*(-sphereRotationDerivative j i
        (fun z => referenceGaugeTangentSecondRotationCoefficient g L Φ a i j (p,z)*Room.scalar (p,z)) x.val) =
          2*sphereRotationDerivative j i (fun z => nf.1 z*mf.1 z) x.val
      rw [hnfun,hmfun]
      ring
    have hRC (v : Hi) : RH (MH C3 v) = ML C2 (RH v)+I ((-2 : ℝ) • MH D3 v) :=
      (congrArg (fun A : Hi →L[ℝ] Half => A v)
        (sphereSobolevRotationL_nativeThreeHalfCoefficient_product_rule
          hcalc hF hO hD τ0 C3 ((-2 : ℝ) • D3) C2
            (smoothMultiplierLowerJets ((-2 : ℝ) • D3))
            (coefficientValue_smoothMultiplierLowerJets C3).symm
            (coefficientValue_smoothMultiplierLowerJets ((-2 : ℝ) • D3)).symm
            j i hDerivativeC)).trans
              (congrArg (fun z : Hi => ML C2 (RH v)+I z) (hScale (-2) D3 v))
    have hArrange {E : Type 0} [AddCommGroup E] (a b c : E) :
        (a+b)+(a+c) = (a+a)+(b+c) := by abel
    have hScalar {E : Type 0} [AddCommGroup E] [Module ℝ E] (a : E) :
        (-2 : ℝ) • a+a = -a := by
      rw [neg_smul,two_smul]
      abel
    have hCross : MH N3 (MH MP3 u)+MH M3 (MH NP3 u) = -(MH D3 u) := by
      have hComm : MH M3 (MH NP3 u) = MH NP3 (MH M3 u) := by
        simpa only [MH] using
          nativeThreeHalfCoefficientMulL_comm_apply hcalc hF hO hD τ0 M3 NP3 u
      exact (congrArg (fun z : Hi => MH N3 (MH MP3 u)+z) hComm).trans
        ((add_comm _ _).trans (hDsum u).symm)
    have hSumLeft : ML N2 (RH (MH M3 u))+ML M2 (RH (MH N3 u)) =
        ML C2 (RH u)+I (-(MH D3 u)) := by
      have hFirst := (congrArg (ML N2) (hRM u)).trans ((ML N2).map_add _ _)
      have hSecond := (congrArg (ML M2) (hRN u)).trans ((ML M2).map_add _ _)
      have hFirstTransport :
          ML N2 (ML M2 (RH u))+ML N2 (I (MH MP3 u)) =
          ML N2 (ML M2 (RH u))+I (MH N3 (MH MP3 u)) :=
        congrArg (fun z : Half => ML N2 (ML M2 (RH u))+z) (hNC (MH MP3 u)).symm
      have hSecondTransport :
          ML M2 (ML N2 (RH u))+ML M2 (I (MH NP3 u)) =
          ML N2 (ML M2 (RH u))+I (MH M3 (MH NP3 u)) :=
        congrArg₂ (fun a b : Half => a+b)
          (nativeHalfCoefficientMulL_comm_apply hcalc hF hO hD τ0 M2 N2 (RH u))
          (hMC (MH NP3 u)).symm
      exact (congrArg₂ (fun a b : Half => a+b)
        (hFirst.trans hFirstTransport) (hSecond.trans hSecondTransport)).trans
          ((hArrange _ _ _).trans
            (congrArg₂ (fun a b : Half => a+b) (hCL (RH u)).symm
              ((I.map_add _ _).symm.trans (congrArg I hCross))))
    have hSumRight : RH (MH C3 u)+I (MH D3 u) = ML C2 (RH u)+I (-(MH D3 u)) :=
      (congrArg (fun z : Half => z+I (MH D3 u)) (hRC u)).trans
        ((add_assoc _ _ _).trans
          (congrArg (fun z : Half => ML C2 (RH u)+z)
            ((I.map_add _ _).symm.trans (congrArg I (hScalar (MH D3 u))))))
    exact hSumLeft.trans hSumRight.symm
  apply ContinuousLinearMap.ext
  intro u
  have hTerms := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hTerm i j u))
  simpa only [referenceGaugeTangentReciprocalHighSkewFamily,
    referenceGaugeTangentSecondHighEndpointFamily,referenceGaugeTangentSecondAdjointHighEndpointFamily,
    nativeCoefficientRotationAdjointEndpointL,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sum_apply,map_sum,map_neg,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.sum_neg_distrib,sub_neg_eq_add,MH,ML,I] using hTerms

lemma referenceGaugeTangentReciprocalSkewFamily_rotation_left (p : Pphys) :
    Vl p = ∑ i : Fin 3, ∑ j : Fin 3,
      ((sphereSobolevRotationL (1/2 : ℝ) j i).comp
          (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets (CJ 3 i j p))) +
        (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets (DJ 3 i j p))).comp
          (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num))) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let MH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
  let ML := nativeHalfCoefficientMulL hcalc hF hO hD τ0
  let MN := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
  let A : Half →L[ℝ] Neg := Vl p
  let TargetLow : Half →L[ℝ] Neg := ∑ i : Fin 3, ∑ j : Fin 3,
    ((sphereSobolevRotationL (1/2 : ℝ) j i).comp (ML (smoothMultiplierLowerJets (CJ 3 i j p))) +
      (MN (smoothMultiplierLowerJets (DJ 3 i j p))).comp J)
  have hV (u : Hi) : A (I u) = J (Vh p u) :=
    (congrArg (fun T : Hi →L[ℝ] Neg => T u)
      (referenceGaugeTangentReciprocalHighSkewFamily_lower_graph
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))) Room p)).symm
  have hTerm (i j : Fin 3) (u : Hi) :
      J (sphereSobolevRotationL (3/2 : ℝ) j i (MH (CJ 3 i j p) u)+I (MH (DJ 3 i j p) u)) =
      sphereSobolevRotationL (1/2 : ℝ) j i
          (ML (smoothMultiplierLowerJets (CJ 3 i j p)) (I u)) +
        MN (smoothMultiplierLowerJets (DJ 3 i j p)) (J (I u)) := by
    have hC := congrArg (fun T : Hi →L[ℝ] Half => T u)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0
        (CJ 3 i j p) (smoothMultiplierLowerJets (CJ 3 i j p))
        (coefficientValue_smoothMultiplierLowerJets (CJ 3 i j p)).symm)
    have hDC := congrArg (fun T : Hi →L[ℝ] Half => T u)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0
        (DJ 3 i j p) (smoothMultiplierLowerJets (DJ 3 i j p))
        (coefficientValue_smoothMultiplierLowerJets (DJ 3 i j p)).symm)
    have hDLower := congrArg (fun T : Half →L[ℝ] Neg => T (I u))
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0
        (smoothMultiplierLowerJets (DJ 3 i j p)))
    have hRot := congrArg (fun T : Hi →L[ℝ] Neg => T (MH (CJ 3 i j p) u))
      (sphereSobolevRotationL_threehalf_half_compatibility j i)
    exact (J.map_add _ _).trans (congrArg₂ (fun a b : Neg => a+b)
      (hRot.trans (congrArg (sphereSobolevRotationL (1/2 : ℝ) j i) hC))
      ((congrArg J hDC).trans hDLower))
  have hTest (u : Hi) : A (I u) = TargetLow (I u) := by
    have hHigh := congrArg (fun T : Hi →L[ℝ] Half => T u)
      (referenceGaugeTangentReciprocalHighSkewFamily_rotation_left
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room p)
    have hTerms := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ => Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
        (fun j _ => hTerm i j u))
    have hSum := (congrArg J hHigh).trans (by
      simpa only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply,map_sum] using hTerms)
    exact (hV u).trans hSum
  have hAll := (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).equalizer
    A.continuous TargetLow.continuous (funext hTest)
  exact ContinuousLinearMap.ext (fun u => congrFun hAll u)

def referenceRadialTangentSecondCommutator (q : ℝ) (y : R3) (r : ℝ) : Half →L[ℝ] Neg :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (((referenceLowerRadialRotationSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r).comp
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets (CJ 3 i j (q,(y,r))))) -
      (sphereSobolevRotationL (1/2 : ℝ) j i).comp
        (secondTaylorRemainder (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (CJ 3 i j (q,(y,r))) (q,(y,t))) r)) -
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (secondTaylorRemainder (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (DJ 3 i j (q,(y,r))) (q,(y,t))) r))

/-- Frozen coefficient in radial Taylor transport, on the actual native lower graph. -/
lemma referenceSmoothMultiplierSecondRemainder_lower_graph
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0) (Q : SmoothCoefficientJets 3)
    (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (secondTaylorRemainder (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))) r v) =
      referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) v) -
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
        (referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r v) := by
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let ML := nativeHalfCoefficientMulL hcalc hF hO hD τ0
  let MN := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
  let G : SmoothCoefficientJets 3 → (Half →L[ℝ] Half) := fun Q =>
    secondTaylorRemainder (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))) r
  let F := fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))
  let A := fun t : ℝ => referenceLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let M := ML (smoothMultiplierLowerJets Q)
  let N := MN (smoothMultiplierLowerJets Q)
  have hFS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ F (θ*r) := by
    have hJoint : ContDiffAt ℝ ∞ (referenceSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q) (q,(y,θ*r)) :=
      contDiffAt_referenceSmoothMultiplierBoundaryCommutatorFamily_fixed
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q
          (q,(y,θ*r)) (hSegment θ hθ)
    have hEmbed : ContDiffAt ℝ ∞ (fun t : ℝ => (q,(y,t))) (θ*r) :=
      contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id)
    simpa only [F,Function.comp_def] using hJoint.comp (θ*r) hEmbed
  have hAS (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ A (θ*r) := by
    have hi := hSegment θ hθ
    unfold referenceRadialEndpointInvertibleLocus at hi
    exact (contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,θ*r))
        hi.2.2 hi.2.1).comp (f := fun t : ℝ => (q,(y,t))) (θ*r)
          (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun t => J.comp (F t)) =ᶠ[𝓝 (θ*r)] (fun t => (A t).comp M-N.comp (A t)) := by
    have hNear : ∀ᶠ t : ℝ in 𝓝 (θ*r), (q,(y,t)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
      (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)).eventually
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds (hSegment θ hθ))
    filter_upwards [hNear] with t ht
    apply ContinuousLinearMap.ext
    intro z
    exact referenceSmoothMultiplierBoundaryCommutatorFamily_lower_agreement
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q (q,(y,t)) ht z
  have hOperator := secondTaylorRemainder_included_commutator F A J M N r hFS hAS hEq
  have hPoint := congrArg (fun T : Half →L[ℝ] Neg => T v) hOperator
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,
    referenceLowerRadialTraceSecondRemainder,F,A,G,M,N] using hPoint

lemma referenceRadialTangentSecondCommutator_graph
    (hKernel : UnitBallValueTraceKernel τ0) (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (u : Hi) :
    referenceRadialTangentSecondCommutator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) =
      Vl (q,(y,r)) (Sh q y r u)-Sl q y r (Vh (q,(y,r)) u) := by
  let p := (q,(y,r))
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let MH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
  let ML := nativeHalfCoefficientMulL hcalc hF hO hD τ0
  let MN := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
  let RotH := fun (i j : Fin 3) => sphereSobolevRotationL (3/2 : ℝ) j i
  let RotL := fun (i j : Fin 3) => sphereSobolevRotationL (1/2 : ℝ) j i
  let Cr := fun (i j : Fin 3) => referenceLowerRadialRotationSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r
  let G : SmoothCoefficientJets 3 → (Half →L[ℝ] Half) := fun Q =>
    secondTaylorRemainder (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))) r
  let CL := fun i j => ML (smoothMultiplierLowerJets (CJ 3 i j p))
  let CH := fun i j => MH (CJ 3 i j p)
  let DL := fun i j => ML (smoothMultiplierLowerJets (DJ 3 i j p))
  let DH := fun i j => MH (DJ 3 i j p)
  let DN := fun i j => MN (smoothMultiplierLowerJets (DJ 3 i j p))
  have hS (v : Hi) : Sl q y r (I v) = J (Sh q y r v) :=
    (congrArg (fun A : Hi →L[ℝ] Neg => A v)
      (referenceSharpRadialTraceSecondRemainder_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment)).symm
  have hIMap (Q : SmoothCoefficientJets 3) (v : Hi) :
      I (MH Q v) = ML (smoothMultiplierLowerJets Q) (I v) :=
    congrArg (fun A : Hi →L[ℝ] Half => A v)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 Q
        (smoothMultiplierLowerJets Q) (coefficientValue_smoothMultiplierLowerJets Q).symm)
  have hJMap (Q : SmoothCoefficientJets 3) (v : Half) :
      J (ML (smoothMultiplierLowerJets Q) v) = MN (smoothMultiplierLowerJets Q) (J v) :=
    congrArg (fun A : Half →L[ℝ] Neg => A v)
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q))
  have hLower (Q : SmoothCoefficientJets 3) (v : Half) :
      J (G Q v) = Sl q y r (ML (smoothMultiplierLowerJets Q) v) -
        MN (smoothMultiplierLowerJets Q) (Sl q y r v) := by
    exact referenceSmoothMultiplierSecondRemainder_lower_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q q y r hSegment v
  have hUpper (Q : SmoothCoefficientJets 3) (v : Hi) :
      G Q (I v) = Sh q y r (MH Q v)-ML (smoothMultiplierLowerJets Q) (Sh q y r v) := by
    apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    change J (G Q (I v)) = J (Sh q y r (MH Q v)-ML (smoothMultiplierLowerJets Q) (Sh q y r v))
    have hFirst := (congrArg (Sl q y r) (hIMap Q v).symm).trans (hS (MH Q v))
    have hSecond := (congrArg (MN (smoothMultiplierLowerJets Q)) (hS v)).trans
      (hJMap Q (Sh q y r v)).symm
    exact (hLower Q (I v)).trans
      ((congrArg₂ (fun a b : Neg => a-b) hFirst hSecond).trans (J.map_sub _ _).symm)
  have hVector {E : Type 0} [AddCommGroup E] (a b c d e : E) :
      ((a-b)-(a-c))-(d-e) = (c+e)-(b+d) := by abel
  have hTerm (i j : Fin 3) :
      (Cr i j (CL i j (I u))-RotL i j (G (CJ 3 i j p) (I u)))-J (G (DJ 3 i j p) (I u)) =
      (RotL i j (CL i j (Sh q y r u))+DN i j (J (Sh q y r u))) -
        Sl q y r (RotH i j (CH i j u)+I (DH i j u)) := by
    have hCr : Cr i j (CL i j (I u)) =
        RotL i j (Sh q y r (CH i j u))-Sl q y r (RotH i j (CH i j u)) :=
      (congrArg (Cr i j) (hIMap (CJ 3 i j p) u)).symm.trans
        (referenceLowerRadialRotationSecondRemainder_completed_graph
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r hSegment (CH i j u))
    have hRotG : RotL i j (G (CJ 3 i j p) (I u)) =
        RotL i j (Sh q y r (CH i j u))-RotL i j (CL i j (Sh q y r u)) :=
      (congrArg (RotL i j) (hUpper (CJ 3 i j p) u)).trans ((RotL i j).map_sub _ _)
    have hDG : J (G (DJ 3 i j p) (I u)) =
        Sl q y r (I (DH i j u))-DN i j (J (Sh q y r u)) :=
      (hLower (DJ 3 i j p) (I u)).trans (congrArg₂ (fun a b : Neg => a-b)
        (congrArg (Sl q y r) (hIMap (DJ 3 i j p) u).symm)
        (congrArg (DN i j) (hS u)))
    exact (congrArg₂ (fun a b : Neg => a-b)
      (congrArg₂ (fun a b : Neg => a-b) hCr hRotG) hDG).trans
        ((hVector _ _ _ _ _).trans
          (congrArg (fun z : Neg => (RotL i j (CL i j (Sh q y r u))+DN i j (J (Sh q y r u)))-z)
            ((Sl q y r).map_add _ _).symm))
  have hLowPoint : Vl p (Sh q y r u) = ∑ i : Fin 3, ∑ j : Fin 3,
      (RotL i j (CL i j (Sh q y r u))+DN i j (J (Sh q y r u))) := by
    simpa only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply,RotL,CL,DN,J,ML,MN] using
      congrArg (fun A : Half →L[ℝ] Neg => A (Sh q y r u))
        (referenceGaugeTangentReciprocalSkewFamily_rotation_left
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room p)
  have hHighPoint : Vh p u = ∑ i : Fin 3, ∑ j : Fin 3,
      (RotH i j (CH i j u)+I (DH i j u)) := by
    simpa only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply,RotH,CH,DH,I,MH] using
      congrArg (fun A : Hi →L[ℝ] Half => A u)
        (referenceGaugeTangentReciprocalHighSkewFamily_rotation_left
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room p)
  have hTerms := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hTerm i j))
  have hExpand : referenceRadialTangentSecondCommutator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r (I u) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ((Cr i j (CL i j (I u))-RotL i j (G (CJ 3 i j p) (I u)))-J (G (DJ 3 i j p) (I u))) := by
    simp only [referenceRadialTangentSecondCommutator,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,Cr,CL,RotL,G,p,J,ML]
  have hSum : (∑ i : Fin 3, ∑ j : Fin 3,
      ((RotL i j (CL i j (Sh q y r u))+DN i j (J (Sh q y r u)))-
        Sl q y r (RotH i j (CH i j u)+I (DH i j u)))) =
      (∑ i : Fin 3, ∑ j : Fin 3, (RotL i j (CL i j (Sh q y r u))+DN i j (J (Sh q y r u)))) -
        Sl q y r (∑ i : Fin 3, ∑ j : Fin 3, (RotH i j (CH i j u)+I (DH i j u))) := by
    simp only [Finset.sum_sub_distrib,map_sum]
  exact hExpand.trans (hTerms.trans (hSum.trans
    (congrArg₂ (fun a b : Neg => a-b) hLowPoint.symm (congrArg (Sl q y r) hHighPoint.symm))))

def referenceRadialAdjointSharpSecondCommutator (q : ℝ) (y : R3) (r : ℝ) : Half →L[ℝ] Neg :=
  referenceRadialTangentSecondCommutator
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r +
  referenceRadialDefectSecondCommutator
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r

lemma referenceRadialAdjointSharpSecondCommutator_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hRoom : (q,(y,r)) ∈ Room.parameterRoom)
    (hAgree : (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp (Dh (q,(y,r))) =
      (Dl (q,(y,r))).comp (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)))
    (u : Hi) :
    referenceRadialAdjointSharpSecondCommutator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) =
      (secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r) (Sh q y r u) -
      Sl q y r ((secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r) u) := by
  let p := (q,(y,r))
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Th := secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
  let Tl := secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
  have hHigh := referenceAdjointRadialSecondRemainder_sub_eq_highSkew_of_lower_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel Room
      q hq y hy r hSegment hRoom hAgree
  have hHighTyped : Th-Sh q y r = Vh p+I.comp (Dh p) := by
    change Th-Sh q y r = Vh p+I.comp (Dh p) at hHigh
    exact hHigh
  have hHighEval : Th u-Sh q y r u = Vh p u+I (Dh p u) := by
    have hPoint := congrArg (fun A : Hi →L[ℝ] Half => A u) hHighTyped
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply] using hPoint
  have hHighPoint : Sl q y r (Th u)-Sl q y r (Sh q y r u) =
      Sl q y r (Vh p u)+Sl q y r (I (Dh p u)) :=
    ((Sl q y r).map_sub _ _).symm.trans
      ((congrArg (Sl q y r) hHighEval).trans ((Sl q y r).map_add _ _))
  have hTranspose : Tl = sphereLowerDistributionalTranspose (Sl q y r) := by
    simpa only [Tl,referenceLowerRadialTraceSecondRemainder] using
      secondTaylorRemainder_referenceAdjointHalfRadial_eq_transpose
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment
  have hy2 : ‖y-y0‖ ≤ 2*ρ := by linarith [hData.1.2.1]
  have hLow := referenceLowerRadialTraceSecondRemainder_transpose_sub_eq_skew_add_half
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))) Room hKernel
      q hq y hy2 r hSegment hRoom
  have hLowTyped : sphereLowerDistributionalTranspose (Sl q y r)-Sl q y r =
      Vl p+J.comp (Dl p) := by
    simpa only [J,p] using hLow
  have hLowEval : sphereLowerDistributionalTranspose (Sl q y r) (Sh q y r u)-
      Sl q y r (Sh q y r u) = Vl p (Sh q y r u)+J (Dl p (Sh q y r u)) := by
    have hPoint := congrArg (fun A : Half →L[ℝ] Neg => A (Sh q y r u)) hLowTyped
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply] using hPoint
  have hLowPoint : Tl (Sh q y r u)-Sl q y r (Sh q y r u) =
      Vl p (Sh q y r u)+J (Dl p (Sh q y r u)) :=
    (congrArg (fun A : Half →L[ℝ] Neg => A (Sh q y r u)-Sl q y r (Sh q y r u)) hTranspose).trans hLowEval
  have hVector {E : Type 0} [AddCommGroup E] (a b c v d x y : E)
      (h₁ : a-b = v+d) (h₂ : c-b = x+y) : (v-x)+(d-y) = a-c := by
    have hArrange : (v-x)+(d-y) = (v+d)-(x+y) := by abel
    exact hArrange.trans ((congrArg₂ (fun e f : E => e-f) h₁.symm h₂.symm).trans (by abel))
  have hKV := referenceRadialTangentSecondCommutator_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hKernel q y r hSegment u
  have hKD := referenceRadialDefectSecondCommutator_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hKernel
      q hq y hy r hSegment hRoom hAgree u
  change referenceRadialTangentSecondCommutator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r (I u) +
    referenceRadialDefectSecondCommutator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r (I u) = _
  exact (congrArg₂ (fun a b : Neg => a+b) hKV hKD).trans
    (hVector _ _ _ _ _ _ _ hLowPoint hHighPoint)

theorem exists_reference_commonRadius_radialAdjointSharpSecondCommutator_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ d →
        ∀ u : Hi,
          referenceRadialAdjointSharpSecondCommutator
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r
            (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) =
          (secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r) (Sh q y r u) -
          Sl q y r ((secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r) u) := by
  obtain ⟨d,hd,hdρ,hRoom⟩ := exists_reference_commonRadius_high_defect_lower_graph_segment
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg Room
  refine ⟨d,hd,hdρ,?_⟩
  intro q hq y hy r hr u
  have hPoint := hRoom q hq y hy r hr
  exact referenceRadialAdjointSharpSecondCommutator_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel
      q hq y hy r hPoint.1 hPoint.2.1 hPoint.2.2 u

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialSkewProductCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRadialSkewProductCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialSkewProductCoefficient_support
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialSkewDerivativeCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRadialSkewDerivativeCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialSkewDerivativeCoefficient_support
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialSkewDerivativeCoefficient_eq_rotation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialSkewProductJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialSkewDerivativeJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceRadialSkewProductJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceRadialSkewDerivativeJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalizedAdjointNegativeDefectFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalizedAdjointNegativeDefectFamily_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDefectSecondCommutator
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDefectSecondCommutator_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentReciprocalHighSkewFamily_rotation_left
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentReciprocalSkewFamily_rotation_left
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialTangentSecondCommutator
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialTangentSecondCommutator_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialAdjointSharpSecondCommutator
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialAdjointSharpSecondCommutator_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_radialAdjointSharpSecondCommutator_graph

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeThreeHalfCoefficientMulL_smul_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeThreeHalfCoefficientMulL_add_products_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSmoothMultiplierSecondRemainder_lower_graph
