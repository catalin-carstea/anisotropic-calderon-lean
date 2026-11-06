import Calderon.ActualPiCommonSupportFamily
import Calderon.ActualPiLowerValueIdentification

/-! Exact original Pi operator germs. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator NormalCoordinatesFrame
  NativeCoefficientBoundaryMultiplier NativeThreeHalfCoefficientMultiplier
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily
  g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily
  g hg L y0 Φ B ε C ρ H a w hData
local notation "MH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "ML" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "MN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0

def referencePiThreeHalfMultiplier (i : Fin 3) (t : Tpar) : Hi →L[ℝ] Hi :=
  sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1) +
  t.1.2.2^2 • (∑ j : Fin 3,
    (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)).comp (MH (NJ3 i j t.1))) +
  t.2 (conformalReferenceGramFrameOperatorJoint g L (t.1.1,t.1.2.1) (coordinateVector i)) •
    ContinuousLinearMap.id ℝ Hi

def referencePiHalfMultiplier (i : Fin 3) (t : Tpar) : Half →L[ℝ] Half :=
  sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1) +
  t.1.2.2^2 • (∑ j : Fin 3,
    (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)).comp (ML (NJ2 i j t.1))) +
  t.2 (conformalReferenceGramFrameOperatorJoint g L (t.1.1,t.1.2.1) (coordinateVector i)) •
    ContinuousLinearMap.id ℝ Half

def referencePiNegativeHalfMultiplier (i : Fin 3) (t : Tpar) : Neg →L[ℝ] Neg :=
  sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single i 1) +
  t.1.2.2^2 • (∑ j : Fin 3,
    (sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single j 1)).comp (MN (NJ2 i j t.1))) +
  t.2 (conformalReferenceGramFrameOperatorJoint g L (t.1.1,t.1.2.1) (coordinateVector i)) •
    ContinuousLinearMap.id ℝ Neg

local notation "PiH" => referencePiThreeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL referencePiThreeHalfMultiplier referencePiHalfMultiplier
  referencePiNegativeHalfMultiplier

lemma nativeCoefficientMultipliers_eq_referencePi_of_genuine_value
    (i : Fin 3) (t : Tpar) (Q : SmoothCoefficientJets 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (t.1.1,(t.1.2,x.val))).IsInvertible)
    (hValue : ∀ x : UnitSphere, coefficientValue 3 Q x.val =
      referencePiScalarCoefficient g L Φ i (t,x.val)) :
    MH Q = PiH i t ∧ ML (smoothMultiplierLowerJets Q) = PiL i t ∧
      MN (smoothMultiplierLowerJets Q) = PiN i t := by
  have hNValue (j : Fin 3) : coefficientValue 3 (NJ3 i j t.1) = coefficientValue 2 (NJ2 i j t.1) := by
    unfold referenceJacobiBoundaryThreeHalfCoefficientFamily
    exact coefficientValue_compactCoefficient 3 _ _ _
  have hNSphere (j : Fin 3) (x : UnitSphere) :
      smoothSphereValue (nativeH2CoefficientSmoothData (NJ3 i j t.1)) x =
        referenceFramedJacobiVelocityRemainder g L Φ i (t.1.1,(t.1.2,x.val)) j := by
    change coefficientValue 3 (NJ3 i j t.1) x.val = _
    rw [hNValue j]
    change smoothSphereValue (coefficientSmoothData (NJ2 i j t.1)) x = _
    rw [referenceJacobiBoundaryCoefficientFamily_eq g hg L y0 Φ B ε C ρ H a w hData i j t.1 hInv,
      smoothSphereValue_referenceJacobiBoundaryCoefficientJets]
    rfl
  have hSphere : smoothSphereValue (nativeH2CoefficientSmoothData Q) =
      sphereCoordinate i + t.1.2.2^2 • (∑ j : Fin 3,
        sphereCoordinate j * smoothSphereValue (nativeH2CoefficientSmoothData (NJ3 i j t.1))) +
      t.2 (conformalReferenceGramFrameOperatorJoint g L (t.1.1,t.1.2.1) (coordinateVector i)) •
        (1 : C(UnitSphere,ℝ)) := by
    apply ContinuousMap.ext
    intro x
    change coefficientValue 3 Q x.val = _
    rw [hValue x]
    simp only [referencePiScalarCoefficient,ContinuousMap.add_apply,ContinuousMap.smul_apply,
      ContinuousMap.sum_apply,ContinuousMap.mul_apply,ContinuousMap.one_apply,smul_eq_mul,mul_one,sphereCoordinate,hNSphere]
    rfl
  have hSphereLower : smoothSphereValue (coefficientSmoothData (smoothMultiplierLowerJets Q)) =
      sphereCoordinate i + t.1.2.2^2 • (∑ j : Fin 3,
        sphereCoordinate j * smoothSphereValue (coefficientSmoothData (NJ2 i j t.1))) +
      t.2 (conformalReferenceGramFrameOperatorJoint g L (t.1.1,t.1.2.1) (coordinateVector i)) •
        (1 : C(UnitSphere,ℝ)) := by
    apply ContinuousMap.ext
    intro x
    have hh := congrArg (fun f : C(UnitSphere,ℝ) => f x) hSphere
    simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,ContinuousMap.sum_apply,
      ContinuousMap.mul_apply,ContinuousMap.one_apply,smul_eq_mul,mul_one,sphereCoordinate] at hh ⊢
    change coefficientValue 3 Q x.val =
      x.val i + t.1.2.2^2 * (∑ j : Fin 3, x.val j * coefficientValue 3 (NJ3 i j t.1) x.val) +
        t.2 (conformalReferenceGramFrameOperatorJoint g L (t.1.1,t.1.2.1) (coordinateVector i)) at hh
    change coefficientValue 2 (smoothMultiplierLowerJets Q) x.val =
      x.val i + t.1.2.2^2 * (∑ j : Fin 3, x.val j * coefficientValue 2 (NJ2 i j t.1) x.val) +
        t.2 (conformalReferenceGramFrameOperatorJoint g L (t.1.1,t.1.2.1) (coordinateVector i))
    rw [coefficientValue_smoothMultiplierLowerJets]
    simpa only [hNValue] using hh
  refine ⟨?_,?_,?_⟩
  · simpa only [referencePiThreeHalfMultiplier] using
      nativeThreeHalfCoefficientMulL_eq_originalPi_of_sphereValue hcalc hF hO hD τ0 Q
        (fun j => NJ3 i j t.1) i (t.1.2.2^2)
        (t.2 (conformalReferenceGramFrameOperatorJoint g L (t.1.1,t.1.2.1) (coordinateVector i))) hSphere
  · simpa only [referencePiHalfMultiplier] using
      nativeHalfCoefficientMulL_eq_originalPi_of_sphereValue hcalc hF hO hD τ0 Q (smoothMultiplierLowerJets Q)
        (fun j => NJ3 i j t.1) (fun j => NJ2 i j t.1)
        (coefficientValue_smoothMultiplierLowerJets Q).symm hNValue i (t.1.2.2^2)
        (t.2 (conformalReferenceGramFrameOperatorJoint g L (t.1.1,t.1.2.1) (coordinateVector i))) hSphere
  · simpa only [referencePiNegativeHalfMultiplier] using
      nativeNegativeHalfCoefficientMulL_eq_originalPi_of_sphereValue hcalc hF hO hD τ0
        (smoothMultiplierLowerJets Q) (fun j => NJ2 i j t.1) i (t.1.2.2^2)
        (t.2 (conformalReferenceGramFrameOperatorJoint g L (t.1.1,t.1.2.1) (coordinateVector i))) hSphereLower

theorem exists_referencePi_commonSupport_native_operator_germs
    (hreg : FixedDirichletRegularity) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
    ∃ (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ i, ContDiff ℝ ∞ (m i))
      (Km : Set R3) (hKm : IsCompact Km)
      (hmz : ∀ i t x, x ∉ Km → m i (t,x) = 0),
      ∀ i : Fin 3, ∀ t ∈
        (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)) ×ˢ
          closedBall (0 : R3 →L[ℝ] ℝ) 1,
        ∀ᶠ z in 𝓝 t,
          let Q := commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z
          MH Q = PiH i z ∧ ML (smoothMultiplierLowerJets Q) = PiL i z ∧
            MN (smoothMultiplierLowerJets Q) = PiN i z := by
  have hFull := exists_referencePi_commonSupport_coefficient_germs
    g L y0 Φ B ε C ρ H a w hData hg hcalc hreg hF hO hD τ0
  rcases hFull with ⟨d,hd,hdρ,m,hm,Km,hKm,hmz,hG⟩
  refine ⟨d,hd,hdρ,m,hm,Km,hKm,hmz,?_⟩
  intro i t ht
  filter_upwards [hG i t ht] with z hz
  exact nativeCoefficientMultipliers_eq_referencePi_of_genuine_value
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i z _
    (fun x => (hz x).2) (fun x => (hz x).1)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
