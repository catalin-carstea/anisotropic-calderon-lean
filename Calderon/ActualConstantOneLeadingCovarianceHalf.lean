import Calderon.ActualConstantOneFirstAngularLift
import Calderon.ActualNativeLeadingCovariantRadiusCancellation
import Calderon.ActualConstantModeHorizontalIdentities
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
private lemma map_covariant_expression
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : V →L[ℝ] W) (h d : V) (c : ℝ) (a : Fin 3 → V) (gamma : Fin 3 → ℝ) :
    T (h+c • d-∑ k : Fin 3, gamma k • a k) =
      T h+c • T d-∑ k : Fin 3, gamma k • T (a k) := by
  simp only [map_sub,map_add,map_smul,map_sum]

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] harmonicSphereSubspace referenceHighHorizontalAction referenceLowerHorizontalAction
  sphereSobolevInclusionL sphereSobolevShiftedDegreeL sphereSobolevConstantOne
  constantOneFirstRaisingThreeHalf referenceMetricGramFrame referenceFrameConnectionCoefficient

include hData hg hcalc hO hD τ0 in
theorem referenceConstantOneLeadingRadiusAngularAction_covariant_half_cancellation
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (i j : Fin 3) (hr : R y ≠ 0) :
    let V : Fin 3 → R3 → SphereSobolev (3/2:ℝ) := fun k z => (R z)⁻¹ • constantOneFirstRaisingThreeHalf hF k
    referenceHighHorizontalAction g L q (V j) y i +
      referenceRadiusHorizontalLogDerivative g L q R y i • sphereSobolevShiftedDegreeL (3/2:ℝ) (V j y) -
      (∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j •
        sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V k y)) = 0 := by
  intro V
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let W : Fin 3 → R3 → SphereSobolev (1/2:ℝ) := fun k z => (R z)⁻¹ •
    sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2:ℝ) k (sphereSobolevConstantOne (3/2:ℝ))
  have hValue (k : Fin 3) (z : R3) : I (V k z) = W k z := by
    exact (I.map_smul (R z)⁻¹ (constantOneFirstRaisingThreeHalf hF k)).trans
      (congrArg (fun a => (R z)⁻¹ • a)
        (sphereSobolevInclusionL_constantOneFirstRaisingThreeHalf hF hO hD k))
  have hField (k : Fin 3) : (fun z => I (V k z)) = W k := funext (hValue k)
  have hDiff : DifferentiableAt ℝ (V j) y :=
    ((hR.differentiable (by simp) y).inv hr).smul_const (constantOneFirstRaisingThreeHalf hF j)
  have hHoriz := referenceHorizontalAction_high_lower_compatibility g L q (V j) y i hDiff
  have hHoriz' : J (referenceHighHorizontalAction g L q (V j) y i) =
      referenceLowerHorizontalAction g L q (W j) y i :=
    hHoriz.trans (congrArg (fun F => referenceLowerHorizontalAction g L q F y i) (hField j))
  have hDegree : J (sphereSobolevShiftedDegreeL (3/2:ℝ) (V j y)) =
      sphereSobolevShiftedDegreeL (1/2:ℝ) (W j y) :=
    (DFunLike.congr_fun sphereSobolevShiftedDegree_high_half_compatibility (V j y)).trans
      (congrArg (sphereSobolevShiftedDegreeL (1/2:ℝ)) (hValue j y))
  have hNative := referenceLeadingRadiusAngularAction_covariant_cancellation
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR y hy i j hr
      (fun _ => sphereSobolevConstantOne (3/2:ℝ)) (differentiableAt_const _)
  have hZero : referenceLowerHorizontalAction g L q (W j) y i +
      referenceRadiusHorizontalLogDerivative g L q R y i • sphereSobolevShiftedDegreeL (1/2:ℝ) (W j y) -
      (∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j • J (W k y)) = 0 := by
    simpa only [W,referenceHighHorizontalAction_constantOne,sphereSobolevShiftedDegreeL_constantOne,
      smul_zero,zero_add,map_zero] using hNative
  have hConnection : (∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j • J (I (V k y))) =
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j • J (W k y) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact congrArg (fun a => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j • J a) (hValue k y)
  have hLinear := map_covariant_expression J
    (referenceHighHorizontalAction g L q (V j) y i)
    (sphereSobolevShiftedDegreeL (3/2:ℝ) (V j y))
    (referenceRadiusHorizontalLogDerivative g L q R y i)
    (fun k : Fin 3 => I (V k y))
    (fun k : Fin 3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j)
  have hHead := congrArg₂ (fun a b : SphereSobolev (-(1/2:ℝ)) =>
    a+referenceRadiusHorizontalLogDerivative g L q R y i • b) hHoriz' hDegree
  have hProjected := congrArg₂ (fun a b : SphereSobolev (-(1/2:ℝ)) => a-b) hHead hConnection
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  exact (hLinear.trans (hProjected.trans hZero)).trans J.map_zero.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
