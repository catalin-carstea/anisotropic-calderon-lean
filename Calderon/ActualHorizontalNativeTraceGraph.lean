import Calderon.NativeSmoothBallSobolevFamily
import Calderon.NativeH2ThreeHalfValueTrace
import Calderon.ActualHorizontalSobolevConnection

/-! The native horizontal trace graph, by coefficients. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeH2ThreeHalfValueTrace SmoothMetricFrame
  MovingFrameConnection SmoothSphereFields SmoothMovingFrameFields
  AmbientReferenceCovariantCore CovariantHarmonicEnergy SpectralCoreRegularity

def nativeThreeHalfSmoothSection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (y : R3) : SphereSobolev (3/2 : ℝ) :=
  nativeThreeHalfValueTraceL hcalc hF hO hD τ0
    (smoothBallSobolev 2
      ⟨fun z => G (y,z), SpatialJetFields.contDiff_spatial_slice G hG y⟩)

theorem sphereSobolevCoefficientL_nativeThreeHalfSmoothSection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (y : R3) (k : ℕ) :
    sphereSobolevCoefficientL (3/2 : ℝ) k
      (nativeThreeHalfSmoothSection hcalc hF hO hD τ0 G hG y) =
    sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG y) := by
  unfold nativeThreeHalfSmoothSection
  rw [sphereSobolevCoefficientL_nativeThreeHalfValueTraceL,
    firstOrder_smoothBallSobolev, τ0.valueTrace_smooth]
  rfl

theorem sphereSobolevCoefficientL_referenceHighHorizontalAction
    (g : MatrixField) (L q : ℝ) (V : R3 → SphereSobolev (3/2 : ℝ))
    (y : R3) (i : Fin 3) (k : ℕ) (hV : DifferentiableAt ℝ V y) :
    sphereSobolevCoefficientL (1/2 : ℝ) k (referenceHighHorizontalAction g L q V y i) =
    referenceHarmonicCovariantDerivative g L q k
      (fun z => sphereSobolevCoefficientL (3/2 : ℝ) k (V z)) y
      (referenceMetricGramFrame g L (q,y) i) := by
  let T := sphereSobolevCoefficientL (3/2 : ℝ) k
  have hDerivative : fderiv ℝ (fun z => T (V z)) y = T.comp (fderiv ℝ V y) :=
    (T.hasFDerivAt.comp y hV.hasFDerivAt).fderiv
  have hRotation (a b : Fin 3) : sphereSobolevCoefficientL (1/2 : ℝ) k
      (sphereSobolevRotationL (3/2 : ℝ) a b (V y)) =
      SmoothSphereRotationProjection.harmonicSphereRotation k a b (T (V y)) := by
    have hs : (3/2 : ℝ)-1 = 1/2 := by norm_num
    simpa only [T, sphereSobolevCoefficientL, hs] using
      sphereSobolevCoefficientL_rotation (3/2 : ℝ) a b k (V y)
  unfold referenceHighHorizontalAction referenceHighHorizontalAngularL
    referenceHarmonicCovariantDerivative
  simp only [map_add, map_smul, map_sum, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, sphereSobolevCoefficientL_inclusion, hRotation]
  change T (fderiv ℝ V y (referenceMetricGramFrame g L (q,y) i)) + _ =
    fderiv ℝ (fun z => T (V z)) y (referenceMetricGramFrame g L (q,y) i) + _
  rw [hDerivative, ContinuousLinearMap.comp_apply]

theorem referenceHighHorizontalAction_nativeThreeHalfSmoothSection_coarse
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (y : R3) (i : Fin 3) :
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (referenceHighHorizontalAction g L q
        (nativeThreeHalfSmoothSection hcalc hF hO hD τ0 G hG) y i) =
    sphereSobolevZeroEquiv hO hD
      (ambientSphereL2
        (ambientFrameHorizontal
          (fun z => referenceFrameConnectionCoefficient g L q z
            (referenceMetricGramFrame g L (q,z) i))
          (fun z => referenceMetricGramFrame g L (q,z) i) G)
        (contDiff_ambientFrameHorizontal _
          (fun a b => contDiff_referenceFrameConnectionCoefficient_field g hg L q _
            (contDiff_referenceMetricGramFrame_slice g hg L q i) a b)
          _ (contDiff_referenceMetricGramFrame_slice g hg L q i) G hG) y) := by
  have hSmooth : ContDiff ℝ ∞ (nativeThreeHalfSmoothSection hcalc hF hO hD τ0 G hG) :=
    (nativeThreeHalfValueTraceL hcalc hF hO hD τ0).contDiff.comp
      (contDiff_smoothBallSobolev_of_joint hcalc 2 G hG)
  apply sphereSobolev_ext 0
  intro k
  rw [sphereSobolevCoefficientL_inclusion, sphereSobolevCoefficientL_zeroEquiv]
  rw [sphereSobolevCoefficientL_referenceHighHorizontalAction g L q _ y i k
    (hSmooth.differentiable (by simp) y)]
  have hCoefficients : (fun z => sphereSobolevCoefficientL (3/2 : ℝ) k
      (nativeThreeHalfSmoothSection hcalc hF hO hD τ0 G hG z)) =
      (fun z => sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG z)) := by
    funext z
    exact sphereSobolevCoefficientL_nativeThreeHalfSmoothSection hcalc hF hO hD τ0 G hG z k
  rw [hCoefficients]
  exact (sphereHarmonicCoordinate_referenceFrameHorizontal hO hD g hg L q k
    (fun z => referenceMetricGramFrame g L (q,z) i)
    (contDiff_referenceMetricGramFrame_slice g hg L q i) G hG y).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeThreeHalfSmoothSection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevCoefficientL_nativeThreeHalfSmoothSection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevCoefficientL_referenceHighHorizontalAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighHorizontalAction_nativeThreeHalfSmoothSection_coarse
