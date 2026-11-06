import Calderon.ActualDilatedNativeSolutionLimit
import Calderon.PositiveCoefficientEnlargedHarmonicRestriction
import Calderon.PositiveCoefficientNativeHalfTrace
import Calderon.SmoothHalfTraceDense

/-! EXPANSION.json precedes the genuine enlarged-solver trace density assembly.
The physical same-chart trace/gauge identification is still separate. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ENNReal ContDiff Topology Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeFullSharpHalfTrace NativeSmoothSharpTraceCompletion

def positiveCoefficientHarmonicNeighborhoodHalfTraceSet
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (A : MatrixField) :
    Set (SphereSobolev (1/2 : ℝ)) :=
  {u | ∃ w : SmoothData, ∃ O : Set R3, IsOpen O ∧ closedBall (0 : R3) 1 ⊆ O ∧
    O ⊆ ball (0 : R3) 2 ∧
    (∀ x ∈ O, ConnectionError.coordinateFluxDivergence
      (fun y => MetricOperator.matrixOperatorMap (A y) (gradient w.1 y : R3)) x = 0) ∧
    u = smoothHalfTrace hF hO hD τ0 w}

theorem smoothHalfTrace_mem_closure_positiveCoefficientHarmonicNeighborhood
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (f : SmoothData) :
    smoothHalfTrace hF hO hD τ0 f ∈ closure
      (positiveCoefficientHarmonicNeighborhoodHalfTraceSet hF hO hD τ0 A) := by
  let U : ℝ → BallH1 := fun a => positiveCoefficientDirichletSolution (fun x => A (a⁻¹ • x))
    (hA.comp (a⁻¹ • ContinuousLinearMap.id ℝ R3).contDiff) (fun x => hPos (a⁻¹ • x)) f
  let u : BallH1 := positiveCoefficientDirichletSolution A hA hPos f
  have hInv : Tendsto (fun a : ℝ => a⁻¹) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [inv_one] using
      (continuousAt_inv₀ (show (1 : ℝ) ≠ 0 by norm_num)).tendsto.mono_left nhdsWithin_le_nhds
  have hU : Tendsto U (𝓝[<] (1 : ℝ)) (𝓝 u) :=
    (tendsto_positiveCoefficientDirichletSolution_dilation_one_scalar A hA hPos f).comp hInv
  have hDilation : Tendsto (fun a : ℝ => nativeH1InwardDilation a (U a))
      (𝓝[<] (1 : ℝ)) (𝓝 u) := tendsto_nativeH1InwardDilation_variable_one U u hU
  have hTrace : Tendsto (fun a : ℝ => nativeHalfTraceL hF hO hD τ0
      (nativeH1InwardDilation a (U a))) (𝓝[<] (1 : ℝ))
      (𝓝 (smoothHalfTrace hF hO hD τ0 f)) := by
    have h := (nativeHalfTraceL hF hO hD τ0).continuous.continuousAt.tendsto.comp hDilation
    simpa only [u,nativeHalfTraceL_positiveCoefficientDirichletSolution,Function.comp_def] using h
  have hMember : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ),
      nativeHalfTraceL hF hO hD τ0 (nativeH1InwardDilation a (U a)) ∈
        positiveCoefficientHarmonicNeighborhoodHalfTraceSet hF hO hD τ0 A := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Ioi_mem_nhds (show (1/2 : ℝ) < 1 by norm_num)), self_mem_nhdsWithin] with a haHalf ha1
    have haLt : a < 1 := Set.mem_Iio.mp ha1
    have ha0 : 0 < a := lt_trans (by norm_num) haHalf
    have hR : 1 < a⁻¹ := by
      rw [← one_div]
      exact (lt_div_iff₀ ha0).mpr (by simpa only [one_mul] using haLt)
    have hR2 : a⁻¹ ≤ 2 := by
      rw [← one_div]
      exact (div_le_iff₀ ha0).mpr (by linarith)
    obtain ⟨b',w,O,_,_,_,_,hOpen,hClosed,_,hDouble,hPDE,hNative⟩ :=
      exists_positiveCoefficient_enlarged_harmonic_restriction
        hcalc hreg τ0 A hA hPos f a⁻¹ hR hR2
    have hNative' : nativeH1InwardDilation a (U a) = smoothSobolev w := by
      simpa only [U,inv_inv] using hNative
    have hTraceEq : nativeHalfTraceL hF hO hD τ0 (nativeH1InwardDilation a (U a)) =
        smoothHalfTrace hF hO hD τ0 w :=
      (congrArg (nativeHalfTraceL hF hO hD τ0) hNative').trans
        (nativeHalfTraceL_smoothSobolev hF hO hD τ0 w)
    exact ⟨w,O,hOpen,hClosed,hDouble,hPDE,hTraceEq⟩
  exact isClosed_closure.mem_of_tendsto hTrace (hMember.mono (fun _ h => subset_closure h))

theorem dense_positiveCoefficientHarmonicNeighborhoodHalfTraceSet
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) :
    Dense (positiveCoefficientHarmonicNeighborhoodHalfTraceSet hF hO hD τ0 A) := by
  have hRange : range (smoothHalfTrace hF hO hD τ0) ⊆ closure
      (positiveCoefficientHarmonicNeighborhoodHalfTraceSet hF hO hD τ0 A) := by
    rintro _ ⟨f,rfl⟩
    exact smoothHalfTrace_mem_closure_positiveCoefficientHarmonicNeighborhood
      hcalc hreg hF hO hD τ0 A hA hPos f
  intro u
  exact closure_minimal hRange isClosed_closure (denseRange_smoothHalfTrace hF hO hD τ0 u)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.positiveCoefficientHarmonicNeighborhoodHalfTraceSet
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothHalfTrace_mem_closure_positiveCoefficientHarmonicNeighborhood
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.dense_positiveCoefficientHarmonicNeighborhoodHalfTraceSet
