import Calderon.ActualReferenceSharpMidpointRadialTrace
import Calderon.ActualNativeHarmonicTraceCoreTaylor
import Calderon.RadialDerivativeLinkedEvaluation

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceRadialEndpointInvertibleLocus_zero_mem
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    (q,(y,0)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
  obtain ⟨δ,hδ,hδρ,hRoom⟩ :=
    exists_reference_commonRadius_subset_radialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  apply hRoom
  refine ⟨hq,?_,?_,?_⟩
  · simpa only [mem_closedBall,dist_eq_norm] using hy
  · linarith
  · exact hδ.le

theorem radialFirstDerivative_referenceSharpMidpointRadialTrace_on_high_data
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (q : ℝ) (y : R3)
    (hp : (q,(y,0)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (f : SphereSobolev (3/2 : ℝ)) :
    radialFirstDerivative (fun p : R3 × ℝ => referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (y,0)
      (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) f) =
    sphereSobolevZeroEquiv hO hD
      (radialFirstDerivative (referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q) (y,0) (harmonicLiftCompletion hF f)) := by
  have hS := isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hSharp : ContDiffAt ℝ ∞ (fun p : R3 × ℝ => referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (y,0) :=
    (contDiffAt_referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) hp).comp
      (y,0) (contDiffAt_const.prodMk contDiffAt_id)
  have hCoarse := contDiffAt_referenceNativeRadialTraceOperatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 q (y,0) hp.1
  have hNear : ∀ᶠ r : ℝ in 𝓝 0, (q,(y,r)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)).eventually
      (hS.mem_nhds hp)
  have hEq : (fun r : ℝ => referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))
        (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) f)) =ᶠ[𝓝 0]
      (fun r : ℝ => sphereSobolevZeroEquiv hO hD
        (referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q (y,r) (harmonicLiftCompletion hF f))) := by
    filter_upwards [hNear] with r hr
    exact referenceSharpMidpointRadialTraceFamily_eq_native_radial_on_high_data
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) hr f
  have ht := radialFirstDerivative_eq_of_linked_evaluation
    (P := R3) (E := SphereSobolev 1) (X := BallSobolev 2)
    (V := SphereL2) (W := SphereSobolev 0)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at ht
  exact ht (fun p : R3 × ℝ => referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q)
    (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap y
    (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) f) (harmonicLiftCompletion hF f)
    (hSharp.differentiableAt (by simp)) (hCoarse.differentiableAt (by simp)) hEq

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
