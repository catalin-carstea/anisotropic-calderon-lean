import Calderon.ActualDensityScalarCutoff
import Calderon.ActualCutoffAllDerivativeRoom
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ConformalDepth RadiusProfile ReferenceDensityBounds ActualNormalizedSecondMetricDrift
open ConformalDepth
attribute [local irreducible] referenceHighDensityFirstAction referenceLowerDensityFirstAction
  referenceHighHorizontalAction referenceLowerHorizontalAction
  referenceMetricGramFrame referenceFrameConnectionCoefficient
  referenceHighHorizontalAngularL referenceLowerHorizontalAngularL
  referenceHighAdjointMovingBoundaryActionFamily referenceLowerAdjointMovingBoundaryActionFamily
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

theorem referenceFrameScalarDerivative_eq_zero_of_notMem_cutoff_derivative_support
    (q : ℝ) (chi : R3 → ℝ) (y : R3)
    (hy : y ∉ tsupport (fderiv ℝ chi)) (i : Fin 3) :
    referenceFrameScalarDerivative g L q chi y i = 0 := by
  have hz : fderiv ℝ chi y = 0 := image_eq_zero_of_notMem_tsupport hy
  simp only [referenceFrameScalarDerivative,hz,zero_apply]

theorem referenceFrameScalarHessian_eq_zero_of_notMem_cutoff_derivative_support
    (q : ℝ) (chi : R3 → ℝ) (y : R3)
    (hy : y ∉ tsupport (fderiv ℝ chi)) (i j : Fin 3) :
    referenceFrameScalarHessian g L q chi y i j = 0 := by
  have hz : fderiv ℝ chi =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hy
  have hj : (fun x => referenceFrameScalarDerivative g L q chi x j) =ᶠ[𝓝 y]
      (fun _ => (0 : ℝ)) := hz.mono fun x hx => by
    simp only [referenceFrameScalarDerivative,hx,Pi.zero_apply,zero_apply]
  have hd : fderiv ℝ (fun x => referenceFrameScalarDerivative g L q chi x j) y = 0 := by
    exact (hj.fderiv_eq (𝕜 := ℝ)).trans (fderiv_const_apply (0 : ℝ))
  have hi (k : Fin 3) : referenceFrameScalarDerivative g L q chi y k = 0 :=
    referenceFrameScalarDerivative_eq_zero_of_notMem_cutoff_derivative_support g L q chi y hy k
  simp only [referenceFrameScalarHessian,hd,hi,zero_apply,
    mul_zero,Finset.sum_const_zero,sub_zero]

theorem referenceDensityScalarCutoffCommutator_eq_zero_of_notMem_derivative_support
    (g2 : MatrixField) (q : ℝ) (R chi : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3)
    (hy : y ∉ tsupport (fderiv ℝ chi)) :
    referenceDensityScalarCutoffCommutator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 q R chi u y = 0 := by
  have hFirst (i : Fin 3) : referenceFrameScalarDerivative g L q chi y i = 0 :=
    referenceFrameScalarDerivative_eq_zero_of_notMem_cutoff_derivative_support g L q chi y hy i
  have hSecond (i j : Fin 3) : referenceFrameScalarHessian g L q chi y i j = 0 :=
    referenceFrameScalarHessian_eq_zero_of_notMem_cutoff_derivative_support g L q chi y hy i j
  simp only [referenceDensityScalarCutoffCommutator,hFirst,hSecond,zero_smul,
    add_zero,Finset.sum_const_zero,smul_zero]

theorem tsupport_referenceDensityScalarCutoffCommutator_subset
    (g2 : MatrixField) (q : ℝ) (R chi : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) :
    tsupport (referenceDensityScalarCutoffCommutator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 q R chi u) ⊆ tsupport (fderiv ℝ chi) := by
  apply closure_minimal _ (isClosed_tsupport (fderiv ℝ chi))
  intro y hy
  by_contra hn
  exact hy (referenceDensityScalarCutoffCommutator_eq_zero_of_notMem_derivative_support
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R chi u y hn)

theorem exists_actual_cutoff_commutator_source_room
    (tb : ℝ) (chi : R3 → ℝ) (hCompact : HasCompactSupport chi)
    (hSupport : tsupport chi ⊆ interior MixedKernelConstructionTask.cylinder)
    (hDeriv : tsupport (fderiv ℝ chi) ⊆
      {z : R3 | z 2 < -(1/4 : ℝ)} ∪ {z : R3 | tb < referenceDepth L z}) :
    ∃ U : Set R3, IsOpen U ∧
      closure U ⊆ interior MixedKernelConstructionTask.cylinder ∩
        ({z : R3 | z 2 < -(1/4 : ℝ)} ∪ {z : R3 | tb < referenceDepth L z}) ∧
      (∀ n : ℕ, tsupport (iteratedFDeriv ℝ (n+1) chi) ⊆ U) ∧
      ∀ (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
        (u : R3 → SphereSobolev (3/2 : ℝ)),
        tsupport (referenceDensityScalarCutoffCommutator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          g2 q R chi u) ⊆ U := by
  obtain ⟨U,hU,hEU,hClosure,hJets⟩ :=
    MixedKernelConstructionTask.exists_actual_cutoff_all_derivative_source_room
      L tb chi hCompact hSupport hDeriv
  refine ⟨U,hU,hClosure,hJets,?_⟩
  intro g2 q R u
  exact (tsupport_referenceDensityScalarCutoffCommutator_subset
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R chi u).trans hEU

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
