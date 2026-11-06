import Calderon.ActualFiniteHighFullAdjointFirstSection

/-! Support of the explicit uncompressed Y section. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteHighPrimalMovingBoundaryFamily
  referenceFiniteHighHorizontalSection referenceFiniteHighFullAdjointFirstSection
  sphereSobolevPartialSumL referenceMetricGramFrame referenceFrameConnectionCoefficient

lemma tsupport_referenceFiniteHighFullAdjointFirstSection_subset
    (n : ℕ) (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (i : Fin 3) :
    tsupport (fun y => referenceFiniteHighFullAdjointFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u y i) ⊆ tsupport u := by
  classical
  change closure (Function.support (fun y : R3 => referenceFiniteHighFullAdjointFirstSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u y i)) ⊆ tsupport u
  apply closure_minimal ?_ (isClosed_tsupport u)
  intro y hy
  by_contra hyu
  have hU : u y = 0 := image_eq_zero_of_notMem_tsupport hyu
  have hDerivative : fderiv ℝ u y = 0 := fderiv_of_notMem_tsupport ℝ hyu
  have hHorizontal : referenceFiniteHighHorizontalSection
      g L hcalc hF hO hD τ0 n q u y i = 0 := by
    simp only [referenceFiniteHighHorizontalSection,hDerivative,ContinuousLinearMap.zero_apply,
      hU,map_zero,smul_zero,Finset.sum_const_zero,zero_add]
  have hValue : referenceFiniteHighFullAdjointFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u y i = 0 := by
    simp only [referenceFiniteHighFullAdjointFirstSection,hHorizontal,hU,map_zero,
      neg_zero,zero_add,smul_zero,sub_zero]
  change referenceFiniteHighFullAdjointFirstSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u y i ≠ 0 at hy
  exact hy hValue

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tsupport_referenceFiniteHighFullAdjointFirstSection_subset
