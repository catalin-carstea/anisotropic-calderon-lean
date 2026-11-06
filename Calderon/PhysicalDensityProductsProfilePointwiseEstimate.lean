import Calderon.PhysicalDensityProductsConcreteSectionsModular
import Calderon.ActualFiniteHarmonicModelHorizontalProfileComparison
import Calderon.PhysicalDensityProductsFiniteCoreProjection
import Calderon.PhysicalDensityProductsConcreteWeightedSums
import Calderon.PhysicalDensityProductsPredicateTransport
import Calderon.PhysicalDensityProductsOperatorSmoothness
import Calderon.SupportedOperatorSection
import Calderon.PhysicalDensityProductsProfileOpenRoom
import Calderon.PhysicalDensityProductsFiniteCorePairing
import Calderon.PhysicalDensityProductsNegativeGraph
import Calderon.SphereSobolevHalfToL2
import Calderon.WeightedIntegralCongruence
import Calderon.SupportedOperatorSectionsOfPairing
import Calderon.PhysicalDensityProductsWeightedSumsSmoothness
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Calderon.PhysicalDensityProductsProfileEnergyIntegrability

/-! Private scalar and actual pointwise profile estimate.
Upfront: /tmp/ProductsProfilePointwiseEstimate-v003/UPFRONT.md.
The full uniform d/C_P theorem and full conditional profile helper remain open.
-/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsProfilePointwise
open EnergyBridge ConnectionError SphereHarmonic SphereHilbertDecomposition NormalCoordinatesFrame
  ActualFiniteHarmonicCore SpectralCoreRegularity SpectralWeightedGraph
  ConformalDepth NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge
  ReferenceDensityBounds ActualFiniteHarmonicModel ReferenceWeightedApproximation
  SectionFiveErrorForms

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)

/-- The original exponent-nine algebra, with no division by a beta parameter. -/
theorem pow_nine_mul_sq_le_of_radius_beta_bound
    (r b b0 c eta u v energy : ℝ)
    (hr : 0 ≤ r) (hb : 0 ≤ b) (hb0 : 0 ≤ b0)
    (hc : 0 ≤ c) (heta : 0 ≤ eta) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hb0b : b0 ≤ b) (hsmall : r*b^2 ≤ eta)
    (hvbound : v ≤ c*r^2*u) (henergy : b*u^2 ≤ energy) :
    b0^9*v^2 ≤ c^2*eta^4*energy := by
  have hcu : 0 ≤ c*r^2*u := mul_nonneg (mul_nonneg hc (sq_nonneg r)) hu
  have hvsq : v^2 ≤ (c*r^2*u)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hvbound) (add_nonneg hcu hv)]
  have hbpow : b0^9 ≤ b^9 := by gcongr
  have hsmallpow : (r*b^2)^4 ≤ eta^4 := by gcongr
  calc
    b0^9*v^2 ≤ b^9*(c*r^2*u)^2 :=
      mul_le_mul hbpow hvsq (sq_nonneg v) (pow_nonneg hb 9)
    _ = c^2*(r*b^2)^4*(b*u^2) := by ring
    _ ≤ c^2*eta^4*(b*u^2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsmallpow (sq_nonneg c))
        (mul_nonneg hb (sq_nonneg u))
    _ ≤ c^2*eta^4*energy :=
      mul_le_mul_of_nonneg_left henergy
        (mul_nonneg (sq_nonneg c) (pow_nonneg heta 4))

lemma norm_finiteCoreSobolevLift
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (y : R3) :
    ‖finiteCoreSobolevLift hO hD s F y‖ =
      ‖(coreWeightOperator hO hD (besselWeight s) F).val y‖ := by
  change ‖sphereSobolevZeroEquiv hO hD
    ((coreWeightOperator hO hD (besselWeight s) F).val y)‖ = _
  exact (sphereSobolevZeroEquiv hO hD).norm_map _

/-- Pointwise locality is independent of geometric room and of derivatives. -/
lemma finiteCoreSobolevLift_eq_zero_of_eq_zero
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (y : R3)
    (hFy : F.val y = 0) : finiteCoreSobolevLift hO hD s F y = 0 := by
  have hw : (coreWeightOperator hO hD (besselWeight s) F).val y = 0 := by
    change finiteHarmonicBlockCutoff hO hD F.property.2.2.choose
      (fun k => besselWeight s k •
        ContinuousLinearMap.id ℝ (harmonicSphereSubspace k)) (F.val y) = 0
    rw [hFy, map_zero]
  change sphereSobolevZeroEquiv hO hD
    ((coreWeightOperator hO hD (besselWeight s) F).val y) = 0
  rw [hw, map_zero]

lemma last_term_le_sourceNormSquareIntegrand
    {ι : Type*} [Fintype ι] (beta : ℝ) (hb : 0 ≤ beta)
    (gradientZero : ι → SphereL2) (phiOne : SphereL2)
    (gradientHalf : ι → SphereL2) (phiThreeHalf : SphereL2) :
    beta * ‖phiThreeHalf‖^2 ≤
      sourceNormSquareIntegrand beta gradientZero phiOne gradientHalf phiThreeHalf := by
  unfold sourceNormSquareIntegrand
  have hzero : 0 ≤ ∑ i, ‖gradientZero i‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hone : 0 ≤ beta^2 * ‖phiOne‖^2 :=
    mul_nonneg (sq_nonneg beta) (sq_nonneg _)
  have hhalf : 0 ≤ beta⁻¹ * ∑ i, ‖gradientHalf i‖^2 :=
    mul_nonneg (inv_nonneg.mpr hb) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  linarith

lemma beta_mul_norm_sq_finiteCoreSobolevLift_le_energy
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q beta : ℝ)
    (hb : 0 ≤ beta) (F : smoothCompactFiniteSphereCore hO hD) (y : R3) :
    beta * ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F y‖^2 ≤
      finiteCoreReferenceProfileEnergy hO hD g hg L q beta F y := by
  rw [norm_finiteCoreSobolevLift]
  unfold finiteCoreReferenceProfileEnergy
  exact last_term_le_sourceNormSquareIntegrand beta hb _ _ _ _

/-- The canonical H^(1/2) to physical L2 output loses no norm. -/
lemma norm_canonical_output_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (T : Hi →L[ℝ] Half) (u : Hi) :
    letI productsOperatorNormedAddCommGroup : NormedAddCommGroup (Hi →L[ℝ] Half) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ)
    letI productsOperatorNormedSpace : NormedSpace ℝ (Hi →L[ℝ] Half) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ)
    ‖(sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (T u))‖ ≤ ‖T‖ * ‖u‖ := by
  letI productsOperatorNormedAddCommGroup : NormedAddCommGroup (Hi →L[ℝ] Half) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ)
  letI productsOperatorNormedSpace : NormedSpace ℝ (Hi →L[ℝ] Half) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ)
  calc
    _ = ‖sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (T u)‖ :=
      (sphereSobolevZeroEquiv hO hD).symm.norm_map _
    _ ≤ ‖sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)‖ * ‖T u‖ :=
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)).le_opNorm _
    _ ≤ 1 * ‖T u‖ := mul_le_mul_of_nonneg_right
      (norm_sphereSobolevInclusionL_le (1/2 : ℝ) 0 (by norm_num)) (norm_nonneg _)
    _ ≤ ‖T‖ * ‖u‖ := by simpa only [one_mul] using T.le_opNorm u

theorem referencePhysicalDensityProducts_profile_pointwise_bound
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (d C_P : ℝ) (hd : 0 < d) (hdρ : d ≤ ρ) (hd1 : d ≤ 1) (hCP : 0 < C_P)
    (hRoom :
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ R : R3 → ℝ,
        ∀ y ∈ closedBall y0 ρ, 0 < R y → R y ≤ d →
          (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
          (∀ θ ∈ Icc (0 : ℝ) 1,
            (q,(y,θ*R y)) ∈ referenceRadialEndpointInvertibleLocus
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
          ∀ ξ : UnitSphere,
            (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)
    (hW :
      letI productsOperatorNormedAddCommGroup :
        NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
        ContinuousLinearMap.toNormedAddCommGroup
          (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
          (σ₁₂ := RingHom.id ℝ)
      letI productsOperatorNormedSpace :
        NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
        ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
          (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
          (σ₁₂ := RingHom.id ℝ)
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ R : R3 → ℝ, ContDiff ℝ ∞ R →
        ∀ y ∈ closedBall y0 ρ, 0 < R y → R y ≤ d → ‖fderiv ℝ R y‖ ≤ 1 →
          ‖referencePhysicalDensityProductsHalfOperator
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y‖ ≤
              C_P * (R y)^2) :
      letI productsOperatorNormedAddCommGroup :
        NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
        ContinuousLinearMap.toNormedAddCommGroup
          (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
          (σ₁₂ := RingHom.id ℝ)
      letI productsOperatorNormedSpace :
        NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
        ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
          (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
          (σ₁₂ := RingHom.id ℝ)
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ δ A : ℝ, ∀ p : ℕ,
        0 < δ → δ ≤ 1 → 0 < A → 1 ≤ p →
      ∀ eta betaMin : ℝ, 0 ≤ eta → eta ≤ 1 → 1 ≤ betaMin →
      ∀ F : smoothCompactFiniteSphereCore hO hD,
        tsupport F.val ⊆ closedBall y0 ρ →
        (∀ y ∈ tsupport F.val,
          referenceRadius δ A p L y ≤ d ∧
          ‖fderiv ℝ (referenceRadius δ A p L) y‖ ≤ 1 ∧
          betaMin ≤ actualReferenceBeta g L q δ A p y ∧
          referenceRadius δ A p L y * (actualReferenceBeta g L q δ A p y)^2 ≤ eta) →
      let u : R3 → SphereSobolev (3/2 : ℝ) :=
        finiteCoreSobolevLift hO hD (3/2 : ℝ) F
      let V : R3 → SphereL2 := fun y => (sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
          (referencePhysicalDensityProductsHalfOperator
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q
              (referenceRadius δ A p L) y (u y)))
      ∀ y : R3, betaMin^9 * ‖V y‖^2 ≤
        C_P^2 * eta^4 * finiteCoreReferenceProfileEnergy hO hD g hg L q
          (actualReferenceBeta g L q δ A p y) F y := by
  letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (Hi →L[ℝ] Half) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ)
  letI productsOperatorNormedSpace :
      NormedSpace ℝ (Hi →L[ℝ] Half) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ)
  intro q hq δ A p hδ hδ1 hA hp eta betaMin heta heta1 hbetaMin F hFsupp hsupport
  intro u V y
  have hb : 0 < actualReferenceBeta g L q δ A p y :=
    actualReferenceBeta_pos g hg L q δ A p hL hδ hA hp y
  have henergy : 0 ≤ finiteCoreReferenceProfileEnergy hO hD g hg L q
      (actualReferenceBeta g L q δ A p y) F y :=
    finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q _ hb.le F y
  by_cases hy : y ∈ tsupport F.val
  · have hs := hsupport y hy
    have hr : 0 < referenceRadius δ A p L y := referenceRadius_pos δ A p L y hδ hA
    have hR : ContDiff ℝ ∞ (referenceRadius δ A p L) :=
      OAI.AnisotropicCalderon.PhysicalDensityProductsProfileEnergyIntegrability.contDiff_referenceRadius
        δ A p L
    have hT := hW q hq (referenceRadius δ A p L) hR y (hFsupp hy) hr hs.1 hs.2.1
    have hV : ‖V y‖ ≤ C_P * (referenceRadius δ A p L y)^2 * ‖u y‖ := by
      calc
        ‖V y‖ ≤ ‖referencePhysicalDensityProductsHalfOperator
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q
              (referenceRadius δ A p L) y‖ * ‖u y‖ :=
          norm_canonical_output_le hO hD _ _
        _ ≤ C_P * (referenceRadius δ A p L y)^2 * ‖u y‖ :=
          mul_le_mul_of_nonneg_right hT (norm_nonneg _)
    exact pow_nine_mul_sq_le_of_radius_beta_bound
      (referenceRadius δ A p L y) (actualReferenceBeta g L q δ A p y)
      betaMin C_P eta ‖u y‖ ‖V y‖
      (finiteCoreReferenceProfileEnergy hO hD g hg L q
        (actualReferenceBeta g L q δ A p y) F y)
      hr.le hb.le (le_trans zero_le_one hbetaMin) hCP.le heta
      (norm_nonneg _) (norm_nonneg _) hs.2.2.1 hs.2.2.2 hV
      (beta_mul_norm_sq_finiteCoreSobolevLift_le_energy hO hD g hg L q _ hb.le F y)
  · have hFy : F.val y = 0 := by
      by_contra hFy
      exact hy (subset_closure hFy)
    have hu : u y = 0 := finiteCoreSobolevLift_eq_zero_of_eq_zero hO hD _ F y hFy
    have hV : V y = 0 := by
      change (sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
          (referencePhysicalDensityProductsHalfOperator
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q
              (referenceRadius δ A p L) y (u y))) = 0
      rw [hu, map_zero, map_zero, map_zero]
    simpa only [hV, norm_zero, pow_two, zero_mul, mul_zero] using
      (mul_nonneg (mul_nonneg (sq_nonneg C_P) (pow_nonneg heta 4)) henergy)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsProfilePointwise

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsProfilePointwise.pow_nine_mul_sq_le_of_radius_beta_bound
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsProfilePointwise.norm_finiteCoreSobolevLift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsProfilePointwise.finiteCoreSobolevLift_eq_zero_of_eq_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsProfilePointwise.last_term_le_sourceNormSquareIntegrand
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsProfilePointwise.beta_mul_norm_sq_finiteCoreSobolevLift_le_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsProfilePointwise.norm_canonical_output_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ProductsProfilePointwise.referencePhysicalDensityProducts_profile_pointwise_bound
