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
import Calderon.PhysicalDensityProductsProfilePointwiseEstimate
import Calderon.PhysicalDensityProductsProfileCanonicalProperties
import Calderon.PhysicalDensityProductsProfileIntegral

/-! Exact original conditional Products profile helper.
Full upfront: /tmp/ProductsProfileConditionalAssembly-v003/UPFRONT.md.
All three mathematical producers have native passes; full checking and configured
proof reviews remain required. Original consumer body remains unread.
-/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  ActualFiniteHarmonicCore SpectralCoreRegularity SpectralWeightedGraph
  ConformalDepth NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge
  ReferenceDensityBounds ActualFiniteHarmonicModel ReferenceWeightedApproximation

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)

theorem products_profile_properties_of_uniform_pointwise_bound
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
      ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ tsupport F.val ∧
      MemLp V 2 (volume : Measure R3) ∧
      (∀ y : R3,
        sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
          (sphereSobolevZeroEquiv hO hD (V y)) =
        sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
          (referencePhysicalDensityProductsHalfOperator
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q
              (referenceRadius δ A p L) y (u y))) ∧
      Integrable (fun y : R3 => referenceDensityFamily g L (q,y) * ‖V y‖^2) ∧
      betaMin^9 * (∫ y : R3, referenceDensityFamily g L (q,y) * ‖V y‖^2) ≤
        C_P^2 * eta^4 * (∫ y : R3, referenceDensityFamily g L (q,y) *
          finiteCoreReferenceProfileEnergy hO hD g hg L q
            (actualReferenceBeta g L q δ A p y) F y)  := by
  letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (Hi →L[ℝ] Half) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ)
  letI productsOperatorNormedSpace :
      NormedSpace ℝ (Hi →L[ℝ] Half) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ)
  intro q hq δ A p hδ hδ1 hA hp eta betaMin heta heta1 hbetaMin F hFsupp hsupport
  have hR : ContDiff ℝ ∞ (referenceRadius δ A p L) :=
    OAI.AnisotropicCalderon.PhysicalDensityProductsProfileEnergyIntegrability.contDiff_referenceRadius
      δ A p L
  have hRpos : ∀ y ∈ tsupport F.val, 0 < referenceRadius δ A p L y :=
    fun y _ => referenceRadius_pos δ A p L y hδ hA
  have hRd : ∀ y ∈ tsupport F.val, referenceRadius δ A p L y ≤ d :=
    fun y hy => (hsupport y hy).1
  have hqual := referencePhysicalDensityProducts_canonical_section_properties_of_uniform_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg g2 hg2
    d hRoom q hq (referenceRadius δ A p L) hR F hFsupp hRpos hRd
  rcases hqual with ⟨hVsmooth, hVcompact, hVsupport, hVMem, hVgraph⟩
  have hright : Integrable
      (fun y : R3 => (C_P^2 * eta^4) * (referenceDensityFamily g L (q,y) *
        finiteCoreReferenceProfileEnergy hO hD g hg L q
          (actualReferenceBeta g L q δ A p y) F y)) (volume : Measure R3) :=
    OAI.AnisotropicCalderon.PhysicalDensityProductsProfileEnergyIntegrability.integrable_const_mul_referenceProfileEnergyIntegrand
      hO hD g hg L q δ A p hL hδ hA hp F (C_P^2 * eta^4)
  have hpointwise :=
    ProductsProfilePointwise.referencePhysicalDensityProducts_profile_pointwise_bound
      g g2 hg hg2 L hL y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
      d C_P hd hdρ hd1 hCP hRoom hW q hq δ A p hδ hδ1 hA hp
      eta betaMin heta heta1 hbetaMin F hFsupp hsupport
  have hmeasure := ProductsProfileIntegral.integrable_weighted_norm_sq_and_integral_bound
    (fun y : R3 => referenceDensityFamily g L (q,y)) _
    (fun y : R3 => finiteCoreReferenceProfileEnergy hO hD g hg L q
      (actualReferenceBeta g L q δ A p y) F y) betaMin (C_P^2 * eta^4)
    (WeightedBaseSpectral.continuous_referenceBaseDensity g hg L q)
    (fun y => (referenceDensityFamily_pos g hg L (q,y)).le)
    hVsmooth hVcompact hright hpointwise
  exact ⟨hVsmooth, hVcompact, hVsupport, hVMem, hVgraph, hmeasure.1, hmeasure.2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.products_profile_properties_of_uniform_pointwise_bound
