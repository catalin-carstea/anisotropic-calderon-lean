import Calderon.ActualPhysicalDensityProductsOperatorIdentities
import Calderon.ActualHighAdjointUnweightedPointValue
import Calderon.ActualHighAdjointStaticEndpointJetBounds
import Calderon.ActualJacobiThreeHalfBoundaryMultiplierFamily
import Calderon.ActualJacobiCoefficientTubeCover
import Calderon.ActualNativeMovingHighLocalRemainderSmoothness
import Calderon.FiniteCoreH1BesselNorm
import Calderon.ActualFiniteHarmonicModelHorizontalProfileIntegral
import Calderon.ActualPhysicalDensityProductsAdjointOperatorCore
import Calderon.ActualPhysicalDensityProductsWeightedAdjunction
import Calderon.FiniteOperatorProductsSmoothness

/-! Collaboration boundary only. These two Props reproduce existing exact Main
Products targets; they neither assume the targets nor prove them. No theorem
body, mathematical definition, normed structure or dependency pin is changed.
Main proves these statements; the transfer/coercivity coordinator consumes them
when developing signed absorption and the uniform full physical lower bound. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
namespace CoercivityTransfer
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore
  ActualFiniteHarmonicModel ConformalDepth ReferenceWeightedApproximation
  ReferenceDensityBounds SpectralCoreRegularity SpectralWeightedGraph
  ActualHorizontalNormBridge NormalizedPrincipalMetricSmooth

def physical_products_uniform_profile_estimate : Prop :=
  ∀ (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace),
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
    ∃ d C_P : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧ 0 < C_P ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ R : R3 → ℝ, ContDiff ℝ ∞ R →
        ∀ y ∈ closedBall y0 ρ, 0 < R y → R y ≤ d → ‖fderiv ℝ R y‖ ≤ 1 →
          ‖referencePhysicalDensityProductsHalfOperator
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y‖ ≤
              C_P * (R y)^2) ∧
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
            (actualReferenceBeta g L q δ A p y) F y)

def physical_products_weighted_adjunction : Prop :=
  ∀ (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (hKgeom : K ⊆ closedBall y0 ρ),
    ∃ p0 : ℕ, 2 ≤ p0 ∧
      ∀ p : ℕ, p0 ≤ p → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
      ∃ A : ℝ, 0 < A ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
      ∀ F G : smoothCompactFiniteSphereCore hO hD,
      tsupport F.val ⊆ K → tsupport G.val ⊆ K →
      let R : R3 → ℝ := referenceRadius delta A p L
      let uF : R3 → SphereSobolev (3/2 : ℝ) := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
      let uG : R3 → SphereSobolev (3/2 : ℝ) := finiteCoreSobolevLift hO hD (3/2 : ℝ) G
      let K0 : SphereL2 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
        (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
          (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
      ∃ pF pdagG : R3 → SphereL2,
        ContDiff ℝ ∞ pF ∧ HasCompactSupport pF ∧ MemLp pF 2 (volume : Measure R3) ∧
        tsupport pF ⊆ tsupport F.val ∧
        ContDiff ℝ ∞ pdagG ∧ HasCompactSupport pdagG ∧ MemLp pdagG 2 (volume : Measure R3) ∧
        tsupport pdagG ⊆ tsupport G.val ∧
        (∀ y : R3, K0 (pF y) =
    (R y)^2 • (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
          (referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y j (uF y))) +
       referenceLowerAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
          (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,y),fderiv ℝ R y) j (uF y)))))) ∧
        (∀ y : R3, K0 (pdagG y) =
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
            (referencePhysicalDensityProductsAdjointHalfOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y (uG y))) ∧
        (∀ y : R3, ⟪pF y,G.val y⟫_ℝ = ⟪F.val y,pdagG y⟫_ℝ) ∧
        (∫ y : R3, referenceDensityFamily g L (q,y) * ⟪pF y,G.val y⟫_ℝ) =
          ∫ y : R3, referenceDensityFamily g L (q,y) * ⟪F.val y,pdagG y⟫_ℝ

end CoercivityTransfer
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
