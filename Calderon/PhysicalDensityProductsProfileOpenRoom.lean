import Calderon.ActualPhysicalDensityProductsAdjointOperatorCore
import Calderon.ActualPhysicalDensityProductsWeightedAdjunction
import Calderon.FiniteOperatorProductsSmoothness
import Calderon.ActualHigherRadiusProfile
import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.ActualPhysicalDensityProductsOperatorIdentities
import Calderon.PhysicalDensityProductsOperatorSmoothness

/-! Actual Main M1 Products adjoint. Full nine-root before-code expansion and
exact original definitions were reviewed before authoring. No quantitative
Productsdag cap, finite-output assumption or intrinsic Half adjoint is used. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  ActualFiniteHarmonicCore SpectralCoreRegularity SpectralWeightedGraph
  ConformalDepth NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge ReferenceDensityBounds
  ActualHigherRadiusProfile
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv
  sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL
  sphereSobolevLinearCoordinateMulL referenceNativeMovingAdjointParametricCorrection
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceAdjointMovingDifferenceQuotientPivotHigh referenceAdjointMovingDifferenceQuotientPivotLow

set_option Elab.async false

theorem exists_referencePhysicalDensityProducts_profile_open_room
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (hKgeom : K ⊆ closedBall y0 ρ) :
    ∃ p0 : ℕ, 2 ≤ p0 ∧
      ∀ p : ℕ, p0 ≤ p → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
      ∃ A : ℝ, 0 < A ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
      let R : R3 → ℝ := referenceRadius delta A p L
      let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      let U : Set R3 := {y | R y ≠ 0 ∧
        (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈ Ω) ∧
        (∀ ξ : UnitSphere,
          (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)}
      ContDiff ℝ ∞ R ∧ (∀ y : R3, 0 < R y) ∧ IsOpen U ∧ K ⊆ U ∧
      ContDiffOn ℝ ∞ (fun y : R3 => referencePhysicalDensityProductsHalfOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y) U ∧
      ContDiffOn ℝ ∞ (fun y : R3 => referencePhysicalDensityProductsAdjointHalfOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y) U := by
  classical
  obtain ⟨d,hd,hdρ,hRoom⟩ := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  obtain ⟨p0,hp0Power,hp02,hProfiles⟩ :=
    exists_fixed_actual_reference_beta_power_radius_profile g hg L hL K hK 0
  refine ⟨p0,hp02,?_⟩
  intro p hp eta heta heta1
  let etaEff : ℝ := min eta d
  have hetaEff : 0 < etaEff := lt_min heta hd
  have hetaEff1 : etaEff ≤ 1 := (min_le_left eta d).trans heta1
  obtain ⟨A,hA,hAll⟩ := hProfiles p hp etaEff hetaEff hetaEff1
  refine ⟨A,hA,?_⟩
  intro q hq delta hdelta hdelta1 g2 hg2 R Ω U
  have hRpos (y : R3) : 0 < R y := referenceRadius_pos delta A p L y hdelta hA
  have hR : ContDiff ℝ ∞ R :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual delta A p L hdelta hA
  have hCover := referenceFramedNormalizedJacobian_isInvertible_on_actual_coefficient_tube
    g L y0 Φ B ε C ρ H a w hData d hd hdρ
  have hKRoom (y : R3) (hy : y ∈ K) : y ∈ U := by
    have hPoint := hAll q hq delta hdelta hdelta1 y hy
    have hyBall : y ∈ closedBall y0 ρ := hKgeom hy
    have hRadius : R y ≤ d := hPoint.2.2.trans (min_le_right eta d)
    refine ⟨(hRpos y).ne',?_,?_⟩
    · intro θ hθ
      have hθr : |θ*R y| ≤ d := by
        rw [abs_mul,abs_of_nonneg hθ.1,abs_of_pos (hRpos y)]
        exact (mul_le_mul_of_nonneg_right hθ.2 (hRpos y).le).trans
          (by simpa only [one_mul] using hRadius)
      exact hRoom ⟨hq,hyBall,abs_le.mp hθr⟩
    · exact hCover (q,(y,R y)) ⟨hq,hyBall,
        ⟨(neg_nonpos.mpr hd.le).trans (hRpos y).le,hRadius⟩⟩
  have hNatural := contDiffOn_referenceHighAdjoint_weighted_correction_open_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hOperators := contDiffOn_referencePhysicalDensityProducts_half_operators
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg g2 hg2 q hq R hR
  exact ⟨hR,hRpos,hNatural.1,hKRoom,hOperators.1,hOperators.2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
