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

/-! The qualitative properties needed for the original canonical Products section. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  ActualFiniteHarmonicCore SpectralCoreRegularity SpectralWeightedGraph
  ConformalDepth NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge ReferenceDensityBounds
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv
set_option Elab.async false

theorem referencePhysicalDensityProducts_canonical_section_properties
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hFs : tsupport F.val ⊆ closedBall y0 ρ)
    (hRoom : ∀ y ∈ tsupport F.val, R y ≠ 0 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      (∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)) :
    let u : R3 → Hi := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
    let V : R3 → SphereL2 := fun y => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (referencePhysicalDensityProductsHalfOperator
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y (u y)))
    ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ tsupport F.val ∧
    MemLp V 2 (volume : Measure R3) ∧
    (∀ y : R3,
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (V y)) =
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referencePhysicalDensityProductsHalfOperator
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y (u y))) := by
  classical
  intro u V
  have hs : tsupport V ⊆ tsupport F.val := by
    have hu : tsupport u ⊆ tsupport F.val :=
      (finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F).2.2.1
    apply closure_minimal ?_ (isClosed_tsupport F.val)
    intro y hy
    by_contra hn
    have hn' : y ∉ tsupport u := fun h => hn (hu h)
    have hz : u y = 0 := image_eq_zero_of_notMem_tsupport hn'
    exact hy (by simp only [V, hz, map_zero])
  let Op : R3 → Hi →L[ℝ] Half := fun y => referencePhysicalDensityProductsHalfOperator
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y
  let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let U : Set R3 := {y | R y ≠ 0 ∧
    (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈ Ω) ∧
    (∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)}
  let J : Half →L[ℝ] SphereL2 :=
    { toFun := fun z => (sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) z)
      map_add' := by intro z z'; simp only [map_add]
      map_smul' := by intro c z; simp only [map_smul, RingHom.id_apply]
      cont := (sphereSobolevZeroEquiv hO hD).symm.continuous.comp
        (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)).continuous }
  have hNatural := contDiffOn_referenceHighAdjoint_weighted_correction_open_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hOperators := contDiffOn_referencePhysicalDensityProducts_half_operators
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg g2 hg2 q hq R hR
  have hRep := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F
  have hSection := contDiff_comp_clm_apply_of_tsupport_subset
    U hNatural.1 u hRep.1 hRep.2.1
    (fun y hy => hRoom y (hRep.2.2.1 hy))
    Op hOperators.1 J
  have hd : ContDiff ℝ ∞ V := hSection.1
  have hc : HasCompactSupport V :=
    F.property.2.1.of_isClosed_subset (isClosed_tsupport V) hs
  refine ⟨hd, hc, hs, hd.continuous.memLp_of_hasCompactSupport hc, ?_⟩
  intro y
  have hV : sphereSobolevZeroEquiv hO hD (V y) =
      sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (referencePhysicalDensityProductsHalfOperator
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y (u y)) :=
    (sphereSobolevZeroEquiv hO hD).apply_symm_apply _
  rw [hV]
  exact congrArg
    (fun T : Half →L[ℝ] Neg => T
      (referencePhysicalDensityProductsHalfOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y (u y)))
    (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ))
      (by norm_num) (by norm_num))

theorem referencePhysicalDensityProducts_canonical_section_properties_of_uniform_room
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (d : ℝ)
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
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hFs : tsupport F.val ⊆ closedBall y0 ρ)
    (hRpos : ∀ y ∈ tsupport F.val, 0 < R y)
    (hRd : ∀ y ∈ tsupport F.val, R y ≤ d) :
    let u : R3 → Hi := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
    let V : R3 → SphereL2 := fun y => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (referencePhysicalDensityProductsHalfOperator
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y (u y)))
    ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ tsupport F.val ∧
    MemLp V 2 (volume : Measure R3) ∧
    (∀ y : R3,
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (V y)) =
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referencePhysicalDensityProductsHalfOperator
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y (u y))) := by
  have hSectionRoom : ∀ y ∈ tsupport F.val, R y ≠ 0 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      (∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible) := by
    intro y hy
    have h := hRoom q hq R y (hFs hy) (hRpos y hy) (hRd y hy)
    exact ⟨ne_of_gt (hRpos y hy), h.2.1, h.2.2⟩
  exact referencePhysicalDensityProducts_canonical_section_properties
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg g2 hg2
    q hq R hR F hFs hSectionRoom

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
