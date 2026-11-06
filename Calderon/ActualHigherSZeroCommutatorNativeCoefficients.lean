import Calderon.ActualHigherSZeroCoefficientFactorisation
import Calderon.ActualHigherSZeroScalarCommutatorForm
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCommutatorNativeCoefficients
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
  PrincipalCommutator ActualScalarPrincipalAdjoint ActualPrincipalErrorCoefficient PerturbedDensityAdjoint
  ActualHigherSScalarCommutatorCoefficients ActualHigherSZeroScalarCommutatorForm
section Generic
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
/-- Coordinate directional jets from the same iterated bound, with its scalar prefactor retained. -/
lemma coordinate_jet_caps_of_iterated_bound (f : R3 → V) (x : R3) (C beta : ℝ)
    (hf : ContDiffAt ℝ ∞ f x)
    (hcap : ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n f x‖ ≤ C*beta^n) :
    ‖f x‖ ≤ C ∧
      (∀ k : Fin 3, ‖directionalFDeriv (coordinateDirection k) f x‖ ≤ C*beta) ∧
      (∀ k m : Fin 3, ‖directionalFDeriv (coordinateDirection m)
        (directionalFDeriv (coordinateDirection k) f) x‖ ≤ C*beta^2) := by
  have hc : ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n f x‖ ≤ C*(1:ℝ)^2*beta^n := by
    intro n hn
    simpa only [one_pow,mul_one] using hcap n hn
  have h := coordinate_jet_caps f x C 1 beta hf hc
  simpa only [one_pow,mul_one] using h
end Generic

private structure PrincipalTwoJetData (g : MatrixField) (L : ℝ) (K : Set R3) where
  A : ℝ
  pos : 0 < A
  cap : ∀ q ∈ Icc (0 : ℝ) 1, ∀ δr Ar : ℝ, ∀ p : ℕ,
    0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p → ∀ x ∈ K,
    ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
    (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
    (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
      (fun y => h y i j) x (eps*referenceRadius δr Ar p L x)) →
    1 ≤ actualReferenceBeta g L q δr Ar p x →
    referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ eps →
    ∀ i j k l : Fin 3,
      |actualPrincipalMatrix g L q δr Ar p h x i j| ≤ A*eps/(actualReferenceBeta g L q δr Ar p x)^2 ∧
      |directionalFDeriv (coordinateDirection k)
        (fun y => actualPrincipalMatrix g L q δr Ar p h y i j) x| ≤ A*eps/actualReferenceBeta g L q δr Ar p x ∧
      |directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k)
        (fun y => actualPrincipalMatrix g L q δr Ar p h y i j)) x| ≤ A*eps

private theorem exists_principalTwoJetData (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    Nonempty (PrincipalTwoJetData g L K) := by
  obtain ⟨A0,A1,A2,hA0,hA1,hA2,hcap⟩ :=
    exists_actual_principal_uniform_two_jet_bound g hg L hL K hK
  let A : ℝ := 1+A0+A1+A2
  have hA : 0 < A := by dsimp [A]; positivity
  have h0 : A0 ≤ A := by dsimp [A]; linarith
  have h1 : A1 ≤ A := by dsimp [A]; linarith
  have h2 : A2 ≤ A := by dsimp [A]; linarith
  refine ⟨⟨A,hA,?_⟩⟩
  intro q hq δr Ar p hδr hδr1 hAr hp x hx eps heps heps1 h hh hjet hb hsmall i j k l
  have hc := hcap q hq δr hδr hδr1 Ar hAr p hp x hx eps heps heps1 h hh hjet hb hsmall i j k l
  have hBeta : actualReferenceBeta g L q δr Ar p x =
      metricDifferentialNorm (referenceMetric (dilatedMetric g q) L)
        (fun y => Real.log (referenceRadius δr Ar p L y)) x := by
    unfold actualReferenceBeta
    rfl
  rw [← hBeta] at hc
  have hbpos : 0 < actualReferenceBeta g L q δr Ar p x := lt_of_lt_of_le zero_lt_one hb
  refine ⟨?_,?_,?_⟩
  · change |actualPrincipalMatrix g L q δr Ar p h x i j| ≤ _
    apply hc.1.trans
    gcongr
  · apply hc.2.1.trans
    gcongr
  · exact hc.2.2.trans (mul_le_mul_of_nonneg_right h2 heps)

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def zeroNativeNormed : NormedAddCommGroup (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] zeroNativeNormed
@[instance_reducible] private def zeroNativeSpace : NormedSpace ℝ (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] zeroNativeSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZc" => ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Actual surviving scalar/zero-S commutator budgets, with Q before all profiles and finite inputs. -/
theorem exists_actual_scalar_zero_coordinate_commutator_coefficient_bounds
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ δr Ar : ℝ, ∀ p : ℕ,
      0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      ∀ x : R3, (Tq δr Ar p q) x ∈ ParamRoom δ →
      (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps*referenceRadius δr Ar p L x)) →
      1 ≤ actualReferenceBeta g L q δr Ar p x →
      referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ eps →
      ZeroCommutatorCoefficientBudget
        (fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j)
        (fun y => CZc g2 δr Ar p q y) x eps (referenceRadius δr Ar p L x)
        (actualReferenceBeta g L q δr Ar p x) Q := by
  obtain ⟨D⟩ := exists_principalTwoJetData g hg L hL (closedBall y0 ρ) (isCompact_closedBall y0 ρ)
  obtain ⟨BZ,hBZ,hZcap⟩ := ActualHigherSZeroCoefficientFactorisation.canonicalZeroCoefficientJetTarget_actual
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2
  have hA : 0 < D.A := D.pos
  refine ⟨2*D.A*BZ,by positivity,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh x hx hjet hb hsmall
  let r := referenceRadius δr Ar p L x
  let beta := actualReferenceBeta g L q δr Ar p x
  let aa : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j
  let zz : R3 → (Hi →L[ℝ] Neg) := fun y => CZc g2 δr Ar p q y
  have hxK : x ∈ closedBall y0 ρ := by
    simpa only [ActualHigherSFormation.higherSParam] using hx.1.2.1
  have has := D.cap q hq δr Ar p hδr hδr1 hAr hp x hxK eps heps heps1 h hh hjet hb hsmall
  have hzcap := hZcap δr Ar p hδr hδr1 hAr hp q hq x hx hb (hsmall.trans heps1)
  have hzg : ContDiffAt ℝ ∞ zz x := ActualHigherSZeroCoefficientJets.contDiffAt_canonicalZeroCoefficient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2
      δr Ar p hδr hAr q x hx
  have ha (i j : Fin 3) : ContDiffAt ℝ ∞ (aa i j) x :=
    (ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh i j).contDiffAt
  have hZcaps := coordinate_jet_caps_of_iterated_bound zz x (BZ*r) beta hzg hzcap
  exact zeroCommutatorCoefficientBudget_of_bounds aa zz x eps r beta D.A BZ heps
    (referenceRadius_pos δr Ar p L x hδr hAr).le (lt_of_lt_of_le zero_lt_one hb)
    D.pos.le hBZ.le ha hzg (fun i j => (has i j 0 0).1)
    (fun i j k => (has i j k 0).2.1) hZcaps.2.1 hZcaps.2.2
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCommutatorNativeCoefficients
