import Calderon.FixedParameterProfileBudgets
import Calderon.ActualFullEGainedJointEndpoints

/-! The physical endpoints, obtained from the joint endpoints of
`ActualFullEGainedJointEndpoints`. -/
set_option autoImplicit false
set_option Elab.async false
set_option stderrAsMessages false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
  (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zH" => zeroReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zL" => zeroReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Rh" => originalRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Rl" => originalRadialLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "sh" => originalRadialReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "sl" => originalRadialReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Hh" => jacobiAngularOperatorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Hl" => jacobiAngularOperatorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "hh" => jacobiAngularReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "hl" => jacobiAngularReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RR" => retainedAdjacentHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "RH" => radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HR" => angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HH" => jacobiAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  originalRadialHigh originalRadialLow originalRadialReverseHigh originalRadialReverseLow
  jacobiAngularOperatorHigh jacobiAngularOperatorLow jacobiAngularReverseHigh jacobiAngularReverseLow
  zeroCorrectionHigh zeroCorrectionHalf zeroReverseHigh zeroReverseHalf sphereSobolevInclusionL
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  fullGainedHigh retainedAdjacentHigh radialAngularHigh angularRadialHigh jacobiAngularHigh
  commonRoom referenceRadialEndpointInvertibleLocus

/-! Physical fixed-q endpoint realization; every parameter guard is derived. -/
open FixedParameterProfilePullback FixedParameterProfileBudgets ConformalDepth
  ReferenceWeightedApproximation ActualScalarPrincipalAdjoint
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q

/-- Actual fixed-q physical value and first derivative caps. -/
def physicalEndpointFirstCaps {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Tpar → V) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (M KT : ℝ) : Prop :=
  ContDiffAt ℝ ∞ (fun y => f ((Tq dr Ar p q) y)) x ∧
    ‖f ((Tq dr Ar p q) x)‖ ≤ M ∧
    ‖fderiv ℝ (fun y => f ((Tq dr Ar p q) y)) x‖ ≤ M*KT

private theorem physicalEndpointFirstCaps_of_within_caps {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Tpar → V) (δ M KT : ℝ) (hM : 0 ≤ M)
    (hf : ContDiffOn ℝ ∞ f (ParamRoom δ)) (hU : UniqueDiffOn ℝ (ParamRoom δ))
    (hcap : ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom δ,
      ‖iteratedFDerivWithin ℝ n f (ParamRoom δ) t‖ ≤ M)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3)
    (hT : ContDiffAt ℝ ∞ (Tq dr Ar p q) x)
    (hmem : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom δ)
    (hTcap : ‖fderiv ℝ (Tq dr Ar p q) x‖ ≤ KT) :
    physicalEndpointFirstCaps (L := L) f dr Ar p q x M KT := by
  have hx := hmem.self_of_nhds
  have hc := physical_pullback_first_caps f (Tq dr Ar p q) (ParamRoom δ) x
    (hf _ hx) hT hmem (hU _ hx) M (hcap 0 (by omega) _ hx) (hcap 1 (by omega) _ hx)
  exact ⟨hc.1,hc.2.1,hc.2.2.trans (mul_le_mul_of_nonneg_left hTcap hM)⟩



/-- Transparent packaging of the original complete six-family all-order within caps. -/
def fullEJointWithinJetCaps (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (germs : CoeffRoom δ0) (δ : ℝ)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half)
    (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half)
    (Cl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg) : Prop :=
  (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ, n ≤ N → ∀ t ∈ ParamRoom δ,
        ‖iteratedFDerivWithin ℝ n
          (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs i j) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (Cl i j) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (EH i) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (EL i) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n
          (orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n
          (orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) (ParamRoom δ) t‖ ≤ M)

/-- The packaged joint cap is definitionally the complete original proposition. -/
theorem fullEJointWithinJetCaps_eq (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (germs : CoeffRoom δ0) (δ : ℝ)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half)
    (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half)
    (Cl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg) :
    fullEJointWithinJetCaps g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg δ0 germs δ Gcoord GN Cl =
  (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ, n ≤ N → ∀ t ∈ ParamRoom δ,
        ‖iteratedFDerivWithin ℝ n
          (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs i j) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (Cl i j) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (EH i) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (EL i) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n
          (orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n
          (orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) (ParamRoom δ) t‖ ≤ M) := rfl

/-- Transparent packaging of the original complete uniform physical caps. -/
def fullEPhysicalCaps (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (germs : CoeffRoom δ0) (δ : ℝ)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half)
    (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half)
    (Cl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg)
    (M KT eta0 : ℝ) : Prop :=
  ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
    ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta0 →
    ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
    1 ≤ actualReferenceBeta g L q dr Ar p x →
    referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
    ∀ i j : Fin 3,
      physicalEndpointFirstCaps (L := L)
        (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs i j)
        dr Ar p q x M KT ∧
      physicalEndpointFirstCaps (L := L) (Cl i j) dr Ar p q x M KT ∧
      physicalEndpointFirstCaps (L := L) (EH i) dr Ar p q x M KT ∧
      physicalEndpointFirstCaps (L := L) (EL i) dr Ar p q x M KT ∧
      physicalEndpointFirstCaps (L := L)
        (orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) dr Ar p q x M KT ∧
      physicalEndpointFirstCaps (L := L)
        (orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) dr Ar p q x M KT

/-- The packaged physical cap is definitionally the complete original proposition. -/
theorem fullEPhysicalCaps_eq (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (germs : CoeffRoom δ0) (δ : ℝ)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half)
    (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half)
    (Cl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg)
    (M KT eta0 : ℝ) :
    fullEPhysicalCaps g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg δ0 germs δ Gcoord GN Cl M KT eta0 =
  (∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
    ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta0 →
    ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
    1 ≤ actualReferenceBeta g L q dr Ar p x →
    referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
    ∀ i j : Fin 3,
      physicalEndpointFirstCaps (L := L)
        (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs i j)
        dr Ar p q x M KT ∧
      physicalEndpointFirstCaps (L := L) (Cl i j) dr Ar p q x M KT ∧
      physicalEndpointFirstCaps (L := L) (EH i) dr Ar p q x M KT ∧
      physicalEndpointFirstCaps (L := L) (EL i) dr Ar p q x M KT ∧
      physicalEndpointFirstCaps (L := L)
        (orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) dr Ar p q x M KT ∧
      physicalEndpointFirstCaps (L := L)
        (orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) dr Ar p q x M KT) := rfl

/-- Transparent packaging of the complete original gained_smooth proposition. -/
def fullEEndpointGainedSmooth (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (germs : CoeffRoom δ0) (δ : ℝ)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half)
    (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half)
    (Cl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg) : Prop :=
  (∀ i j : Fin 3,
        ContDiffOn ℝ ∞ (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (Cl i j) (ParamRoom δ))

/-- Definitional equality to the complete original gained_smooth proposition. -/
theorem fullEEndpointGainedSmooth_eq (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (germs : CoeffRoom δ0) (δ : ℝ)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half)
    (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half)
    (Cl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg) :
    fullEEndpointGainedSmooth g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg δ0 germs δ Gcoord GN Cl =
  (∀ i j : Fin 3,
        ContDiffOn ℝ ∞ (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (Cl i j) (ParamRoom δ)) := rfl

/-- Transparent packaging of the complete original ordinary_smooth proposition. -/
def fullEEndpointOrdinarySmooth (δ : ℝ) : Prop :=
  (∀ i : Fin 3, ContDiffOn ℝ ∞ (EH i) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (EL i) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) (ParamRoom δ))

/-- Definitional equality to the complete original ordinary_smooth proposition. -/
theorem fullEEndpointOrdinarySmooth_eq (δ : ℝ) :
    fullEEndpointOrdinarySmooth g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ =
  (∀ i : Fin 3, ContDiffOn ℝ ∞ (EH i) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (EL i) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) (ParamRoom δ)) := rfl

/-- Transparent packaging of the complete original high_graph proposition. -/
def fullEEndpointHighGraph (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (germs : CoeffRoom δ0) (δ : ℝ)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half)
    (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half) : Prop :=
  (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs i j t u) =
          orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t (EH j t u)-
            EL j t (orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t u))

/-- Definitional equality to the complete original high_graph proposition. -/
theorem fullEEndpointHighGraph_eq (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (germs : CoeffRoom δ0) (δ : ℝ)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half)
    (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half) :
    fullEEndpointHighGraph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg δ0 germs δ Gcoord GN =
  (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs i j t u) =
          orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t (EH j t u)-
            EL j t (orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t u)) := rfl

/-- Transparent packaging of the complete original low_graph proposition. -/
def fullEEndpointLowGraphs (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (germs : CoeffRoom δ0) (δ : ℝ)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half)
    (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half)
    (Cl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg) : Prop :=
  (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ,
        (Cl i j t).comp IH=(JL).comp (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs i j t) ∧
        (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp (Cl i j t)=
          (v016TransposeL (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs j i t)).comp JL ∧
        ‖Cl i j t‖ ≤
          (‖fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs j i t‖+
           ‖fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs i j t‖)/2)

/-- Definitional equality to the complete original low_graph proposition. -/
theorem fullEEndpointLowGraphs_eq (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (germs : CoeffRoom δ0) (δ : ℝ)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half)
    (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half)
    (Cl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg) :
    fullEEndpointLowGraphs g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg δ0 germs δ Gcoord GN Cl =
  (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ,
        (Cl i j t).comp IH=(JL).comp (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs i j t) ∧
        (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp (Cl i j t)=
          (v016TransposeL (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs j i t)).comp JL ∧
        ‖Cl i j t‖ ≤
          (‖fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs j i t‖+
           ‖fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 germs i j t‖)/2) := rfl

example : True := by
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-PHYSICAL-PACKAGE ALL-SIX-PROPERTIES-COMPLETE"
    out.flush
  trivial

/-- All joint witnesses and constants are selected before every physical profile and angular input. -/
structure FullEPhysicalEndpointRoom (hreg : FixedDirichletRegularity) where
  δ0 : ℝ
  δ0_pos : 0 < δ0
  δ0_le : δ0 ≤ ρ
  germs : CoeffRoom δ0
  δ : ℝ
  δ_pos : 0 < δ
  δ_le0 : δ ≤ δ0
  δ_le : δ ≤ ρ
  parameter_subset : commonRoom y0 ρ δ ⊆ Ω
  Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half
  GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half
  Cl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg
  gained_smooth : fullEEndpointGainedSmooth g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg δ0 germs δ Gcoord GN Cl
  ordinary_smooth : fullEEndpointOrdinarySmooth g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ
  high_graph : fullEEndpointHighGraph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg δ0 germs δ Gcoord GN
  low_graph : fullEEndpointLowGraphs g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg δ0 germs δ Gcoord GN Cl
  joint_caps : fullEJointWithinJetCaps g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg δ0 germs δ Gcoord GN Cl
  M : ℝ
  M_nonneg : 0 ≤ M
  KT : ℝ
  KT_pos : 0 < KT
  eta0 : ℝ
  eta0_pos : 0 < eta0
  eta0_le : eta0 ≤ 1
  physical_caps : fullEPhysicalCaps g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg δ0 germs δ Gcoord GN Cl M KT eta0



example : True := by
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-PHYSICAL-PACKAGE STRUCTURE-COMPLETE"
    out.flush
  trivial

/-- The actual complete joint producer discharges every physical cap; q endpoints are included. -/
theorem exists_fullE_physical_endpoint_room (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    Nonempty (FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg) := by
  classical
  obtain ⟨δ0, hδ0, hδ0ρ, W, δ, hδ, hδ0le, hδρ, hRoom,
    Gcoord, GN, Cl, hSm, hOrd, hGraph, hCl, hCaps⟩ :=
    exists_commonRoom_actual_fullE_gained_smooth_endpoints
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel
  obtain ⟨M, hM, hcap⟩ := hCaps 1
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-PHYSICAL JOINT-WITNESSES-SELECTED"
    out.flush
  let K := closedBall y0 ρ
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨KT, hKT, hTbound⟩ :=
    exists_uniform_higherSParam_derivative_bound g hg L hL K hK
  obtain ⟨eta0, heta0, heta01, hguard⟩ :=
    exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ δ hδ K hK
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-PHYSICAL PROFILE-WITNESSES-SELECTED"
    out.flush
  have hU : UniqueDiffOn ℝ (ParamRoom δ) :=
    (uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 hδ).prod
      (uniqueDiffOn_convex (convex_closedBall _ _) ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  refine ⟨{
    δ0 := δ0,
    δ0_pos := hδ0,
    δ0_le := hδ0ρ,
    germs := W,
    δ := δ,
    δ_pos := hδ,
    δ_le0 := hδ0le,
    δ_le := hδρ,
    parameter_subset := hRoom,
    Gcoord := Gcoord,
    GN := GN,
    Cl := Cl,
    gained_smooth := hSm,
    ordinary_smooth := hOrd,
    high_graph := hGraph,
    low_graph := hCl,
    joint_caps := hCaps,
    M := M,
    M_nonneg := hM,
    KT := KT,
    KT_pos := hKT,
    eta0 := eta0,
    eta0_pos := heta0,
    eta0_le := heta01,
    physical_caps := ?_
  }⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0le x hx hxBall hb hs i j
  have hGuard := hguard q hq dr hdr hdr1 Ar hAr p hp eta heta heta0le x hx hxBall hb hs
  have hmem := higherSParam_eventually_mem y0 ρ δ L dr Ar q p hdr hAr x hGuard
  have hxT := hmem.self_of_nhds
  have hT : ContDiffAt ℝ ∞ (Tq dr Ar p q) x :=
    (contDiff_radiusProfileMap q (referenceRadius dr Ar p L)
      (contDiff_referenceRadius_actual dr Ar p L hdr hAr)).contDiffAt
  have hTc := hTbound q hq dr hdr hdr1 Ar hAr p hp eta heta (heta0le.trans heta01) x hx hb hs
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact physicalEndpointFirstCaps_of_within_caps (L := L) (y0 := y0) (ρ := ρ)
      _ δ M KT hM (hSm i j).1 hU (fun n hn t ht => (hcap i j n hn t ht).1)
      dr Ar p q x hT hmem hTc
  · exact physicalEndpointFirstCaps_of_within_caps (L := L) (y0 := y0) (ρ := ρ)
      _ δ M KT hM (hSm i j).2 hU (fun n hn t ht => (hcap i j n hn t ht).2.1)
      dr Ar p q x hT hmem hTc
  · exact physicalEndpointFirstCaps_of_within_caps (L := L) (y0 := y0) (ρ := ρ)
      _ δ M KT hM (hOrd i).1 hU (fun n hn t ht => (hcap i j n hn t ht).2.2.1)
      dr Ar p q x hT hmem hTc
  · exact physicalEndpointFirstCaps_of_within_caps (L := L) (y0 := y0) (ρ := ρ)
      _ δ M KT hM (hOrd i).2.1 hU (fun n hn t ht => (hcap i j n hn t ht).2.2.2.1)
      dr Ar p q x hT hmem hTc
  · exact physicalEndpointFirstCaps_of_within_caps (L := L) (y0 := y0) (ρ := ρ)
      _ δ M KT hM (hOrd i).2.2.1 hU (fun n hn t ht => (hcap i j n hn t ht).2.2.2.2.1)
      dr Ar p q x hT hmem hTc
  · exact physicalEndpointFirstCaps_of_within_caps (L := L) (y0 := y0) (ρ := ρ)
      _ δ M KT hM (hOrd i).2.2.2 hU (fun n hn t ht => (hcap i j n hn t ht).2.2.2.2.2)
      dr Ar p q x hT hmem hTc


example : True := by
  run_tac do
    let out ← IO.getStderr
    let observed ← IO.monoMsNow
    out.putStrLn ("E-PHYSICAL-CANONICAL SUPPORTING-THEOREM-COMMAND-COMPLETE mono_ms=" ++ toString observed)
    out.flush
  trivial

/-- The actual compact reciprocal-room theorem supplies the remaining geometric witness. -/
theorem exists_actual_fullE_physical_endpoint_room (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ ActualRoom : ReferenceGaugeNormalReciprocalRoom g L Φ a
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)),
      Nonempty (FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 ActualRoom hreg) := by
  let Q := Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)
  have hQ : IsCompact Q := isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  let ActualRoom := referenceGaugeNormalReciprocalRoomOfCompact g L Φ y0 B ε C ρ H a w hData hg Q hQ
  exact ⟨ActualRoom,exists_fullE_physical_endpoint_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    ActualRoom hL hreg hKernel⟩

example : True := by
  run_tac do
    let out ← IO.getStderr
    let observed ← IO.monoMsNow
    out.putStrLn ("E-PHYSICAL-CANONICAL FINAL-ACTUAL-THEOREM-COMMAND-COMPLETE mono_ms=" ++ toString observed)
    out.flush
  trivial

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly.exists_commonRoom_actual_fullE_gained_smooth_endpoints

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly.exists_actual_fullE_physical_endpoint_room
