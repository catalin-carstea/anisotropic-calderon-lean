import Calderon.ActualRawAdjointDegreeSignedRemainder
import Calderon.CompactInverseDerivativeBounds

set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff ENNReal Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.RawAdjointDegreeGainDraft
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "NegH" => SphereSobolev (-(1/2 : ℝ))
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local instance] rawAdjointDegreeHalfCompleteSpace rawAdjointDegreeNegativeCompleteSpace

local instance rawDegreeHighHalfSeminormedGroup : SeminormedAddCommGroup (Hi →L[ℝ] Half) := ContinuousLinearMap.toSeminormedAddCommGroup
local instance rawDegreeHighHalfNormedGroup : NormedAddCommGroup (Hi →L[ℝ] Half) := ContinuousLinearMap.toNormedAddCommGroup
local instance rawDegreeHighHalfNormedSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := ContinuousLinearMap.toNormedSpace
local instance rawDegreeHalfNegativeSeminormedGroup : SeminormedAddCommGroup (Half →L[ℝ] NegH) := ContinuousLinearMap.toSeminormedAddCommGroup
local instance rawDegreeHalfNegativeNormedGroup : NormedAddCommGroup (Half →L[ℝ] NegH) := ContinuousLinearMap.toNormedAddCommGroup
local instance rawDegreeHalfNegativeNormedSpace : NormedSpace ℝ (Half →L[ℝ] NegH) := ContinuousLinearMap.toNormedSpace

local notation "Csharp" => referenceRadialDegreeCommutatorHalfFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Wsharp" => referenceTwoAngleDegreeRotationDerivativeFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
local notation "Qsharp" => referenceTwoAngleDegreeCommutatorHalfFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

/-! ## Root draft (kept): negative-transpose low families and the explicit high lift -/

local notation "Ct" => lowFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Wt" => rotationDerivativeFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0

local notation "Gt" => gainedHighFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0

local notation "Gt2" => gainedHighSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0

/-! ## Typed per-family caps (MATHEMATICS.md §1.2)

Each cap is its own declaration, stated in this instance context, so its conclusion is
literally the corresponding sub-formula of `exists_compact_rawAdjointDegree_jet_caps`.
No proof-local instances: `f` is passed explicitly and the CLM type is inferred from it. -/

private lemma rawDegreeCap_gainedHigh (Kc : Set (ℝ × (R3 × ℝ)))
    (hKc : IsCompact Kc) (hKΩ : Kc ⊆ Ω) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ p ∈ Kc, ‖iteratedFDeriv ℝ n Gt p‖ ≤ M := by
  obtain ⟨M,hM,hB⟩ := exists_compact_iteratedFDeriv_bound Gt Kc hKc
    (fun p hp => contDiffAt_gainedHighFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p (hKΩ hp)) N
  exact ⟨M,hM,hB⟩

include hreg in
private lemma rawDegreeCap_low (Kc : Set (ℝ × (R3 × ℝ)))
    (hKc : IsCompact Kc) (hKΩ : Kc ⊆ Ω) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ p ∈ Kc, ‖iteratedFDeriv ℝ n Ct p‖ ≤ M := by
  obtain ⟨M,hM,hB⟩ := exists_compact_iteratedFDeriv_bound Ct Kc hKc
    (fun p hp => contDiffAt_lowFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p (hKΩ hp)) N
  exact ⟨M,hM,hB⟩

private lemma rawDegreeCap_rotation (Kc : Set (ℝ × (R3 × ℝ)))
    (hKc : IsCompact Kc) (hKΩ : Kc ⊆ Ω) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k l : Fin 3, ∀ n : ℕ, n ≤ N → ∀ p ∈ Kc,
      ‖iteratedFDeriv ℝ n (Wt k l) p‖ ≤ M := by
  have hW (k l : Fin 3) := exists_compact_iteratedFDeriv_bound (Wt k l) Kc hKc
    (fun p hp => contDiffAt_rotationDerivativeFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p (hKΩ hp)) N
  choose MW hMW hWb using hW
  refine ⟨∑ i : Fin 3, ∑ j : Fin 3, MW i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hMW i j)), ?_⟩
  intro k l n hn p hp
  have hkl : MW k l ≤ ∑ i : Fin 3, ∑ j : Fin 3, MW i j :=
    (Finset.single_le_sum (f := fun j => MW k j) (fun j _ => hMW k j)
      (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun i => ∑ j : Fin 3, MW i j)
        (fun i _ => Finset.sum_nonneg (fun j _ => hMW i j)) (Finset.mem_univ k))
  exact (hWb k l n hn p hp).trans hkl

/-! ## Opaque real-valued combination (MATHEMATICS.md §1.3, §2)

Generic over the point type and over the three real-valued jet-norm functions, so no
physical term is ever destructured or re-checked. In the public theorem the implicit
functions are solved by Miller-pattern unification against the original header. -/

private lemma rawDegreeCaps_combine {P : Type*} {Kc : Set P} {N : ℕ}
    {fG fC : ℕ → P → ℝ} {fW : Fin 3 → Fin 3 → ℕ → P → ℝ}
    (hG : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ p ∈ Kc, fG n p ≤ M)
    (hC : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ p ∈ Kc, fC n p ≤ M)
    (hW : ∃ M : ℝ, 0 ≤ M ∧ ∀ k l : Fin 3, ∀ n : ℕ, n ≤ N → ∀ p ∈ Kc, fW k l n p ≤ M) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ p ∈ Kc,
      fG n p ≤ M ∧ fC n p ≤ M ∧ ∀ k l : Fin 3, fW k l n p ≤ M := by
  obtain ⟨MG,hMG,hG'⟩ := hG
  obtain ⟨MC,hMC,hC'⟩ := hC
  obtain ⟨MW,hMW,hW'⟩ := hW
  refine ⟨MG+MC+MW,add_nonneg (add_nonneg hMG hMC) hMW,?_⟩
  intro n hn p hp
  refine ⟨?_,?_,?_⟩
  · linarith [hG' n hn p hp]
  · linarith [hC' n hn p hp]
  · intro k l
    linarith [hW' k l n hn p hp]

theorem exists_compact_rawAdjointDegree_jet_caps (Kc : Set (ℝ × (R3 × ℝ)))
    (hKc : IsCompact Kc) (hKΩ : Kc ⊆ Ω) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ p ∈ Kc,
      ‖iteratedFDeriv ℝ n Gt p‖ ≤ M ∧ ‖iteratedFDeriv ℝ n Ct p‖ ≤ M ∧
      ∀ k l : Fin 3, ‖iteratedFDeriv ℝ n (Wt k l) p‖ ≤ M :=
  rawDegreeCaps_combine
    (rawDegreeCap_gainedHigh
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 Kc hKc hKΩ N)
    (rawDegreeCap_low
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 Kc hKc hKΩ N)
    (rawDegreeCap_rotation
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 Kc hKc hKΩ N)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.RawAdjointDegreeGainDraft
