import Calderon.ActualRawAdjointDegreeCompactCaps

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

attribute [local instance] rawDegreeHighHalfSeminormedGroup rawDegreeHighHalfNormedGroup rawDegreeHighHalfNormedSpace rawDegreeHalfNegativeSeminormedGroup rawDegreeHalfNegativeNormedGroup rawDegreeHalfNegativeNormedSpace

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

/-! ## Common-room helpers (MATHEMATICS.md §1.4, §2)

`R_δ = Icc 0 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)`. The segment lemma is elementary. Each
per-family cap bounds one jet on `R_δ` for any `δ` with `R_δ ⊆ Ω`; it is a direct application
of `exists_compact_iteratedFDeriv_bound` (no destructuring). No proof-local instances. -/

private lemma rawDegreeFinal_segment (δ : ℝ)
    (hRoom : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ), p ∈ Ω)
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)) :
    ∀ θ ∈ Icc (0:ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω := by
  intro θ hθ
  have ht : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
  have hr : |p.2.2| ≤ δ := abs_le.mpr hp.2.2
  have htr : |θ*p.2.2| ≤ δ := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans (by simpa only [one_mul] using hr)
  exact hRoom (p.1,(p.2.1,θ*p.2.2)) ⟨hp.1,hp.2.1,abs_le.mp htr⟩

private lemma rawDegreeFinal_cap_gainedHigh (δ : ℝ)
    (hRoom : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ), p ∈ Ω) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N →
      ∀ p ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ),
        ‖iteratedFDeriv ℝ n Gt p‖ ≤ M := by
  have hK : IsCompact (Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)) :=
    isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  exact exists_compact_iteratedFDeriv_bound Gt _ hK
    (fun p hp => contDiffAt_gainedHighFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p (hRoom p hp)) N

private lemma rawDegreeFinal_cap_secondRemainder (δ : ℝ)
    (hRoom : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ), p ∈ Ω) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N →
      ∀ p ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ),
        ‖iteratedFDeriv ℝ n (fun z : ℝ × (R3 × ℝ) => Gt2 z.1 z.2.1 z.2.2) p‖ ≤ M := by
  have hK : IsCompact (Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)) :=
    isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  exact exists_compact_iteratedFDeriv_bound
    (fun z : ℝ × (R3 × ℝ) => Gt2 z.1 z.2.1 z.2.2) _ hK
    (fun p hp => contDiffAt_gainedHighSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2
      (rawDegreeFinal_segment g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 δ hRoom p hp)) N

/-! ## Opaque common-room assembly (MATHEMATICS.md §1.4, §2)

Generic over the point type, the room family `R`, the locus `U`, the five pointwise
predicates and the two real-valued jet-norm functions. One `δ` comes from the radius
hypothesis before `N`, and one `M = MA + MB ≥ 0` comes before the point and the order. In
the public theorem every implicit argument is solved by Miller-pattern unification against
the original header. -/

private lemma rawDegreeFinal_combine {P : Type*} {ρ' : ℝ} {R : ℝ → Set P} {U : Set P}
    {Q2 Q3 Q4 Q5 Q6 : P → Prop} {fA fB : ℕ → P → ℝ}
    (hδ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ' ∧ R δ ⊆ U)
    (hseg : ∀ δ : ℝ, (∀ p ∈ R δ, p ∈ U) → ∀ p ∈ R δ, Q2 p)
    (h3 : ∀ p : P, p ∈ U → Q3 p) (h4 : ∀ p : P, Q2 p → Q4 p)
    (h5 : ∀ p : P, p ∈ U → Q5 p) (h6 : ∀ p : P, Q2 p → Q6 p)
    (hA : ∀ δ : ℝ, (∀ p ∈ R δ, p ∈ U) → ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ n : ℕ, n ≤ N → ∀ p ∈ R δ, fA n p ≤ M)
    (hB : ∀ δ : ℝ, (∀ p ∈ R δ, p ∈ U) → ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ n : ℕ, n ≤ N → ∀ p ∈ R δ, fB n p ≤ M) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ' ∧ ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ p ∈ R δ, p ∈ U ∧ Q2 p ∧ Q3 p ∧ Q4 p ∧ Q5 p ∧ Q6 p ∧
        ∀ n : ℕ, n ≤ N → fA n p ≤ M ∧ fB n p ≤ M := by
  obtain ⟨δ,hδ0,hδρ,hRoom⟩ := hδ
  have hR : ∀ p ∈ R δ, p ∈ U := fun p hp => hRoom hp
  refine ⟨δ,hδ0,hδρ,fun N => ?_⟩
  obtain ⟨MA,hMA,hA'⟩ := hA δ hR N
  obtain ⟨MB,hMB,hB'⟩ := hB δ hR N
  refine ⟨MA+MB,add_nonneg hMA hMB,fun p hp => ?_⟩
  have hU : p ∈ U := hR p hp
  have hs : Q2 p := hseg δ hR p hp
  refine ⟨hU,hs,h3 p hU,h4 p hs,h5 p hU,h6 p hs,fun n hn => ⟨?_,?_⟩⟩
  · linarith [hA' n hn p hp]
  · linarith [hB' n hn p hp]

theorem exists_reference_commonRadius_rawAdjointDegree_compact_caps :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ p ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ),
        p ∈ Ω ∧
        (∀ θ ∈ Icc (0:ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) ∧
        ContDiffAt ℝ ∞ Gt p ∧
        ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) => Gt2 z.1 z.2.1 z.2.2) p ∧
        (∀ u : Hi,
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (Gt p u) =
            sphereSobolevShiftedDegreeL (1/2 : ℝ)
              (referenceAdjointThreeHalfRadialFamily
                g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p u) -
            referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
              (sphereSobolevShiftedDegreeL (3/2 : ℝ) u)) ∧
        (∀ u : Hi,
          sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (Gt2 p.1 p.2.1 p.2.2 u) =
            sphereSobolevShiftedDegreeL (1/2:ℝ)
              (secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
                g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (p.1,(p.2.1,t))) p.2.2 u) -
            secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
                g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (p.1,(p.2.1,t))) p.2.2
              (sphereSobolevShiftedDegreeL (3/2:ℝ) u)) ∧
        ∀ n : ℕ, n ≤ N →
          ‖iteratedFDeriv ℝ n Gt p‖ ≤ M ∧
          ‖iteratedFDeriv ℝ n (fun z : ℝ × (R3 × ℝ) => Gt2 z.1 z.2.1 z.2.2) p‖ ≤ M :=
  rawDegreeFinal_combine
    (exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg)
    (rawDegreeFinal_segment g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (contDiffAt_gainedHighFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0)
    (fun (p : ℝ × (R3 × ℝ)) hs => contDiffAt_gainedHighSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2 hs)
    (gainedHighFamily_raw_adjoint_degree_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0)
    (fun (p : ℝ × (R3 × ℝ)) hs => gainedHighSecondRemainder_signed_adjoint_degree_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2 hs)
    (rawDegreeFinal_cap_gainedHigh g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0)
    (rawDegreeFinal_cap_secondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0)

/- Not claimed here (next targets): the primal-constant rewrite of the norm bound,
[a,T] and [A,S] high mixed gains, the actual Pi mixed gains, D_Q, physical coercivity,
Products. -/

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.RawAdjointDegreeGainDraft
