import Calderon.ActualRawAdjointDegreeCore
import Calderon.NativeRadialJetTranspose
import Calderon.SphereSobolevPairingInclusion
import Mathlib.Topology.DenseEmbedding

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

lemma gainedHighFamily_raw_adjoint_degree_graph (p : ℝ × (R3 × ℝ)) (hp : p ∈ Ω)
    (u : Hi) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (Gt p u) =
      sphereSobolevShiftedDegreeL (1/2 : ℝ)
        (referenceAdjointThreeHalfRadialFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p u) -
      referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (sphereSobolevShiftedDegreeL (3/2 : ℝ) u) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Z := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Bhigh := sphereSobolevShiftedDegreeL (3/2 : ℝ)
  let Bhalf := sphereSobolevShiftedDegreeL (1/2 : ℝ)
  let C0 := referenceRadialDegreeCommutatorHalfFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Sh := referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Sl := referenceLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Th := referenceAdjointThreeHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Tl := referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let P : NegH → Half → ℝ := fun v z => sphereSobolevDualPairing (-(1/2 : ℝ)) v z
  let Q : Half → NegH → ℝ := fun z v => sphereSobolevDualPairing (1/2 : ℝ) z v
  have hFlip (v : NegH) (z : Half) : Q z v = P v z := (real_inner_comm z v).symm
  have hSub (z : Half) (v₁ v₂ : NegH) : Q z (v₁-v₂) = Q z v₁-Q z v₂ :=
    inner_sub_right z v₁ v₂
  have hBTranspose : sphereLowerDistributionalTranspose Bhalf = Bhalf :=
    sphereLowerDistributionalTranspose_shiftedDegree_half
  have hDegree (v : Hi) : J (Bhigh v) = Bhalf (I v) :=
    congrArg (fun A : Hi →L[ℝ] NegH => A v) sphereSobolevShiftedDegree_high_half_compatibility
  have hBPair (v : Hi) (z : Half) : Q (I v) (Bhalf z) = ⟪Z (Bhigh v),Z z⟫_ℝ := by
    calc
      _ = Q z (sphereLowerDistributionalTranspose Bhalf (I v)) :=
        sphereSobolevDualPairing_lower_distributionalTranspose Bhalf z (I v)
      _ = Q z (Bhalf (I v)) := congrArg (fun A => Q z (A (I v))) hBTranspose
      _ = Q z (J (Bhigh v)) := congrArg (Q z) (hDegree v).symm
      _ = P (J (Bhigh v)) z := hFlip _ _
      _ = _ := sphereSobolevDualPairing_inclusion_eq_inner_zero
        (1/2 : ℝ) (by norm_num) (Bhigh v) z
  -- actual raw sharp lower compatibility on the SAME locus
  have hSharp (v : Hi) : J (Sh v) = Sl (I v) :=
    congrArg (fun A : Hi →L[ℝ] NegH => A v)
      (referenceSharpRadialTraceFamily_lower_compatibility_on_locus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp)
  -- actual raw adjoint high/half compatibility (weak-invertibility component of p ∈ Ω)
  have hAdj (v : Hi) : J (Th v) = Tl (I v) :=
    congrArg (fun A : Hi →L[ℝ] NegH => A v)
      (referenceAdjointRadialEndpointFamily_high_half_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p hp.2.1)
  -- actual raw pivot duality of the lower radial endpoint
  have hDual (f v : Half) : Q v (Sl f) = Q f (Tl v) :=
    sphereSobolevDualPairing_referenceLowerRadial_adjoint
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD p hp.2.1 f v
  have hSPair (z : Half) (v : Hi) : Q (I v) (Sl z) = ⟪Z z,Z (Th v)⟫_ℝ := by
    calc
      _ = Q z (Tl (I v)) := hDual z (I v)
      _ = Q z (J (Th v)) := congrArg (Q z) (hAdj v).symm
      _ = P (J (Th v)) z := hFlip _ _
      _ = ⟪Z (Th v),Z z⟫_ℝ :=
        sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num) (Th v) z
      _ = _ := real_inner_comm _ _
  have hTPair (z : Half) (v : Hi) : Q (I v) (Tl z) = ⟪Z z,Z (Sh v)⟫_ℝ := by
    calc
      _ = Q z (Sl (I v)) := (hDual (I v) z).symm
      _ = Q z (J (Sh v)) := congrArg (Q z) (hSharp v).symm
      _ = P (J (Sh v)) z := hFlip _ _
      _ = ⟪Z (Sh v),Z z⟫_ℝ :=
        sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num) (Sh v) z
      _ = _ := real_inner_comm _ _
  -- actual raw high graph of the degree commutator on the SAME locus
  have hRaw (v : Hi) : C0 (I v) = Bhalf (Sh v) - Sl (Bhigh v) := by
    have hOriginal := referenceRadialDegreeCommutatorHalfFamily_high_graph_on_locus
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp v
    have hValue : referenceRadialDegreeCommutatorHighL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p v =
        Bhalf (Sh v) - Sl (Bhigh v) := by
      simp only [referenceRadialDegreeCommutatorHighL, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.comp_apply, Bhalf, Sh, Sl, Bhigh]
    exact hOriginal.trans hValue
  have hTest (v : Hi) :
      Q (I v) (sphereLowerDistributionalTranspose C0 (I u)) =
        Q (I v) (Tl (Bhigh u)-Bhalf (Th u)) := by
    calc
      _ = Q (I u) (C0 (I v)) :=
        (sphereSobolevDualPairing_lower_distributionalTranspose C0 (I v) (I u)).symm
      _ = Q (I u) (Bhalf (Sh v)-Sl (Bhigh v)) := congrArg (Q (I u)) (hRaw v)
      _ = Q (I u) (Bhalf (Sh v))-Q (I u) (Sl (Bhigh v)) := hSub _ _ _
      _ = ⟪Z (Bhigh u),Z (Sh v)⟫_ℝ-⟪Z (Bhigh v),Z (Th u)⟫_ℝ :=
        congrArg₂ (fun x y : ℝ => x-y) (hBPair u (Sh v)) (hSPair (Bhigh v) u)
      _ = Q (I v) (Tl (Bhigh u))-Q (I v) (Bhalf (Th u)) :=
        congrArg₂ (fun x y : ℝ => x-y) (hTPair (Bhigh u) v).symm (hBPair v (Th u)).symm
      _ = _ := (hSub _ _ _).symm
  let Ltest : Half → ℝ := fun z => Q z (sphereLowerDistributionalTranspose C0 (I u))
  let Rtest : Half → ℝ := fun z => Q z (Tl (Bhigh u)-Bhalf (Th u))
  have hLtest : Continuous Ltest := continuous_id.inner continuous_const
  have hRtest : Continuous Rtest := continuous_id.inner continuous_const
  have hTests : Ltest ∘ I = Rtest ∘ I := funext hTest
  have hAll : Ltest = Rtest :=
    (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).equalizer
      hLtest hRtest hTests
  have hPositive : sphereLowerDistributionalTranspose C0 (I u) =
      Tl (Bhigh u)-Bhalf (Th u) :=
    sphereSobolev_eq_of_dualPairing_eq (1/2 : ℝ) _ _ (fun z => congrFun hAll z)
  have hLow : J (Gt p u) = Ct p (I u) :=
    congrArg (fun A : Hi →L[ℝ] NegH => A u)
      (gainedHighFamily_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp)
  calc
    J (Gt p u) = Ct p (I u) := hLow
    _ = -(sphereLowerDistributionalTranspose C0 (I u)) := rfl
    _ = -(Tl (Bhigh u)-Bhalf (Th u)) := congrArg (fun z : NegH => -z) hPositive
    _ = Bhalf (Th u)-Tl (Bhigh u) := neg_sub _ _

/-! ## Signed second Taylor remainder and its exact graph (MATHEMATICS.md §4)

q and y are frozen inside the signed integral; only the radial variable moves. -/

/- Negation commutes with the signed remainder unconditionally, because
`deriv (-F) = -deriv F` holds pointwise. -/

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.RawAdjointDegreeGainDraft
