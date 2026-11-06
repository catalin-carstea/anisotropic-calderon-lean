import Calderon.ActualReferenceDegreeRotationWitness
import Calderon.SphereSobolevRotationCommutatorHighLift
import Calderon.LowerDistributionalTransposeCovariance
import Calderon.ActualAdjointMovingBoundaryFamilyFoundation

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

local instance rawAdjointDegreeHalfCompleteSpace : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance rawAdjointDegreeNegativeCompleteSpace :
    CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local notation "Csharp" => referenceRadialDegreeCommutatorHalfFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Wsharp" => referenceTwoAngleDegreeRotationDerivativeFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
local notation "Qsharp" => referenceTwoAngleDegreeCommutatorHalfFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

/-! ## Same-map normed outer view

The existing `sphereLowerDistributionalTransposeL` is packaged with the topological CLM data
on its carrier, which `hasFDerivAt`/`contDiff` do not accept. Proof-locally we repackage the
SAME pointwise map `sphereLowerDistributionalTranspose` with `LinearMap.mkContinuous` (bound
`1` from `adjoint.norm_map`), exactly as in `Calderon.NativeLowerTransposeDerivative`;
`hApply` is the pointwise link to the original map. -/

private lemma rawDegreeLowerTranspose_hasDerivAt
    (F : ℝ → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))))
    (F' : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (r : ℝ) (hF : HasDerivAt F F' r) :
    HasDerivAt (fun t => sphereLowerDistributionalTranspose (F t))
      (sphereLowerDistributionalTranspose F') r := by
  letI : NormedAddCommGroup
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    ContinuousLinearMap.toNormedSpace
  let t : (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) →ₗ[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    { toFun := sphereLowerDistributionalTranspose
      map_add' := fun A A' => by
        have h := sphereLowerDistributionalTransposeL.map_add A A'
        simpa only [sphereLowerDistributionalTransposeL_apply] using h
      map_smul' := fun c A => by
        have h := sphereLowerDistributionalTransposeL.map_smul c A
        simpa only [sphereLowerDistributionalTransposeL_apply,RingHom.id_apply] using h }
  have hBound : ∀ A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)),
      ‖t A‖ ≤ (1 : ℝ) * ‖A‖ := by
    intro A
    have hAdj : t A = ContinuousLinearMap.adjoint A := by
      change sphereLowerDistributionalTranspose A = ContinuousLinearMap.adjoint A
      unfold sphereLowerDistributionalTranspose sphereHalfDualCarrierEquiv
      apply ContinuousLinearMap.ext
      intro u
      rfl
    have hNorm : ‖t A‖ ≤ ‖A‖ :=
      (congrArg (fun S : SphereSobolev (1/2 : ℝ) →L[ℝ]
        SphereSobolev (-(1/2 : ℝ)) => ‖S‖) hAdj).le.trans
          (ContinuousLinearMap.adjoint.norm_map A).le
    simpa only [one_mul] using hNorm
  let T : (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) →L[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    LinearMap.mkContinuous
      (E := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
      (F := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
      t (1 : ℝ) hBound
  have hApply (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :
      T A = sphereLowerDistributionalTranspose A := rfl
  have hT := T.hasFDerivAt.comp_hasDerivAt r hF
  have hEq : (fun t => sphereLowerDistributionalTranspose (F t)) =ᶠ[𝓝 r]
      (fun t => T (F t)) :=
    Filter.Eventually.of_forall (fun t => (hApply (F t)).symm)
  exact (hT.congr_of_eventuallyEq hEq).congr_deriv (hApply F')

private lemma rawDegreeLowerTranspose_neg_contDiffAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))))
    (x : X) (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (fun y => -sphereLowerDistributionalTranspose (F y)) x := by
  letI : NormedAddCommGroup
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    ContinuousLinearMap.toNormedSpace
  let t : (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) →ₗ[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    { toFun := sphereLowerDistributionalTranspose
      map_add' := fun A A' => by
        have h := sphereLowerDistributionalTransposeL.map_add A A'
        simpa only [sphereLowerDistributionalTransposeL_apply] using h
      map_smul' := fun c A => by
        have h := sphereLowerDistributionalTransposeL.map_smul c A
        simpa only [sphereLowerDistributionalTransposeL_apply,RingHom.id_apply] using h }
  have hBound : ∀ A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)),
      ‖t A‖ ≤ (1 : ℝ) * ‖A‖ := by
    intro A
    have hAdj : t A = ContinuousLinearMap.adjoint A := by
      change sphereLowerDistributionalTranspose A = ContinuousLinearMap.adjoint A
      unfold sphereLowerDistributionalTranspose sphereHalfDualCarrierEquiv
      apply ContinuousLinearMap.ext
      intro u
      rfl
    have hNorm : ‖t A‖ ≤ ‖A‖ :=
      (congrArg (fun S : SphereSobolev (1/2 : ℝ) →L[ℝ]
        SphereSobolev (-(1/2 : ℝ)) => ‖S‖) hAdj).le.trans
          (ContinuousLinearMap.adjoint.norm_map A).le
    simpa only [one_mul] using hNorm
  let T : (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) →L[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
    LinearMap.mkContinuous
      (E := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
      (F := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
      t (1 : ℝ) hBound
  have hApply (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :
      T A = sphereLowerDistributionalTranspose A := rfl
  have hT := (T.contDiff.contDiffAt.comp x hF).neg
  have hEq : (fun y => -sphereLowerDistributionalTranspose (F y)) =ᶠ[𝓝 x]
      (fun y => -T (F y)) :=
    Filter.Eventually.of_forall (fun y => congrArg Neg.neg (hApply (F y)).symm)
  exact hT.congr_of_eventuallyEq hEq

/-! ## Negative-transpose low families and the explicit high lift -/

def lowFamily (p : ℝ × (R3 × ℝ)) : Half →L[ℝ] NegH :=
  -sphereLowerDistributionalTranspose (Csharp p)

def rotationDerivativeFamily (k l : Fin 3) (p : ℝ × (R3 × ℝ)) : Half →L[ℝ] NegH :=
  -sphereLowerDistributionalTranspose (Wsharp k l p)

local notation "Ct" => lowFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Wt" => rotationDerivativeFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0

lemma distribution_witness (k l : Fin 3) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ Ω) (u : Hi) :
    sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
      (Ct p (sphereSobolevRotationL (3/2 : ℝ) k l u) +
       Wt k l p (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)) =
    sphereSobolevRotationL (-(1/2 : ℝ)) k l
      (Ct p (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)) := by
  letI : NormedAddCommGroup (Half →L[ℝ] NegH) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (Half →L[ℝ] NegH) := ContinuousLinearMap.toNormedSpace
  let Q : ℝ → Half →L[ℝ] NegH := fun φ =>
    -sphereLowerDistributionalTranspose (Qsharp k l (φ,p))
  have hQsharp := hasDerivAt_referenceTwoAngleDegreeCommutatorHalfFamily_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p hp
  have hQt : HasDerivAt (fun φ : ℝ => -sphereLowerDistributionalTranspose (Qsharp k l (φ,p)))
      (-sphereLowerDistributionalTranspose (Wsharp k l p)) (0 : ℝ) :=
    (rawDegreeLowerTranspose_hasDerivAt
      (fun φ : ℝ => Qsharp k l (φ,p)) (Wsharp k l p) (0 : ℝ) hQsharp).neg
  -- `Q φ = -transpose (Qsharp k l (φ,p))` and `Wt k l p = -transpose (Wsharp k l p)` by definition.
  have hQ : HasDerivAt Q (Wt k l p) 0 := by
    simpa only [Q,rotationDerivativeFamily,Function.comp_def] using hQt
  have hz := referenceTwoAngleDegreeDataInvertibleLocus_zero_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l p hp
  have hNear : ∀ᶠ φ : ℝ in 𝓝 0, (φ,p) ∈ referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l :=
    (continuousAt_id.prodMk continuousAt_const).eventually
      ((isOpen_referenceTwoAngleDegreeDataInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l).mem_nhds hz)
  have hZero := referenceTwoAngleDegreeCommutatorHalfFamily_zero_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p hp
  have hCov : ∀ᶠ φ : ℝ in 𝓝 0, ∀ f : Half,
      Q φ (sphereSobolevOrthogonalPullbackL (1/2 : ℝ)
        (coordinateRotationIsometry k l φ) f) =
      sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ))
        (coordinateRotationIsometry k l φ) (Ct p f) := by
    filter_upwards [hNear] with φ hφ
    have hSharp : (Qsharp k l (φ,p)).comp
        (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) (coordinateRotationIsometry k l φ)) =
      (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ))
        (coordinateRotationIsometry k l φ)).comp (Csharp p) := by
      apply ContinuousLinearMap.ext
      intro f
      exact (referenceTwoAngleDegreeCommutatorHalfFamily_coordinate_covariance
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l φ p hφ f).trans
          (congrArg (fun T : Half →L[ℝ] NegH =>
            sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ))
              (coordinateRotationIsometry k l φ) (T f)) hZero)
    have ht := neg_lowerDistributionalTranspose_orthogonal_covariance
      (coordinateRotationIsometry k l φ) (Qsharp k l (φ,p)) (Csharp p) hSharp
    intro f
    simpa only [Q,lowFamily,ContinuousLinearMap.comp_apply] using
      congrArg (fun T : Half →L[ℝ] NegH => T f) ht
  have hRaw := sphereSobolev_local_rotation_derivative_distribution
    hO hD (1/2 : ℝ) (-(1/2 : ℝ)) k l Q (Ct p) (Wt k l p) hQ hCov u
  -- Order transport at the operator level: the orders sit in the CLM
  -- types, so `simp` cannot rewrite them; the carriers are the same fixed `lp` space.
  have hInc : ∀ (s r : ℝ) (h₁ : (1/2 : ℝ) ≤ s) (h₂ : (1/2 : ℝ) ≤ r), s = r →
      sphereSobolevInclusionL s (1/2 : ℝ) h₁ = sphereSobolevInclusionL r (1/2 : ℝ) h₂ := by
    rintro s r h₁ h₂ rfl
    rfl
  have hRot : ∀ s r : ℝ, s = r →
      sphereSobolevRotationL s k l = sphereSobolevRotationL r k l := by
    rintro s r rfl
    rfl
  have hI : sphereSobolevInclusionL ((1/2 : ℝ)+1) (1/2 : ℝ) (by norm_num) =
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) :=
    hInc ((1/2 : ℝ)+1) (3/2 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hR : sphereSobolevRotationL ((1/2 : ℝ)+1) k l = sphereSobolevRotationL (3/2 : ℝ) k l :=
    hRot ((1/2 : ℝ)+1) (3/2 : ℝ) (by norm_num)
  have hJ : sphereSobolevInclusionL (-(1/2 : ℝ)) ((-(1/2 : ℝ))-1) (by norm_num) =
      sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num) :=
    sphereSobolevInclusionL_eq_of_order_eq_local (-(1/2 : ℝ)) ((-(1/2 : ℝ))-1) (-(3/2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  have hTransport
      (A B : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
      (i0 i1 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
      (j0 j1 : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(3/2:ℝ)))
      (r0 r1 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
      (S : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(3/2:ℝ)))
      (x : SphereSobolev (3/2:ℝ)) (hi : i0 = i1) (hj : j0 = j1) (hr : r0 = r1)
      (hh : S (A (i0 x)) = j0 (B (i0 x) + A (r0 x))) :
      S (A (i1 x)) = j1 (B (i1 x) + A (r1 x)) := by
    cases hi
    cases hj
    cases hr
    exact hh
  have hDistribution : sphereSobolevRotationL (-(1/2 : ℝ)) k l
      (Ct p (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)) =
    sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
      (Wt k l p (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) +
       Ct p (sphereSobolevRotationL (3/2 : ℝ) k l u)) := by
    exact hTransport (Ct p) (Wt k l p)
      (sphereSobolevInclusionL ((1/2:ℝ)+1) (1/2:ℝ) (by norm_num)) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      (sphereSobolevInclusionL (-(1/2:ℝ)) ((-(1/2:ℝ))-1) (by norm_num)) (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num))
      (sphereSobolevRotationL ((1/2:ℝ)+1) k l) (sphereSobolevRotationL (3/2:ℝ) k l)
      (sphereSobolevRotationL (-(1/2:ℝ)) k l) u hI hJ hR hRaw
  exact (congrArg (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num))
    (add_comm (Ct p (sphereSobolevRotationL (3/2 : ℝ) k l u))
      (Wt k l p (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)))).trans
        hDistribution.symm

def gainedHighFamily (p : ℝ × (R3 × ℝ)) : Hi →L[ℝ] Half :=
  sphereSobolevRotationCommutatorHighLiftL (Ct p) (fun k l => Wt k l p)

local notation "Gt" => gainedHighFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0

lemma gainedHighFamily_lower_compatibility (p : ℝ × (R3 × ℝ)) (hp : p ∈ Ω) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp (Gt p) =
      (Ct p).comp (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) :=
  sphereSobolevRotationCommutatorHighLiftL_lower_compatibility _ _
    (fun u k l => distribution_witness
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p hp u)

lemma norm_gainedHighFamily_le (p : ℝ × (R3 × ℝ)) :
    ‖Gt p‖ ≤ 19*‖Ct p‖ + Real.sqrt 2*∑ k : Fin 3, ∑ l : Fin 3, ‖Wt k l p‖ :=
  norm_sphereSobolevRotationCommutatorHighLiftL_le _ _

include hreg in
lemma contDiffAt_lowFamily (p : ℝ × (R3 × ℝ)) (hp : p ∈ Ω) :
    ContDiffAt ℝ ∞ Ct p := by
  have hC := contDiffAt_referenceRadialDegreeCommutatorHalfFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp
  -- `Ct = fun x => -transpose (Csharp x)` by definition of `lowFamily`.
  exact rawDegreeLowerTranspose_neg_contDiffAt
    (fun x : ℝ × (R3 × ℝ) => Csharp x) p hC

lemma contDiffAt_rotationDerivativeFamily (k l : Fin 3) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ Ω) : ContDiffAt ℝ ∞ (Wt k l) p := by
  have hW := contDiffAt_referenceTwoAngleDegreeRotationDerivativeFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p hp
  -- `Wt k l = fun x => -transpose (Wsharp k l x)` by definition of `rotationDerivativeFamily`.
  exact rawDegreeLowerTranspose_neg_contDiffAt
    (fun x : ℝ × (R3 × ℝ) => Wsharp k l x) p hW

lemma contDiffAt_gainedHighFamily (p : ℝ × (R3 × ℝ)) (hp : p ∈ Ω) :
    ContDiffAt ℝ ∞ Gt p := by
  have hC := contDiffAt_lowFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp
  have hW (k l : Fin 3) := contDiffAt_rotationDerivativeFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p hp
  unfold gainedHighFamily sphereSobolevRotationCommutatorHighLiftL
  apply ContDiffAt.add
  · exact contDiffAt_const.clm_comp (hC.clm_comp contDiffAt_const)
  · apply ContDiffAt.sum
    intro k hk
    apply ContDiffAt.sum
    intro l hl
    exact contDiffAt_const.clm_comp
      ((hC.clm_comp contDiffAt_const).add ((hW k l).clm_comp contDiffAt_const))

/-! ## RAW actual adjoint radial degree graph (Theorem R)

For p in the SAME original locus: J (Gt p u) = Bhalf (Th p u) - Tl p (Bhigh u), where
Th/Tl are the actual raw adjoint radial families. The proof tests against the raw pivot
duality of the actual lower radial endpoint and uses density of Hi in Half. It does not
use the signed remainder graph. -/


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.RawAdjointDegreeGainDraft
