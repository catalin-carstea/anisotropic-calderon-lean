import Calderon.ActualReferenceTwoAngleDegreeCovariance
import Calderon.ActualReferenceTwoAngleDegreeZeroIdentification
import Calderon.SphereSobolevLocalRotationDistributionDerivative
import Calderon.LocalRadialDerivative

/-! The true derivative witness. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceTwoAngleDegreeCommutatorHalfFamily
  referenceRadialDegreeCommutatorHalfFamily referenceTwoAngleDegreeDataInvertibleLocus

def referenceTwoAngleDegreeRotationDerivativeFamily (k l : Fin 3)
    (p : ℝ × (R3 × ℝ)) : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  radialFirstDerivative
    (fun z : (ℝ × (R3 × ℝ)) × ℝ => referenceTwoAngleDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (z.2,z.1)) (p,0)

lemma hasDerivAt_referenceTwoAngleDegreeCommutatorHalfFamily_angle
    (k l : Fin 3) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    HasDerivAt (fun φ : ℝ => referenceTwoAngleDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (φ,p))
      (referenceTwoAngleDegreeRotationDerivativeFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p) 0 := by
  let F : (ℝ × (R3 × ℝ)) × ℝ →
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    fun z => referenceTwoAngleDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (z.2,z.1)
  have hz := referenceTwoAngleDegreeDataInvertibleLocus_zero_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l p hp
  have hC := contDiffAt_referenceTwoAngleDegreeCommutatorHalfFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (0,p) hz
  have hJoint : ContDiffAt ℝ ∞ F (p,0) :=
    hC.comp (p,0) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hc : HasDerivAt (fun φ : ℝ => (p,φ)) (0,1) 0 :=
    (hasDerivAt_const 0 p).prodMk (hasDerivAt_id 0)
  have hd := (hJoint.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc
  simpa only [Function.comp_def,referenceTwoAngleDegreeRotationDerivativeFamily,
    radialFirstDerivative,F] using hd

lemma contDiffAt_referenceTwoAngleDegreeRotationDerivativeFamily
    (k l : Fin 3) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (referenceTwoAngleDegreeRotationDerivativeFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l) p := by
  let F : (ℝ × (R3 × ℝ)) × ℝ →
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    fun z => referenceTwoAngleDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (z.2,z.1)
  have hz := referenceTwoAngleDegreeDataInvertibleLocus_zero_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l p hp
  have hC := contDiffAt_referenceTwoAngleDegreeCommutatorHalfFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (0,p) hz
  have hJoint : ContDiffAt ℝ ∞ F (p,0) :=
    hC.comp (p,0) (contDiffAt_snd.prodMk contDiffAt_fst)
  exact (contDiffAt_radialFirstDerivative F (p,0) hJoint).comp p
    (contDiffAt_id.prodMk contDiffAt_const)

lemma referenceTwoAngleDegreeRotationDerivativeFamily_distribution_witness
    (k l : Fin 3) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (u : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
      (referenceRadialDegreeCommutatorHalfFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
          (sphereSobolevRotationL (3/2:ℝ) k l u) +
       referenceTwoAngleDegreeRotationDerivativeFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)) =
    sphereSobolevRotationL (-(1/2:ℝ)) k l
      (referenceRadialDegreeCommutatorHalfFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)) := by
  let Q : ℝ → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) := fun φ =>
    referenceTwoAngleDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (φ,p)
  let C0 := referenceRadialDegreeCommutatorHalfFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let D := referenceTwoAngleDegreeRotationDerivativeFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
  have hz := referenceTwoAngleDegreeDataInvertibleLocus_zero_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l p hp
  have hNear : ∀ᶠ φ : ℝ in 𝓝 0, (φ,p) ∈ referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l :=
    (continuousAt_id.prodMk continuousAt_const).eventually
      ((isOpen_referenceTwoAngleDegreeDataInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l).mem_nhds hz)
  have hZero := referenceTwoAngleDegreeCommutatorHalfFamily_zero_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p hp
  have hQ : HasDerivAt Q D 0 := hasDerivAt_referenceTwoAngleDegreeCommutatorHalfFamily_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p hp
  have hCov : ∀ᶠ φ : ℝ in 𝓝 0, ∀ f : SphereSobolev (1/2:ℝ),
      Q φ (sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry k l φ) f) =
      sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry k l φ) (C0 f) := by
    filter_upwards [hNear] with φ hφ
    intro f
    exact (referenceTwoAngleDegreeCommutatorHalfFamily_coordinate_covariance
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l φ p hφ f).trans
        (congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
          sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry k l φ) (T f)) hZero)
  have hRaw := sphereSobolev_local_rotation_derivative_distribution
    hO hD (1/2:ℝ) (-(1/2:ℝ)) k l Q C0 D hQ hCov u
  -- Order transport at the operator level: the orders sit in the CLM
  -- types, so `simp` cannot rewrite them; the carriers are the same fixed `lp` space.
  have hInc : ∀ (s r : ℝ) (h₁ : (1/2:ℝ) ≤ s) (h₂ : (1/2:ℝ) ≤ r), s = r →
      sphereSobolevInclusionL s (1/2:ℝ) h₁ = sphereSobolevInclusionL r (1/2:ℝ) h₂ := by
    rintro s r h₁ h₂ rfl
    rfl
  have hRot : ∀ s r : ℝ, s = r →
      sphereSobolevRotationL s k l = sphereSobolevRotationL r k l := by
    rintro s r rfl
    rfl
  have hI : sphereSobolevInclusionL ((1/2:ℝ)+1) (1/2:ℝ) (by norm_num) = I :=
    hInc ((1/2:ℝ)+1) (3/2:ℝ) (by norm_num) (by norm_num) (by norm_num)
  have hR : sphereSobolevRotationL ((1/2:ℝ)+1) k l = sphereSobolevRotationL (3/2:ℝ) k l :=
    hRot ((1/2:ℝ)+1) (3/2:ℝ) (by norm_num)
  have hJ : sphereSobolevInclusionL (-(1/2:ℝ)) ((-(1/2:ℝ))-1) (by norm_num) = J :=
    sphereSobolevInclusionL_eq_of_order_eq_local (-(1/2:ℝ)) ((-(1/2:ℝ))-1) (-(3/2:ℝ))
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
  have hDistribution : sphereSobolevRotationL (-(1/2:ℝ)) k l (C0 (I u)) =
      J (D (I u) + C0 (sphereSobolevRotationL (3/2:ℝ) k l u)) := by
    exact hTransport (C0) (D)
      (sphereSobolevInclusionL ((1/2:ℝ)+1) (1/2:ℝ) (by norm_num)) (I)
      (sphereSobolevInclusionL (-(1/2:ℝ)) ((-(1/2:ℝ))-1) (by norm_num)) (J)
      (sphereSobolevRotationL ((1/2:ℝ)+1) k l) (sphereSobolevRotationL (3/2:ℝ) k l)
      (sphereSobolevRotationL (-(1/2:ℝ)) k l) u hI hJ hR hRaw
  exact (congrArg J (add_comm (C0 (sphereSobolevRotationL (3/2:ℝ) k l u)) (D (I u)))).trans
    hDistribution.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDegreeRotationDerivativeFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.hasDerivAt_referenceTwoAngleDegreeCommutatorHalfFamily_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAngleDegreeRotationDerivativeFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDegreeRotationDerivativeFamily_distribution_witness
