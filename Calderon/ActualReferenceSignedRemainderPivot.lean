import Calderon.ActualReferenceAdjointSignedRemainderCompatibility
import Calderon.ActualReferenceRotationSignedRemainder
import Calderon.SphereSobolevPairingInclusion

/-! Both opposite-index pivots, derived from the lower transpose and
signed high/low coherence. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceSharpRadialTraceSecondRemainder
  referenceLowerRadialTraceSecondRemainder referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily secondTaylorRemainder sphereSobolevInclusionL

lemma referenceRadialSecondRemainder_genuine_pivot_pairings
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (∀ z : SphereSobolev (1/2 : ℝ), ∀ v : SphereSobolev (3/2 : ℝ),
      sphereSobolevDualPairing (-(1/2 : ℝ)) ((referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r) z) (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v) =
        ⟪sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) z,sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) ((secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r) v)⟫_ℝ) ∧
    (∀ z : SphereSobolev (1/2 : ℝ), ∀ v : SphereSobolev (3/2 : ℝ),
      sphereSobolevDualPairing (-(1/2 : ℝ)) ((secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r) z) (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v) =
        ⟪sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) z,sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) ((referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r) v)⟫_ℝ) := by
  let Sh : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    (referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r)
  let Sl : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    (referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r)
  let Th : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    (secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r)
  let Tl : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    (secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r)
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let P : SphereSobolev (-(1/2 : ℝ)) → SphereSobolev (1/2 : ℝ) → ℝ :=
    fun x y => sphereSobolevDualPairing (-(1/2 : ℝ)) x y
  have hS := referenceSharpRadialTraceSecondRemainder_lower_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment
  have hT := referenceAdjointRadialSecondRemainder_high_half_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment
  have hTranspose : Tl = sphereLowerDistributionalTranspose Sl := by
    have hActual := secondTaylorRemainder_referenceAdjointHalfRadial_eq_transpose
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment
    have hSl : Sl = secondTaylorRemainder (fun t : ℝ => referenceLowerRadialEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r := by
      unfold Sl referenceLowerRadialTraceSecondRemainder
      rfl
    exact hActual.trans (congrArg sphereLowerDistributionalTranspose hSl.symm)
  have hReverse : sphereLowerDistributionalTranspose Tl = Sl :=
    (congrArg sphereLowerDistributionalTranspose hTranspose).trans
      (sphereLowerDistributionalTranspose_involutive Sl)
  have hSValue (v : SphereSobolev (3/2 : ℝ)) : Sl (I v) = J (Sh v) := by
    have h := congrArg
      (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T v) hS
    exact (by simpa only [ContinuousLinearMap.comp_apply] using h.symm)
  have hTValue (v : SphereSobolev (3/2 : ℝ)) : Tl (I v) = J (Th v) := by
    have h := congrArg
      (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T v) hT
    exact (by simpa only [ContinuousLinearMap.comp_apply] using h.symm)
  constructor
  · intro z v
    change P (Sl z) (I v) = ⟪Z z,Z (Th v)⟫_ℝ
    have hDual := sphereSobolevDualPairing_lower_distributionalTranspose Sl z (I v)
    have hLow : sphereLowerDistributionalTranspose Sl (I v) = J (Th v) :=
      (congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ]
        SphereSobolev (-(1/2 : ℝ)) => T (I v)) hTranspose.symm).trans (hTValue v)
    calc
      P (Sl z) (I v) = sphereSobolevDualPairing (1/2 : ℝ) (I v) (Sl z) :=
        (real_inner_comm (Sl z) (I v)).symm
      _ = sphereSobolevDualPairing (1/2 : ℝ) z (sphereLowerDistributionalTranspose Sl (I v)) := hDual
      _ = sphereSobolevDualPairing (1/2 : ℝ) z (J (Th v)) :=
        congrArg (sphereSobolevDualPairing (1/2 : ℝ) z) hLow
      _ = P (J (Th v)) z := (real_inner_comm z (J (Th v))).symm
      _ = ⟪Z (Th v),Z z⟫_ℝ :=
        sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num) (Th v) z
      _ = ⟪Z z,Z (Th v)⟫_ℝ := real_inner_comm _ _
  · intro z v
    change P (Tl z) (I v) = ⟪Z z,Z (Sh v)⟫_ℝ
    have hDual := sphereSobolevDualPairing_lower_distributionalTranspose Tl z (I v)
    have hLow : sphereLowerDistributionalTranspose Tl (I v) = J (Sh v) :=
      (congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ]
        SphereSobolev (-(1/2 : ℝ)) => T (I v)) hReverse).trans (hSValue v)
    calc
      P (Tl z) (I v) = sphereSobolevDualPairing (1/2 : ℝ) (I v) (Tl z) :=
        (real_inner_comm (Tl z) (I v)).symm
      _ = sphereSobolevDualPairing (1/2 : ℝ) z (sphereLowerDistributionalTranspose Tl (I v)) := hDual
      _ = sphereSobolevDualPairing (1/2 : ℝ) z (J (Sh v)) :=
        congrArg (sphereSobolevDualPairing (1/2 : ℝ) z) hLow
      _ = P (J (Sh v)) z := (real_inner_comm z (J (Sh v))).symm
      _ = ⟪Z (Sh v),Z z⟫_ℝ :=
        sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num) (Sh v) z
      _ = ⟪Z z,Z (Sh v)⟫_ℝ := real_inner_comm _ _

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialSecondRemainder_genuine_pivot_pairings
