import Calderon.ActualReferenceTwoAngleDegreeExtraction
import Calderon.ActualReferenceRotationUpperCovariance
import Calderon.SphereSobolevDenseEndpointCovariance
import Calderon.SphereSobolevShiftedDegreeOrthogonalCovariance

/-! Full upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-actual-degree-covariance-v129.md. Concrete actual covariance. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceTwoAngleSharpRadialTraceFamily
  referenceRotationSharpRadialTraceFamily referenceSharpRadialTraceFamily
  referenceTwoAngleDegreeCommutatorHalfFamily referenceTwoAngleLowerRadialEndpointFamily
  sphereSobolevInclusionL sphereSobolevOrthogonalPullbackL sphereSobolevShiftedDegreeL

lemma referenceTwoAngleDegreeData_high_endpoint_covariance
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k l : Fin 3) (φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hp : (φ,p) ∈ referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l)
    (u : SphereSobolev (3/2:ℝ)) :
    referenceTwoAngleSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,(φ,p))
      (sphereSobolevOrthogonalPullbackL (3/2:ℝ) (coordinateRotationIsometry k l φ) u) =
    sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry k l φ)
      (referenceTwoAngleSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,(0,p)) u) := by
  have hPoint : (0,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l :=
    Set.mem_iInter.mp hp (0,0)
  have hOrig := hPoint.1.2.2
  have hRot : (referenceRotationStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p)).IsInvertible := by
    have h := hPoint.2
    change (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 0 k l (0,(φ,p))).IsInvertible at h
    rw [referenceTwoAngleStrongDirichletFamily_zero_outer_angle] at h
    exact h
  have hPhi := referenceTwoAngleSharpRadialTraceFamily_zero_outer_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l φ p
  have hZero := (referenceTwoAngleSharpRadialTraceFamily_zero_outer_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l 0 p).trans
      (referenceRotationSharpRadialTraceFamily_zero_angle
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l p)
  have hNative := referenceRotationSharpRadialTraceFamily_coordinate_covariance
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l φ p hOrig.1 hOrig.2.1 hRot u
  exact (congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) =>
    T (sphereSobolevOrthogonalPullbackL (3/2:ℝ) (coordinateRotationIsometry k l φ) u)) hPhi).trans
      (hNative.trans (congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) =>
        sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry k l φ) (T u)) hZero.symm))

lemma referenceTwoAngleDegreeCommutatorHalfFamily_coordinate_covariance
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k l : Fin 3) (φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hp : (φ,p) ∈ referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l)
    (f : SphereSobolev (1/2:ℝ)) :
    referenceTwoAngleDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (φ,p)
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry k l φ) f) =
    sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry k l φ)
      (referenceTwoAngleDegreeCommutatorHalfFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (0,p) f) := by
  have hPoint : (0,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l :=
    Set.mem_iInter.mp hp (0,0)
  have hOrig := hPoint.1.2.2
  have hp0 := referenceTwoAngleDegreeDataInvertibleLocus_zero_angle
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l p hOrig
  have hPoint0 : (0,(0,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l :=
    Set.mem_iInter.mp hp0 (0,0)
  let e := coordinateRotationIsometry k l φ
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let S0 := referenceTwoAngleSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,(0,p))
  let Sphi := referenceTwoAngleSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,(φ,p))
  let A0 := referenceTwoAngleLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,(0,p))
  let Aphi := referenceTwoAngleLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,(φ,p))
  let C0 := referenceTwoAngleDegreeCommutatorHalfFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (0,p)
  let Cphi := referenceTwoAngleDegreeCommutatorHalfFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (φ,p)
  let Uh := sphereSobolevOrthogonalPullbackL (1/2:ℝ) e
  let Um := sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e
  let UH := sphereSobolevOrthogonalPullbackL (3/2:ℝ) e
  let Bh := sphereSobolevShiftedDegreeL (1/2:ℝ)
  let BH := sphereSobolevShiftedDegreeL (3/2:ℝ)
  have hA0 (u : SphereSobolev (3/2:ℝ)) : A0 (I u) = J (S0 u) :=
    (congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u)
      (referenceTwoAngleSharpRadialTraceFamily_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,(0,p))
          hOrig.2.2 hOrig.2.1 hPoint0.2)).symm
  have hAphi (u : SphereSobolev (3/2:ℝ)) : Aphi (I u) = J (Sphi u) :=
    (congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u)
      (referenceTwoAngleSharpRadialTraceFamily_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,(φ,p))
          hOrig.2.2 hOrig.2.1 hPoint.2)).symm
  have hUpper (u : SphereSobolev (3/2:ℝ)) : Sphi (UH u) = Uh (S0 u) :=
    referenceTwoAngleDegreeData_high_endpoint_covariance
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l φ p hp u
  have hLower (v : SphereSobolev (1/2:ℝ)) : Aphi (Uh v) = Um (A0 v) :=
    lowerEndpoint_orthogonal_covariance_of_upper e A0 Aphi S0 Sphi hA0 hAphi hUpper v
  have hC0 (u : SphereSobolev (3/2:ℝ)) : C0 (I u) = Bh (S0 u) - A0 (BH u) :=
    referenceTwoAngleDegreeCommutatorHalfFamily_raw_high_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (0,p) hp0 u
  have hCphi (u : SphereSobolev (3/2:ℝ)) : Cphi (I u) = Bh (Sphi u) - Aphi (BH u) :=
    referenceTwoAngleDegreeCommutatorHalfFamily_raw_high_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l (φ,p) hp u
  have hPullbackOrder (s t : ℝ) (hst : s = t) :
      (sphereSobolevOrthogonalPullbackL s e : SphereSobolev 0 →L[ℝ] SphereSobolev 0) =
        (sphereSobolevOrthogonalPullbackL t e : SphereSobolev 0 →L[ℝ] SphereSobolev 0) := by
    cases hst
    rfl
  have hBh (v : SphereSobolev (1/2:ℝ)) : Bh (Uh v) = Um (Bh v) := by
    have h := sphereSobolevShiftedDegreeL_orthogonalPullback_apply (1/2:ℝ) e v
    exact h.trans (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => T (Bh v))
      (hPullbackOrder ((1/2:ℝ)-1) (-(1/2:ℝ)) (by norm_num)))
  have hBH (u : SphereSobolev (3/2:ℝ)) : BH (UH u) = Uh (BH u) := by
    have h := sphereSobolevShiftedDegreeL_orthogonalPullback_apply (3/2:ℝ) e u
    exact h.trans (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => T (BH u))
      (hPullbackOrder ((3/2:ℝ)-1) (1/2:ℝ) (by norm_num)))
  apply denseRange_clm_apply_eq I
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (Cphi.comp Uh) (Um.comp C0)
  intro u
  have hInput : I (UH u) = Uh (I u) :=
    sphereSobolevInclusionL_orthogonalPullback_apply (3/2:ℝ) (1/2:ℝ) (by norm_num) e u
  calc
    _ = Cphi (I (UH u)) := congrArg Cphi hInput.symm
    _ = Bh (Sphi (UH u)) - Aphi (BH (UH u)) := hCphi (UH u)
    _ = Bh (Uh (S0 u)) - Aphi (Uh (BH u)) :=
      congrArg₂ (fun x y : SphereSobolev (1/2:ℝ) => Bh x - Aphi y) (hUpper u) (hBH u)
    _ = Um (Bh (S0 u)) - Um (A0 (BH u)) :=
      congrArg₂ (fun x y : SphereSobolev (-(1/2:ℝ)) => x-y) (hBh (S0 u)) (hLower (BH u))
    _ = Um (Bh (S0 u) - A0 (BH u)) := (Um.map_sub _ _).symm
    _ = _ := congrArg Um (hC0 u).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDegreeData_high_endpoint_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDegreeCommutatorHalfFamily_coordinate_covariance
