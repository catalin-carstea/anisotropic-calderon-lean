import Calderon.ActualHorizontalSobolevConnection
import Calderon.ActualAdjointMovingBoundaryFamilies

/-! The total actual adjoint families, their compatible horizontal domain and the
product rule. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ConformalDepth RadiusProfile ReferenceDensityBounds NormalCoordinatesFrame

attribute [local irreducible] referenceHighAdjointMovingBoundaryActionFamily
  referenceLowerAdjointMovingBoundaryActionFamily referenceHighAdjointMovingBoundaryAction
  referenceLowerAdjointMovingBoundaryAction referenceHighHorizontalAction referenceLowerHorizontalAction
  referenceMetricGramFrame referenceHighHorizontalAngularL referenceLowerHorizontalAngularL

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

theorem referenceAdjointMovingBoundaryActionFamily_high_lower_compatibility
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i) =
    (referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hHigh := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => Iout.comp A)
    (referenceHighAdjointMovingBoundaryActionFamily_eq g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i hInv)
  have hLow := congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A.comp Iin)
    (referenceLowerAdjointMovingBoundaryActionFamily_eq g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i hInv hWeak)
  exact hHigh.trans ((referenceAdjointMovingBoundaryAction_high_lower_compatibility
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R y i hInv hWeak).trans hLow.symm)

def referenceHighDensityFirstAction (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3) : SphereSobolev (1/2 : ℝ) :=
  referenceHighHorizontalAction g L q u y i +
    referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i (u y)

def referenceLowerDensityFirstAction (q : ℝ) (R : R3 → ℝ)
    (v : R3 → SphereSobolev (1/2 : ℝ)) (y : R3) (i : Fin 3) : SphereSobolev (-(1/2 : ℝ)) :=
  referenceLowerHorizontalAction g L q v y i +
    referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i (v y)

theorem referenceDensityFirstAction_high_lower_compatibility
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (hu : DifferentiableAt ℝ u y) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i) =
    referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
      (fun x => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u x)) y i := by
  have hHorizontal := referenceHorizontalAction_high_lower_compatibility g L q u y i hu
  have hAdjoint := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A (u y))
    (referenceAdjointMovingBoundaryActionFamily_high_lower_compatibility
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R y i hInv hWeak)
  have hCombined := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b)
    hHorizontal hAdjoint
  simpa only [referenceHighDensityFirstAction,referenceLowerDensityFirstAction,
    ContinuousLinearMap.comp_apply,map_add] using hCombined

theorem contDiffAt_referenceHighDensityFirstAction
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3)
    (hu : ContDiffAt ℝ ∞ u y) (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun x => referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x i) y := by
  have hHorizontal := contDiffAt_referenceHighHorizontalAction g hg L q u y i hu
  have hC := (contDiffAt_referenceHighAdjointMovingBoundaryActionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg R (q,y) i hR hr hInv hp).comp y
      (contDiffAt_const.prodMk contDiffAt_id)
  exact hHorizontal.add (hC.clm_apply hu)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic SmoothMetricFrame MovingFrameConnection
attribute [local irreducible] referenceMetricGramFrame referenceHighHorizontalAngularL
  referenceLowerHorizontalAngularL

theorem referenceLowerHorizontalAction_add
    (g : MatrixField) (L q : ℝ) (u v : R3 → SphereSobolev (1/2 : ℝ))
    (y : R3) (i : Fin 3) (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    referenceLowerHorizontalAction g L q (fun x => u x+v x) y i =
    referenceLowerHorizontalAction g L q u y i + referenceLowerHorizontalAction g L q v y i := by
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let e := referenceMetricGramFrame g L (q,y) i
  let Ω := referenceLowerHorizontalAngularL g L q y i
  have hD := congrArg (fun A : R3 →L[ℝ] SphereSobolev (1/2 : ℝ) => Iout (A e))
    (fderiv_add hu hv)
  have hD' : Iout (fderiv ℝ (fun x => u x+v x) y e) =
      Iout (fderiv ℝ u y e) + Iout (fderiv ℝ v y e) := by
    simpa only [Pi.add_def,ContinuousLinearMap.add_apply,map_add] using hD
  have hCombined := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b)
    hD' (map_add Ω (u y) (v y))
  calc
    _ = (Iout (fderiv ℝ u y e) + Iout (fderiv ℝ v y e)) + (Ω (u y)+Ω (v y)) := hCombined
    _ = _ := by simp only [referenceLowerHorizontalAction,Iout,e,Ω]; abel

theorem referenceLowerHorizontalAction_clm_apply
    (g : MatrixField) (L q : ℝ)
    (F : R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3)
    (hF : DifferentiableAt ℝ F y) (hu : DifferentiableAt ℝ u y) :
    referenceLowerHorizontalAction g L q (fun x => F x (u x)) y i =
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (F y (fderiv ℝ u y (referenceMetricGramFrame g L (q,y) i))) +
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      ((fderiv ℝ F y (referenceMetricGramFrame g L (q,y) i)) (u y)) +
    referenceLowerHorizontalAngularL g L q y i (F y (u y)) := by
  have hD := congrArg (fun A : R3 →L[ℝ] SphereSobolev (1/2 : ℝ) =>
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (A (referenceMetricGramFrame g L (q,y) i))) (fderiv_clm_apply hF hu)
  have hCombined := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
    z + referenceLowerHorizontalAngularL g L q y i (F y (u y))) hD
  simpa only [referenceLowerHorizontalAction,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,map_add] using hCombined

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMovingBoundaryActionFamily_high_lower_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighDensityFirstAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerDensityFirstAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityFirstAction_high_lower_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighDensityFirstAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerHorizontalAction_add
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerHorizontalAction_clm_apply
