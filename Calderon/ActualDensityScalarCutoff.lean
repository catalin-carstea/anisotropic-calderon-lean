import Calderon.ActualPhysicalDensityOperator
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ConformalDepth RadiusProfile ReferenceDensityBounds ActualNormalizedSecondMetricDrift
attribute [local irreducible] referenceHighDensityFirstAction referenceLowerDensityFirstAction
  referenceHighHorizontalAction referenceLowerHorizontalAction
  referenceMetricGramFrame referenceFrameConnectionCoefficient
  referenceHighHorizontalAngularL referenceLowerHorizontalAngularL
  referenceHighAdjointMovingBoundaryActionFamily referenceLowerAdjointMovingBoundaryActionFamily
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

theorem referenceHighDensityFirstAction_smul
    (q : ℝ) (R chi : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ))
    (y : R3) (i : Fin 3) (hchi : DifferentiableAt ℝ chi y)
    (hu : DifferentiableAt ℝ u y) :
    referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      q R (fun x => chi x • u x) y i =
    (fderiv ℝ chi y (referenceMetricGramFrame g L (q,y) i)) •
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u y) +
    chi y • referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      q R u y i := by
  have hDerivative := congrArg
    (fun A : R3 →L[ℝ] SphereSobolev (3/2 : ℝ) => A (referenceMetricGramFrame g L (q,y) i))
    (fderiv_fun_smul hchi hu)
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply] at hDerivative
  simp only [referenceHighDensityFirstAction,referenceHighHorizontalAction,
    hDerivative,map_add,map_smul,smul_add]
  abel

theorem referenceLowerDensityFirstAction_smul
    (q : ℝ) (R chi : R3 → ℝ) (u : R3 → SphereSobolev (1/2 : ℝ))
    (y : R3) (i : Fin 3) (hchi : DifferentiableAt ℝ chi y)
    (hu : DifferentiableAt ℝ u y) :
    referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      q R (fun x => chi x • u x) y i =
    (fderiv ℝ chi y (referenceMetricGramFrame g L (q,y) i)) •
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (u y) +
    chi y • referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      q R u y i := by
  have hDerivative := congrArg
    (fun A : R3 →L[ℝ] SphereSobolev (1/2 : ℝ) => A (referenceMetricGramFrame g L (q,y) i))
    (fderiv_fun_smul hchi hu)
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply] at hDerivative
  simp only [referenceLowerDensityFirstAction,referenceLowerHorizontalAction,
    hDerivative,map_add,map_smul,smul_add]
  abel

theorem referenceLowerDensityFirstAction_add
    (q : ℝ) (R : R3 → ℝ) (u v : R3 → SphereSobolev (1/2 : ℝ))
    (y : R3) (i : Fin 3) (hu : DifferentiableAt ℝ u y)
    (hv : DifferentiableAt ℝ v y) :
    referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      q R (fun x => u x+v x) y i =
    referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i +
    referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i := by
  have hh := referenceLowerHorizontalAction_add g L q u v y i hu hv
  simp only [referenceLowerDensityFirstAction,hh,map_add]
  abel

def referenceFrameScalarDerivative (g : MatrixField) (L q : ℝ) (chi : R3 → ℝ)
    (y : R3) (i : Fin 3) : ℝ :=
  fderiv ℝ chi y (referenceMetricGramFrame g L (q,y) i)

def referenceFrameScalarHessian (g : MatrixField) (L q : ℝ) (chi : R3 → ℝ)
    (y : R3) (i j : Fin 3) : ℝ :=
  fderiv ℝ (fun x => referenceFrameScalarDerivative g L q chi x j) y
    (referenceMetricGramFrame g L (q,y) i) -
  ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
    (referenceMetricGramFrame g L (q,y) i) k j * referenceFrameScalarDerivative g L q chi y k

private theorem sum_scalar_cutoff_algebra {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a : Fin 3 → ℝ) (u : Fin 3 → E) (c : ℝ) (v : E) :
    (∑ k : Fin 3, (a k • v + c • u k)) =
      (∑ k : Fin 3, a k) • v + c • ∑ k : Fin 3, u k := by
  rw [Finset.sum_add_distrib,Finset.sum_smul,Finset.smul_sum]

theorem referenceDensityCovariantSecondAction_smul
    (hreg : FixedDirichletRegularity) (q : ℝ) (R chi : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i j : Fin 3)
    (hu : ContDiff ℝ ∞ u) (hchi : ContDiff ℝ ∞ chi)
    (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceDensityCovariantSecondAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      q R (fun x => chi x • u x) y i j =
    chi y • referenceDensityCovariantSecondAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      q R u y i j +
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceFrameScalarDerivative g L q chi y i •
        referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y j +
       referenceFrameScalarDerivative g L q chi y j •
        referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i +
       referenceFrameScalarHessian g L q chi y i j •
        sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u y)) := by
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Dh := referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
  let Dl := referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
  let cj : R3 → ℝ := fun x => referenceFrameScalarDerivative g L q chi x j
  let Γ : Fin 3 → ℝ := fun k => referenceFrameConnectionCoefficient g L q y
    (referenceMetricGramFrame g L (q,y) i) k j
  have huc : DifferentiableAt ℝ u y := hu.differentiable (by simp) y
  have hcc : DifferentiableAt ℝ chi y := hchi.differentiable (by simp) y
  have hcj : ContDiff ℝ ∞ cj :=
    (hchi.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_referenceMetricGramFrame_slice g hg L q j)
  have hIu : ContDiff ℝ ∞ (fun x => Iin (u x)) := Iin.contDiff.comp hu
  have hDhj : ContDiffAt ℝ ∞ (fun x => Dh u x j) y :=
    contDiffAt_referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg q R u y j hu.contDiffAt hR hr hInv hp
  have hHigh : (fun x => Dh (fun z => chi z • u z) x j) =
      (fun x => cj x • Iin (u x) + chi x • Dh u x j) := by
    funext x
    exact referenceHighDensityFirstAction_smul g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      q R chi u x j (hchi.differentiable (by simp) x) (hu.differentiable (by simp) x)
  have hLowSum := referenceLowerDensityFirstAction_add g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    q R (fun x => cj x • Iin (u x)) (fun x => chi x • Dh u x j) y i
    ((hcj.differentiable (by simp) y).smul (hIu.differentiable (by simp) y))
    (hcc.smul (hDhj.differentiableAt (by simp)))
  have hLowLeft := referenceLowerDensityFirstAction_smul g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    q R cj (fun x => Iin (u x)) y i (hcj.differentiable (by simp) y) (hIu.differentiable (by simp) y)
  have hLowRight := referenceLowerDensityFirstAction_smul g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    q R chi (fun x => Dh u x j) y i hcc (hDhj.differentiableAt (by simp))
  have hCompat : Dl (fun x => Iin (u x)) y i = Iout (Dh u y i) :=
    (referenceDensityFirstAction_high_lower_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg q R y i hInv hp.2.1 u huc).symm
  have hLow : Dl (fun x => Dh (fun z => chi z • u z) x j) y i =
      fderiv ℝ cj y (referenceMetricGramFrame g L (q,y) i) • Iout (Iin (u y)) +
      cj y • Iout (Dh u y i) +
      (referenceFrameScalarDerivative g L q chi y i • Iout (Dh u y j) +
       chi y • Dl (fun x => Dh u x j) y i) := by
    have hTransport : Dl (fun x => Dh (fun z => chi z • u z) x j) y i =
        Dl (fun x => cj x • Iin (u x) + chi x • Dh u x j) y i :=
      congrArg (fun f : R3 → SphereSobolev (1/2 : ℝ) => Dl f y i) hHigh
    have hLeft : Dl (fun x => cj x • Iin (u x)) y i =
        fderiv ℝ cj y (referenceMetricGramFrame g L (q,y) i) • Iout (Iin (u y)) +
        cj y • Iout (Dh u y i) :=
      hLowLeft.trans (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
        fderiv ℝ cj y (referenceMetricGramFrame g L (q,y) i) • Iout (Iin (u y)) + cj y • z) hCompat)
    have hRight : Dl (fun x => chi x • Dh u x j) y i =
        referenceFrameScalarDerivative g L q chi y i • Iout (Dh u y j) +
        chi y • Dl (fun x => Dh u x j) y i := hLowRight
    exact hTransport.trans (hLowSum.trans
      (congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b) hLeft hRight))
  have hConn : (∑ k : Fin 3, Γ k • Iout (Dh (fun x => chi x • u x) y k)) =
      (∑ k : Fin 3, Γ k * referenceFrameScalarDerivative g L q chi y k) • Iout (Iin (u y)) +
      chi y • ∑ k : Fin 3, Γ k • Iout (Dh u y k) := by
    have hTerm (k : Fin 3) : Γ k • Iout (Dh (fun x => chi x • u x) y k) =
        (Γ k * referenceFrameScalarDerivative g L q chi y k) • Iout (Iin (u y)) +
        chi y • (Γ k • Iout (Dh u y k)) := by
      have hFirst : Dh (fun x => chi x • u x) y k =
          referenceFrameScalarDerivative g L q chi y k • Iin (u y) + chi y • Dh u y k :=
        referenceHighDensityFirstAction_smul g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          q R chi u y k hcc huc
      calc
        _ = Γ k • Iout (referenceFrameScalarDerivative g L q chi y k • Iin (u y) +
            chi y • Dh u y k) :=
          congrArg (fun z : SphereSobolev (1/2 : ℝ) => Γ k • Iout z) hFirst
        _ = _ := by simp only [map_add,map_smul,smul_add,smul_smul]; module
    calc
      _ = ∑ k : Fin 3, ((Γ k * referenceFrameScalarDerivative g L q chi y k) • Iout (Iin (u y)) +
          chi y • (Γ k • Iout (Dh u y k))) := Finset.sum_congr rfl (fun k _ => hTerm k)
      _ = _ := sum_scalar_cutoff_algebra
        (fun k => Γ k * referenceFrameScalarDerivative g L q chi y k)
        (fun k => Γ k • Iout (Dh u y k)) (chi y) (Iout (Iin (u y)))
  have hDifference := congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x-z) hLow hConn
  refine hDifference.trans ?_
  simp only [referenceDensityCovariantSecondAction,referenceFrameScalarHessian,
    map_add,map_smul,map_sub,sub_smul,smul_sub]
  change
    (fderiv ℝ cj y (referenceMetricGramFrame g L (q,y) i) • Iout (Iin (u y)) +
      cj y • Iout (Dh u y i) +
      (referenceFrameScalarDerivative g L q chi y i • Iout (Dh u y j) +
       chi y • Dl (fun x => Dh u x j) y i)) -
    ((∑ k : Fin 3, Γ k * referenceFrameScalarDerivative g L q chi y k) • Iout (Iin (u y)) +
      chi y • ∑ k : Fin 3, Γ k • Iout (Dh u y k)) =
    chi y • Dl (fun x => Dh u x j) y i -
      chi y • ∑ k : Fin 3, Γ k • Iout (Dh u y k) +
    (referenceFrameScalarDerivative g L q chi y i • Iout (Dh u y j) +
     cj y • Iout (Dh u y i) +
     (fderiv ℝ cj y (referenceMetricGramFrame g L (q,y) i) • Iout (Iin (u y)) -
      (∑ k : Fin 3, Γ k * referenceFrameScalarDerivative g L q chi y k) • Iout (Iin (u y))))
  abel


def referenceDensityScalarCutoffCommutator
    (g2 : MatrixField) (q : ℝ) (R chi : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) : SphereSobolev (1/2 : ℝ) :=
  R y • ((∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
      (referenceFrameScalarDerivative g L q chi y i •
        referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y j +
       referenceFrameScalarDerivative g L q chi y j •
        referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i +
       referenceFrameScalarHessian g L q chi y i j •
        sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u y))) +
    ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) •
      (referenceFrameScalarDerivative g L q chi y i •
        sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u y)))

theorem referencePhysicalDensityOperator_smul_sub
    (g2 : MatrixField) (hreg : FixedDirichletRegularity) (q : ℝ) (R chi : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3)
    (hu : ContDiff ℝ ∞ u) (hchi : ContDiff ℝ ∞ chi)
    (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 q R (fun x => chi x • u x) y -
    chi y • referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 q R u y =
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceDensityScalarCutoffCommutator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        g2 q R chi u y) := by
  have hSecond (i j : Fin 3) := referenceDensityCovariantSecondAction_smul
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R chi u y i j hu hchi hR hr hInv hp
  have hFirst (i : Fin 3) := referenceHighDensityFirstAction_smul
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R chi u y i
      (hchi.differentiable (by simp) y) (hu.differentiable (by simp) y)
  unfold referencePhysicalDensityOperator referenceDensityScalarCutoffCommutator
  simp only [hSecond,hFirst,map_smul,map_add,map_sum,
    smul_add,Finset.sum_add_distrib,Finset.smul_sum,referenceFrameScalarDerivative]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  module

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
