import Calderon.ActualCovariantDensityFirstActions
import Calderon.ActualDensityAngularBoundaryAction

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/EXPANSION.md.
Literal ordered covariant density P in H-1/2. Neither Ppsi=0 nor L2/coercivity
is assumed or concluded. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ConformalDepth RadiusProfile ReferenceDensityBounds ActualNormalizedSecondMetricDrift

attribute [local irreducible] referenceHighAdjointMovingBoundaryActionFamily
  referenceLowerAdjointMovingBoundaryActionFamily referenceHighHorizontalAction
  referenceLowerHorizontalAction referenceHighHorizontalAngularL referenceLowerHorizontalAngularL
  referenceMetricGramFrame referenceFrameConnectionCoefficient referenceDensityPrincipalFrameCoefficient
  referenceHighDensityFirstAction referenceLowerDensityFirstAction

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceAdjointMovingCovariantDerivativeL
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i j : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
    (fderiv ℝ (fun x : R3 => referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,x) j)
      y (referenceMetricGramFrame g L (q,y) i)) +
  (referenceLowerHorizontalAngularL g L q y i).comp
    (referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) j) -
  (referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) j).comp
    (referenceHighHorizontalAngularL g L q y i) -
  ∑ k : Fin 3,
    referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j •
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) k)

theorem referenceLowerHorizontalAction_adjointMoving_product
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i j : Fin 3)
    (hu : ContDiffAt ℝ ∞ u y) (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceLowerHorizontalAction g L q
      (fun x => referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,x) j (u x)) y i -
    (∑ k : Fin 3,
      referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j •
        sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
          (referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) k (u y))) =
    referenceAdjointMovingCovariantDerivativeL g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i j (u y) +
    referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) j
      (referenceHighHorizontalAction g L q u y i) := by
  let Ch : Fin 3 → R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    fun k x => referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,x) k
  let Cl := referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) j
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let e := referenceMetricGramFrame g L (q,y) i
  let Ωh := referenceHighHorizontalAngularL g L q y i
  let Ωl := referenceLowerHorizontalAngularL g L q y i
  let conn : SphereSobolev (-(1/2 : ℝ)) := ∑ k : Fin 3,
    referenceFrameConnectionCoefficient g L q y e k j • Iout (Ch k y (u y))
  have hCh : ContDiffAt ℝ ∞ (Ch j) y :=
    (contDiffAt_referenceHighAdjointMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg R (q,y) j hR hr hInv hp).comp y (contDiffAt_const.prodMk contDiffAt_id)
  have hProduct := referenceLowerHorizontalAction_clm_apply g L q (Ch j) u y i
    (hCh.differentiableAt (by simp)) (hu.differentiableAt (by simp))
  have hBase : Iout (Ch j y (fderiv ℝ u y e)) = Cl (Iin (fderiv ℝ u y e)) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      A (fderiv ℝ u y e))
      (referenceAdjointMovingBoundaryActionFamily_high_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R y j hInv hp.2.1)
  have hProduct' : referenceLowerHorizontalAction g L q (fun x => Ch j x (u x)) y i =
      Cl (Iin (fderiv ℝ u y e)) + Iout ((fderiv ℝ (Ch j) y e) (u y)) + Ωl (Ch j y (u y)) :=
    hProduct.trans (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      z + Iout ((fderiv ℝ (Ch j) y e) (u y)) + Ωl (Ch j y (u y))) hBase)
  have hSub := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => z-conn) hProduct'
  have hAlgebra :
      (Cl (Iin (fderiv ℝ u y e)) + Iout ((fderiv ℝ (Ch j) y e) (u y)) +
        Ωl (Ch j y (u y))) - conn =
      (Iout ((fderiv ℝ (Ch j) y e) (u y)) + Ωl (Ch j y (u y)) - Cl (Ωh (u y)) - conn) +
        Cl (Iin (fderiv ℝ u y e) + Ωh (u y)) := by
    simp only [map_add]
    abel
  simpa only [referenceAdjointMovingCovariantDerivativeL,referenceHighHorizontalAction,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,Ch,Cl,Iin,Iout,e,Ωh,Ωl,conn]
    using hSub.trans hAlgebra

def referenceHorizontalCovariantSecondAction (q : ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i j : Fin 3) : SphereSobolev (-(1/2 : ℝ)) :=
  referenceLowerHorizontalAction g L q (fun x => referenceHighHorizontalAction g L q u x j) y i -
  ∑ k : Fin 3,
    referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j •
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighHorizontalAction g L q u y k)

def referenceDensityCovariantSecondAction (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i j : Fin 3) : SphereSobolev (-(1/2 : ℝ)) :=
  referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
    (fun x => referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x j) y i -
  ∑ k : Fin 3,
    referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j •
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y k)

attribute [local irreducible] referenceAdjointMovingCovariantDerivativeL
  referenceHorizontalCovariantSecondAction referenceDensityCovariantSecondAction

theorem referenceDensityCovariantSecondAction_expansion
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i j : Fin 3)
    (hu : ContDiffAt ℝ ∞ u y) (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceDensityCovariantSecondAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j =
    referenceHorizontalCovariantSecondAction g L q u y i j +
    referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i
      (referenceHighHorizontalAction g L q u y j) +
    referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) j
      (referenceHighHorizontalAction g L q u y i) +
    referenceAdjointMovingCovariantDerivativeL g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i j (u y) +
    referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i
      (referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) j (u y)) := by
  trace "physical-second: body"
  let Ch : Fin 3 → R3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    fun k x => referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,x) k
  let Cl := referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Γ : Fin 3 → ℝ := fun k => referenceFrameConnectionCoefficient g L q y
    (referenceMetricGramFrame g L (q,y) i) k j
  let connH : SphereSobolev (-(1/2 : ℝ)) :=
    ∑ k : Fin 3, Γ k • Iout (referenceHighHorizontalAction g L q u y k)
  let connC : SphereSobolev (-(1/2 : ℝ)) := ∑ k : Fin 3, Γ k • Iout (Ch k y (u y))
  let connD : SphereSobolev (-(1/2 : ℝ)) :=
    ∑ k : Fin 3, Γ k • Iout (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y k)
  trace "physical-second: aliases"
  have hH := contDiffAt_referenceHighHorizontalAction g hg L q u y j hu
  have hC := (contDiffAt_referenceHighAdjointMovingBoundaryActionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg R (q,y) j hR hr hInv hp).comp y (contDiffAt_const.prodMk contDiffAt_id)
  trace "physical-second: smoothness"
  have hAdd := referenceLowerHorizontalAction_add g L q
    (fun x => referenceHighHorizontalAction g L q u x j) (fun x => Ch j x (u x)) y i
      (hH.differentiableAt (by simp)) ((hC.clm_apply hu).differentiableAt (by simp))
  trace "physical-second: horizontal add"
  have hFirst := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b)
    hAdd (map_add Cl (referenceHighHorizontalAction g L q u y j) (Ch j y (u y)))
  have hSub := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => z-connD) hFirst
  trace "physical-second: first split"
  have hConn : connD = connH+connC := by
    simp only [connD,connH,connC,referenceHighDensityFirstAction,map_add,smul_add,
      Finset.sum_add_distrib,Ch]
  have hSplit := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
    (referenceLowerHorizontalAction g L q (fun x => referenceHighHorizontalAction g L q u x j) y i +
      referenceLowerHorizontalAction g L q (fun x => Ch j x (u x)) y i +
      (Cl (referenceHighHorizontalAction g L q u y j) + Cl (Ch j y (u y)))) - z) hConn
  trace "physical-second: connection split"
  have hProduct := referenceLowerHorizontalAction_adjointMoving_product
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R u y i j hu hR hr hInv hp
  have hMiddle := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
    referenceLowerHorizontalAction g L q (fun x => referenceHighHorizontalAction g L q u x j) y i -
      connH + Cl (referenceHighHorizontalAction g L q u y j) + z + Cl (Ch j y (u y))) hProduct
  have hAlgebra :
      (referenceLowerHorizontalAction g L q (fun x => referenceHighHorizontalAction g L q u x j) y i +
        referenceLowerHorizontalAction g L q (fun x => Ch j x (u x)) y i +
        (Cl (referenceHighHorizontalAction g L q u y j) + Cl (Ch j y (u y)))) - (connH+connC) =
      referenceLowerHorizontalAction g L q (fun x => referenceHighHorizontalAction g L q u x j) y i -
        connH + Cl (referenceHighHorizontalAction g L q u y j) +
        (referenceLowerHorizontalAction g L q (fun x => Ch j x (u x)) y i - connC) +
        Cl (Ch j y (u y)) := by abel
  trace "physical-second: algebra"
  have hFinal := (hSub.trans hSplit).trans (hAlgebra.trans hMiddle)
  trace "physical-second: final"
  simp only [referenceDensityCovariantSecondAction,referenceLowerDensityFirstAction,
    referenceHighDensityFirstAction,referenceHorizontalCovariantSecondAction,Ch,Cl,Iout,Γ,connH,
    connC,connD] at hFinal ⊢
  trace "physical-second: definitions expanded"
  exact hFinal.trans (by abel)

def referencePhysicalDensityOperator (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) : SphereSobolev (-(1/2 : ℝ)) :=
  R y • ((∑ i : Fin 3, ∑ j : Fin 3,
    referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
      referenceDensityCovariantSecondAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j) +
    ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) •
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i))

theorem referencePhysicalDensityOperator_expansion
    (g2 : MatrixField) (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3)
    (hu : ContDiffAt ℝ ∞ u y) (hR : ContDiffAt ℝ ∞ R y) (hr : R y ≠ 0)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y =
    R y • ((∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
        (referenceHorizontalCovariantSecondAction g L q u y i j +
        referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i
          (referenceHighHorizontalAction g L q u y j) +
        referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) j
          (referenceHighHorizontalAction g L q u y i) +
        referenceAdjointMovingCovariantDerivativeL g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i j (u y) +
        referenceLowerAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i
          (referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) j (u y)))) +
      ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) •
        sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
          (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i)) := by
  apply congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => R y • z)
  apply congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => z +
    ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) •
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i))
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
    referenceDensityPrincipalFrameCoefficient g g2 L q y i j • z)
    (referenceDensityCovariantSecondAction_expansion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R u y i j hu hR hr hInv hp)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMovingCovariantDerivativeL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerHorizontalAction_adjointMoving_product
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHorizontalCovariantSecondAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityCovariantSecondAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityCovariantSecondAction_expansion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensityOperator
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensityOperator_expansion
