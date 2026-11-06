import Calderon.ActualPhysicalDensityLeadingDecomposition
import Calderon.ActualDensityCorrectionRemainderSplitting
import Calderon.ActualNativeMovingAdjointMixedJNegativeInclusion

/-! The literal full ordered error. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referencePhysicalDensityOperator referenceDensityCovariantSecondAction
  referenceHighDensityFirstAction referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceNativeMovingAdjointParametricCorrection referenceNativeMovingAdjointHighMixedCorrection
  referenceMetricGramFrame referenceFrameConnectionCoefficient referenceDensityPrincipalFrameCoefficient
  referenceRadiusHorizontalLogDerivative sphereSobolevInclusionL sphereSobolevAngularCoordinateTransposeL
  referenceRadialEndpointInvertibleLocus normalizedSecondDriftFrameJoint

def referencePhysicalDensityError (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) : SphereSobolev (-(1/2 : ℝ)) :=
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Ahi := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
  let Alo := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
  let D := fun (i : Fin 3) (x : R3) => referenceHighWeightedHorizontalAction g L q R u x i
  let Fh := fun (i : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
    hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) i
  let Fl := fun i : Fin 3 => referenceNativeMovingAdjointParametricCorrection
    hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
  let Eh := fun (i : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x i
  let El := fun i : Fin 3 => referenceLowerAdjointMovingDifferenceQuotient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  let F := fun (i : Fin 3) (x : R3) => Iin (Fh i x (u x))
  let E := fun (i : Fin 3) (x : R3) => Eh i x (u x)
  let MF := fun i : Fin 3 => Iout.comp (Fl i)
  let ME := El
  let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let sigma := fun i j : Fin 3 => Q i j-if i=j then (1 : ℝ) else 0
  let b := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
  let Gamma := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q y
    (referenceMetricGramFrame g L (q,y) i) k j
  let f := fun i : Fin 3 => referenceRadiusHorizontalLogDerivative g L q R y i
  let r := R y
  let CovD := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (D j) y i-
    ∑ k : Fin 3, Gamma i j k • Iout (D k y)
  let UF := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (F j) y i+
    MF i (D j y)-(∑ k : Fin 3, Gamma i j k • Iout (F k y))+MF i (F j y)
  let UE := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (E j) y i+
    ME i (D j y)+f i • Iout (E j y)-(∑ k : Fin 3, Gamma i j k • Iout (E k y))
  let UA := fun i j : Fin 3 => Alo i (E j y)+ME i (Ahi j (u y))
  let UFE := fun i j : Fin 3 => MF i (E j y)+ME i (F j y)
  let UEE := fun i j : Fin 3 => ME i (E j y)
  let USigma := (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (D j y))+
    r⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (Ahi j (u y)))
  let UD := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j)+
    r • (∑ i : Fin 3, b i • Iout (D i y))
  let UFirst := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UF i j)+
    r • (∑ i : Fin 3, b i • Iout (F i y))
  let USecond := r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UE i j)+
    r^2 • (∑ i : Fin 3, b i • Iout (E i y))
  let UAngular := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UA i j)
  let UProducts := r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UFE i j)
  let UDouble := r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UEE i j)
  USigma+UD+UFirst+USecond+UAngular+UProducts+UDouble

attribute [local irreducible] referencePhysicalDensityError

lemma referencePhysicalDensityOperator_eq_leading_add_mixed_add_error
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (hr : R y ≠ 0) (hu : ContDiffAt ℝ ∞ u y)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let D := fun (i : Fin 3) (x : R3) => referenceHighWeightedHorizontalAction g L q R u x i
    let Alo := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
    let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y =
    (2 : ℝ) • (∑ i : Fin 3, Alo i (D i y)) + Iout (referenceNativeMovingAdjointHighMixedCorrection
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 q y (fderiv ℝ R y) (u y)) +
    referencePhysicalDensityError g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y := by
  dsimp only
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Ahi := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
  let Alo := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
  let D := fun (i : Fin 3) (x : R3) => referenceHighWeightedHorizontalAction g L q R u x i
  let Fh := fun (i : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
    hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) i
  let Fl := fun i : Fin 3 => referenceNativeMovingAdjointParametricCorrection
    hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
  let Eh := fun (i : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x i
  let El := fun i : Fin 3 => referenceLowerAdjointMovingDifferenceQuotient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  let F := fun (i : Fin 3) (x : R3) => Iin (Fh i x (u x))
  let E := fun (i : Fin 3) (x : R3) => Eh i x (u x)
  let MF := fun i : Fin 3 => Iout.comp (Fl i)
  let ME := El
  let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let sigma := fun i j : Fin 3 => Q i j-if i=j then (1 : ℝ) else 0
  let b := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
  let Gamma := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q y
    (referenceMetricGramFrame g L (q,y) i) k j
  let f := fun i : Fin 3 => referenceRadiusHorizontalLogDerivative g L q R y i
  let r := R y
  let CovD := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (D j) y i-
    ∑ k : Fin 3, Gamma i j k • Iout (D k y)
  let UF := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (F j) y i+
    MF i (D j y)-(∑ k : Fin 3, Gamma i j k • Iout (F k y))+MF i (F j y)
  let UE := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (E j) y i+
    ME i (D j y)+f i • Iout (E j y)-(∑ k : Fin 3, Gamma i j k • Iout (E k y))
  let UA := fun i j : Fin 3 => Alo i (E j y)+ME i (Ahi j (u y))
  let UFE := fun i j : Fin 3 => MF i (E j y)+ME i (F j y)
  let UEE := fun i j : Fin 3 => ME i (E j y)
  let USigma := (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (D j y))+
    r⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (Ahi j (u y)))
  let UD := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j)+
    r • (∑ i : Fin 3, b i • Iout (D i y))
  let UFirst := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UF i j)+
    r • (∑ i : Fin 3, b i • Iout (F i y))
  let USecond := r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UE i j)+
    r^2 • (∑ i : Fin 3, b i • Iout (E i y))
  let UAngular := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UA i j)
  let UProducts := r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UFE i j)
  let UDouble := r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UEE i j)
  let K := fun (i : Fin 3) (x : R3) => F i x+R x • E i x
  let V := fun (i : Fin 3) (x : R3) => (R x)⁻¹ • Ahi i (u x)
  let Klo := fun i : Fin 3 => MF i+r • ME i
  let Rem := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (K j) y i+
    r⁻¹ • Alo i (K j y)+(Klo i) (D j y)+(Klo i) (V j y)+(Klo i) (K j y)-
    ∑ k : Fin 3, Gamma i j k • Iout (K k y)
  let Jpair := fun i j : Fin 3 => Alo i (F j y)+MF i (Ahi j (u y))
  let LD := (2 : ℝ) • (∑ i : Fin 3, Alo i (D i y))
  let SC := (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (D j y))
  let SD := r⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (Ahi j (u y)))
  have hContractRadius {Z : Type} [AddCommGroup Z] [Module ℝ Z]
      (s : ℝ) (c : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → Fin 3 → Z) :
      s • (∑ i : Fin 3, ∑ j : Fin 3, c i j • v i j) =
      ∑ i : Fin 3, ∑ j : Fin 3, c i j • (s • v i j) := by
    have hScale : s • (∑ i : Fin 3, ∑ j : Fin 3, c i j • v i j) =
        ∑ i : Fin 3, ∑ j : Fin 3, s • (c i j • v i j) := by
      simp only [Finset.smul_sum]
    exact hScale.trans (Finset.sum_congr rfl
      (fun i _ => Finset.sum_congr rfl (fun j _ => smul_comm s (c i j) (v i j))))
  have hSix {Z : Type} [AddCommGroup Z] [Module ℝ Z]
      (s : ℝ) (c : Fin 3 → Fin 3 → ℝ)
      (v0 v1 v2 v3 v4 v5 : Fin 3 → Fin 3 → Z) :
      (∑ i : Fin 3, ∑ j : Fin 3,
        c i j • (v0 i j+s • v1 i j+s^2 • v2 i j+s • v3 i j+s^2 • v4 i j+s^3 • v5 i j)) =
      (∑ i : Fin 3, ∑ j : Fin 3, c i j • v0 i j)+
      s • (∑ i : Fin 3, ∑ j : Fin 3, c i j • v1 i j)+
      s^2 • (∑ i : Fin 3, ∑ j : Fin 3, c i j • v2 i j)+
      s • (∑ i : Fin 3, ∑ j : Fin 3, c i j • v3 i j)+
      s^2 • (∑ i : Fin 3, ∑ j : Fin 3, c i j • v4 i j)+
      s^3 • (∑ i : Fin 3, ∑ j : Fin 3, c i j • v5 i j) := by
    have hPoint (t : ℝ) (z0 z1 z2 z3 z4 z5 : Z) :
        t • (z0+s • z1+s^2 • z2+s • z3+s^2 • z4+s^3 • z5) =
        t • z0+s • (t • z1)+s^2 • (t • z2)+s • (t • z3)+s^2 • (t • z4)+s^3 • (t • z5) := by
      simp only [smul_add,smul_smul]
      module
    have hSum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ => Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
        (fun j _ => hPoint (c i j) (v0 i j) (v1 i j) (v2 i j) (v3 i j) (v4 i j) (v5 i j)))
    exact hSum.trans (by simp only [Finset.sum_add_distrib,Finset.smul_sum])
  have hRegroup {Z : Type} [AddCommGroup Z]
      (l sc sd cd bd jq jb uf bf ue be ua ufe uee : Z) :
      l+sc+sd+cd+(jq+uf+ue+ua+ufe+uee)+bd+jb+(bf+be) =
      l+(jq+jb)+((sc+sd)+(cd+bd)+(uf+bf)+(ue+be)+ua+ufe+uee) := by abel
  trace "PHYSICAL_ERROR_ABSTRACT_SUM_ALGEBRA_READY"
  have hActualSplit (i j : Fin 3) : r • Rem i j =
      Jpair i j+r • UF i j+r^2 • UE i j+r • UA i j+r^2 • UFE i j+r^3 • UEE i j :=
    referenceDensityCovariantCorrectionRemainder_split
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R hR u y i j hr hu hInv hp
  have hWeightedSplit : (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (r • Rem i j)) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        Q i j • (Jpair i j+r • UF i j+r^2 • UE i j+r • UA i j+r^2 • UFE i j+r^3 • UEE i j) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => Q i j • z) (hActualSplit i j)))
  have hRemainder := ((hContractRadius r Q Rem).trans hWeightedSplit).trans
    (hSix r Q Jpair UF UE UA UFE UEE)
  trace "PHYSICAL_ERROR_REMAINDER_SUM_READY"
  have hDriftK := referenceMovingCorrectionRemainder_drift_sum_split
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y
  have hLeading := referencePhysicalDensityOperator_leading_decomposition
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 hreg q hq R hR u y hy hr hu hInv hp
  have hSlots := congrArg₂
    (fun rem driftK : SphereSobolev (-(1/2 : ℝ)) =>
      LD+SC+SD+r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j)+rem+
      r • (∑ i : Fin 3, b i • Iout (D i y))+
      (∑ i : Fin 3, b i • Iout (Ahi i (u y)))+driftK)
    hRemainder hDriftK
  have hExpanded := hLeading.trans hSlots
  trace "PHYSICAL_ERROR_ACTUAL_EXPANSION_READY"
  have hOrdered := hExpanded.trans (hRegroup LD SC SD
    (r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j))
    (r • (∑ i : Fin 3, b i • Iout (D i y)))
    (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Jpair i j)
    (∑ i : Fin 3, b i • Iout (Ahi i (u y)))
    (r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UF i j))
    (r • (∑ i : Fin 3, b i • Iout (F i y)))
    (r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UE i j))
    (r^2 • (∑ i : Fin 3, b i • Iout (E i y)))
    (r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UA i j))
    (r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UFE i j))
    (r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UEE i j)))
  have hMixed := referenceNativeMovingAdjointHighMixedCorrection_negative_inclusion
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 hreg q hq y hy (fderiv ℝ R y) (u y)
  have hError : referencePhysicalDensityError g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y = USigma+UD+UFirst+USecond+UAngular+UProducts+UDouble := by
    unfold referencePhysicalDensityError
    rfl
  trace "PHYSICAL_ERROR_MIXED_AND_ERROR_READY"
  have hFinal := congrArg₂
    (fun mixed error : SphereSobolev (-(1/2 : ℝ)) => LD+mixed+error)
    hMixed.symm hError.symm
  exact hOrdered.trans hFinal

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensityError
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensityOperator_eq_leading_add_mixed_add_error
