import Calderon.ActualFinitePhysicalModelErrorDictionary

/-! Concrete original finite-input error dictionary. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore
  ActualFiniteHarmonicModel ActualFiniteHarmonicAmbient SpectralCoreRegularity
  SpectralWeightedGraph SphereHilbertDecomposition NormalCoordinatesFrame SmoothMetricFrame MovingFrameConnection AmbientReferenceRaising
  ActualReferenceModelTrace ActualReferenceParallelRaising ActualPhysicalMixedNative
  ActualPhysicalPureAngular ActualNormalizedSecondMetricDrift
  ActualNormalizedSecondDriftAngularAllocation ActualNormalizedSecondModelErrorAssembly
  ReferenceDensityBounds NormalizedPrincipalMetric ConformalDepth RadiusProfile
  AngularShiftGraph HarmonicDerivativeOperator SmoothSphereRotationProjection
  PrincipalCommutator BoundedAngularShift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)


theorem referencePhysicalDensityOperator_finiteCore_eq_nativeModel_add_full_residual
    (hg : IsAdmissibleMetric g) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A)
    (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ
        (q,((y,referenceRadius δ A p L y),x.val))).IsInvertible)
    (hp : (q,(y,referenceRadius δ A p L y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let R : R3 → ℝ := referenceRadius δ A p L
    let u : R3 → SphereSobolev (3/2 : ℝ) := finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
    let K : SphereL2 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
    let Iin : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let Iout : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Ahi : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
    let Alo : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
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
    let USigma : SphereSobolev (-(1/2 : ℝ)) := (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (D j y))+
      r⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (Ahi j (u y)))
    let UD : SphereSobolev (-(1/2 : ℝ)) := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j)+
      r • (∑ i : Fin 3, b i • Iout (D i y))
    let UFirst := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UF i j)+
      r • (∑ i : Fin 3, b i • Iout (F i y))
    let USecond := r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UE i j)+
      r^2 • (∑ i : Fin 3, b i • Iout (E i y))
    let UAngular := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UA i j)
    let UProducts := r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UFE i j)
    let UDouble := r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UEE i j)
    let JF : SphereSobolev (-(1/2 : ℝ)) := ∑ i : Fin 3, ∑ j : Fin 3, Q i j •
      (Alo i (F j y)+MF i (Ahi j (u y)))
    referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y =
    K ((nativeNormalizedSecondReferenceModel hO hD hF g g2 hg L q δ A p hg2 hδ hA F0).val y)+
      JF+UFirst+USecond+UAngular+UProducts+UDouble := by
  intro R u K Iin Iout Ahi Alo D Fh Fl Eh El F E MF ME Q sigma b Gamma f r
    CovD UF UE UA UFE UEE USigma UD UFirst USecond UAngular UProducts UDouble JF
  have hR : ContDiff ℝ ∞ R :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ A p L hδ hA
  have hr : R y ≠ 0 := ne_of_gt (referenceRadius_pos δ A p L y hδ hA)
  have hu : ContDiffAt ℝ ∞ u y :=
    (finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F0).1.contDiffAt
  have hPhysical := referencePhysicalDensityOperator_eq_leading_add_mixed_add_error
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 hreg q hq
    R hR u y hy hr hu hInv hp
  change referencePhysicalDensityOperator
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y =
    (2 : ℝ) • (∑ i : Fin 3, Alo i (D i y)) +
    Iout (referenceNativeMovingAdjointHighMixedCorrection
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 q y (fderiv ℝ R y) (u y)) +
    referencePhysicalDensityError
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y at hPhysical
  have hT : (∑ i : Fin 3, Alo i (D i y)) =
      K ((nativeT hO hD hF g hg L q δ A p hδ hA F0).val y) :=
    referencePhysicalLeadingAction_finiteCore_eq_nativeT
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq δ A p hδ hA F0 y hy
  have hURaw := referencePhysicalDensity_principal_drift_finiteCore_eq_nativeU
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    hg g2 hg2 hreg q hq δ A p hδ hA F0 y hy
  have hU : K ((nativeU hO hD hF g g2 hg L q δ A p hg2 hδ hA F0).val y) = USigma+UD := by
    simpa only [USigma,UD,CovD,r,R,u,K,Iout,Ahi,Alo,D,Q,sigma,b,Gamma] using hURaw
  have hMixedRaw := referenceNativeMovingAdjointHighMixedCorrection_finiteCore_split
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    hg g2 hg2 hreg q hq F0 y hy (fderiv ℝ R y)
  have hJPair (i j : Fin 3) :
      Alo i (Iin (Fh j y (u y)))+Iout (Fl i (Ahi j (u y))) =
      Alo i (F j y)+MF i (Ahi j (u y)) := by rfl
  have hJFSum : (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
      (Alo i (Iin (Fh j y (u y)))+Iout (Fl i (Ahi j (u y))))) = JF := by
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => Q i j • z) (hJPair i j)))
  have hMixedExpanded : Iout (referenceNativeMovingAdjointHighMixedCorrection
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 q y (fderiv ℝ R y) (u y)) =
      K ((nativeModelRaisingDrift hO hD hF g g2 hg hg2 L q F0).val y)+
      (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
        (Alo i (Iin (Fh j y (u y)))+Iout (Fl i (Ahi j (u y))))) := by
    simpa only [R,u,K,Iin,Iout,Ahi,Alo,Fh,Fl,Q] using hMixedRaw
  have hMixed : Iout (referenceNativeMovingAdjointHighMixedCorrection
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 q y (fderiv ℝ R y) (u y)) =
      K ((nativeModelRaisingDrift hO hD hF g g2 hg hg2 L q F0).val y)+JF :=
    hMixedExpanded.trans (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      K ((nativeModelRaisingDrift hO hD hF g g2 hg hg2 L q F0).val y)+z) hJFSum)
  have hError : referencePhysicalDensityError
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y =
      (USigma+UD)+UFirst+USecond+UAngular+UProducts+UDouble := by
    simp only [referencePhysicalDensityError,USigma,UD,UFirst,USecond,UAngular,UProducts,UDouble,
      CovD,UF,UE,UA,UFE,UEE,r,F,E,MF,ME,Eh,El,Fh,Fl,D,Iin,Iout,Ahi,Alo,Q,sigma,b,Gamma,f]
  have hModel : K ((nativeNormalizedSecondReferenceModel
      hO hD hF g g2 hg L q δ A p hg2 hδ hA F0).val y) =
      (2 : ℝ) • K ((nativeT hO hD hF g hg L q δ A p hδ hA F0).val y)+
      K ((nativeU hO hD hF g g2 hg L q δ A p hg2 hδ hA F0).val y)+
      K ((nativeModelRaisingDrift hO hD hF g g2 hg hg2 L q F0).val y) := by
    simp only [nativeNormalizedSecondReferenceModel,nativeModelRaising,two_mul,
      LinearMap.add_apply,Submodule.coe_add,Pi.add_apply,map_add,two_smul]
  have hErrorNative : referencePhysicalDensityError
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y =
      K ((nativeU hO hD hF g g2 hg L q δ A p hg2 hδ hA F0).val y)+
        UFirst+USecond+UAngular+UProducts+UDouble :=
    hError.trans (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      z+UFirst+USecond+UAngular+UProducts+UDouble) hU.symm)
  have hLeading := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => (2 : ℝ) • z) hT
  have hSlots := congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z)
    (congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z) hLeading hMixed) hErrorNative
  have hReorder {Z : Type} [AddCommGroup Z]
      (t n j f uf ue ua up ud : Z) :
      t+(j+f)+(n+uf+ue+ua+up+ud) = t+n+j+f+uf+ue+ua+up+ud := by abel
  have hOrdered := hReorder (Z := SphereSobolev (-(1/2 : ℝ)))
    ((2 : ℝ) • K ((nativeT hO hD hF g hg L q δ A p hδ hA F0).val y))
    (K ((nativeU hO hD hF g g2 hg L q δ A p hg2 hδ hA F0).val y))
    (K ((nativeModelRaisingDrift hO hD hF g g2 hg hg2 L q F0).val y))
    JF UFirst USecond UAngular UProducts UDouble
  have hModelTransport := congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
    z+JF+UFirst+USecond+UAngular+UProducts+UDouble) hModel.symm
  exact hPhysical.trans (hSlots.trans (hOrdered.trans hModelTransport))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensityOperator_finiteCore_eq_nativeModel_add_full_residual
