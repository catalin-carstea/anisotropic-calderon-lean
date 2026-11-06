import Calderon.ActualFinitePhysicalModelFullErrorDictionary

/-! Full before-source expansion and verified API bundle:
actual-finite-physical-model-dictionary-author-oct19-v001/BEFORE-SOURCE-RECEIPT.json.
Concrete original finite-input dictionary. No quantitative or transfer-existence claim. -/
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


def referenceFinitePhysicalModelResidual
    (hg:IsAdmissibleMetric g) (g2:MatrixField) (q δ A:ℝ) (p:ℕ)
    (F0:smoothCompactFiniteSphereCore hO hD) (y:R3):SphereSobolev (-(1/2:ℝ)) :=
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
    JF+UFirst+USecond+UAngular+UProducts+UDouble

theorem referencePhysicalDensityOperator_finiteCore_eq_nativeModel_add_explicit_residual
    (hg : IsAdmissibleMetric g) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A)
    (F0 : smoothCompactFiniteSphereCore hO hD) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ
        (q,((y,referenceRadius δ A p L y),x.val))).IsInvertible)
    (hp : (q,(y,referenceRadius δ A p L y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let K:SphereL2→L[ℝ]SphereSobolev (-(1/2:ℝ)):=
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
    referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 q (referenceRadius δ A p L) (finiteCoreSobolevLift hO hD (3/2:ℝ) F0) y=
      K ((nativeNormalizedSecondReferenceModel hO hD hF g g2 hg L q δ A p hg2 hδ hA F0).val y)+
        referenceFinitePhysicalModelResidual g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
          hg g2 q δ A p F0 y := by
  dsimp only
  have h:=referencePhysicalDensityOperator_finiteCore_eq_nativeModel_add_full_residual
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hg g2 hg2 hreg q hq δ A p hδ hA F0 y hy hInv hp
  extract_lets (merge := false) (useContext := false) (descend := false) o_R o_u o_K o_Iin o_Iout o_Ahi o_Alo o_D o_Fh o_Fl o_Eh o_El o_F o_E o_MF o_ME o_Q o_sigma o_b o_Gamma o_f o_r o_CovD o_UF o_UE o_UA o_UFE o_UEE o_USigma o_UD o_UFirst o_USecond o_UAngular o_UProducts o_UDouble o_JF at h
  unfold referenceFinitePhysicalModelResidual
  extract_lets (merge := false) (useContext := false) n_R n_u n_K n_Iin n_Iout n_Ahi n_Alo n_D n_Fh n_Fl n_Eh n_El n_F n_E n_MF n_ME n_Q n_sigma n_b n_Gamma n_f n_r n_CovD n_UF n_UE n_UA n_UFE n_UEE n_USigma n_UD n_UFirst n_USecond n_UAngular n_UProducts n_UDouble n_JF
  have eq_R : n_R = o_R := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_R, o_R]
  have eq_u : n_u = o_u := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_u, o_u]
  have eq_K : n_K = o_K := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_K, o_K]
  have eq_Iin : n_Iin = o_Iin := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_Iin, o_Iin]
  have eq_Iout : n_Iout = o_Iout := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_Iout, o_Iout]
  have eq_Ahi : n_Ahi = o_Ahi := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_Ahi, o_Ahi]
  have eq_Alo : n_Alo = o_Alo := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_Alo, o_Alo]
  have eq_D : n_D = o_D := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_D, o_D, eq_R, eq_u]
  have eq_Fh : n_Fh = o_Fh := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_Fh, o_Fh, eq_R]
  have eq_Fl : n_Fl = o_Fl := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_Fl, o_Fl, eq_R]
  have eq_Eh : n_Eh = o_Eh := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_Eh, o_Eh, eq_R]
  have eq_El : n_El = o_El := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_El, o_El, eq_R]
  have eq_F : n_F = o_F := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_F, o_F, eq_u, eq_Iin, eq_Fh]
  have eq_E : n_E = o_E := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_E, o_E, eq_u, eq_Eh]
  have eq_MF : n_MF = o_MF := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_MF, o_MF, eq_Iout, eq_Fl]
  have eq_ME : n_ME = o_ME := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_ME, o_ME, eq_El]
  have eq_Q : n_Q = o_Q := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_Q, o_Q]
  have eq_sigma : n_sigma = o_sigma := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_sigma, o_sigma, eq_Q]
  have eq_b : n_b = o_b := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_b, o_b]
  have eq_Gamma : n_Gamma = o_Gamma := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_Gamma, o_Gamma]
  have eq_f : n_f = o_f := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_f, o_f, eq_R]
  have eq_r : n_r = o_r := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_r, o_r, eq_R]
  have eq_CovD : n_CovD = o_CovD := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_CovD, o_CovD, eq_R, eq_Iout, eq_D, eq_Gamma]
  have eq_UF : n_UF = o_UF := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_UF, o_UF, eq_R, eq_Iout, eq_D, eq_F, eq_MF, eq_Gamma]
  have eq_UE : n_UE = o_UE := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_UE, o_UE, eq_R, eq_Iout, eq_D, eq_E, eq_ME, eq_Gamma, eq_f]
  have eq_UA : n_UA = o_UA := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_UA, o_UA, eq_u, eq_Ahi, eq_Alo, eq_E, eq_ME]
  have eq_UFE : n_UFE = o_UFE := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_UFE, o_UFE, eq_F, eq_E, eq_MF, eq_ME]
  have eq_UEE : n_UEE = o_UEE := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_UEE, o_UEE, eq_E, eq_ME]
  have eq_USigma : n_USigma = o_USigma := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_USigma, o_USigma, eq_u, eq_Ahi, eq_Alo, eq_D, eq_sigma, eq_r]
  have eq_UD : n_UD = o_UD := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_UD, o_UD, eq_Iout, eq_D, eq_Q, eq_b, eq_r, eq_CovD]
  have eq_UFirst : n_UFirst = o_UFirst := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_UFirst, o_UFirst, eq_Iout, eq_F, eq_Q, eq_b, eq_r, eq_UF]
  have eq_USecond : n_USecond = o_USecond := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_USecond, o_USecond, eq_Iout, eq_E, eq_Q, eq_b, eq_r, eq_UE]
  have eq_UAngular : n_UAngular = o_UAngular := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_UAngular, o_UAngular, eq_Q, eq_r, eq_UA]
  have eq_UProducts : n_UProducts = o_UProducts := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_UProducts, o_UProducts, eq_Q, eq_r, eq_UFE]
  have eq_UDouble : n_UDouble = o_UDouble := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_UDouble, o_UDouble, eq_Q, eq_r, eq_UEE]
  have eq_JF : n_JF = o_JF := by
    simp (config := {zeta := false, zetaDelta := false}) only [n_JF, o_JF, eq_u, eq_Ahi, eq_Alo, eq_F, eq_MF, eq_Q]
  simpa (config := {zeta := false, zetaDelta := false}) only [eq_JF, eq_UFirst, eq_USecond, eq_UAngular, eq_UProducts, eq_UDouble, o_R, o_u, o_K, add_assoc] using h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
