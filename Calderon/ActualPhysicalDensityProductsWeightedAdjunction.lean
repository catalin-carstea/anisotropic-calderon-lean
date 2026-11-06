import Calderon.ActualPhysicalDensityProductsAdjointOperatorCore

/-! Actual Main M1 Products adjoint. Full nine-root before-code expansion and
exact original definitions were reviewed before authoring. No quantitative
Productsdag cap, finite-output assumption or intrinsic Half adjoint is used. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  ActualFiniteHarmonicCore SpectralCoreRegularity SpectralWeightedGraph
  ConformalDepth NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge ReferenceDensityBounds
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv
  sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL
  sphereSobolevLinearCoordinateMulL referenceNativeMovingAdjointParametricCorrection
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceAdjointMovingDifferenceQuotientPivotHigh referenceAdjointMovingDifferenceQuotientPivotLow

lemma inner_zero_referencePhysicalDensityProductsAdjointHalfOperator
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (g2 : MatrixField)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (hr : R y ≠ 0)
    (hInv : ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (u v : SphereSobolev (3/2 : ℝ)) :
    ⟪sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v),
      sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (referencePhysicalDensityProductsHalfOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y u)⟫_ℝ =
    ⟪sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (referencePhysicalDensityProductsAdjointHalfOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y v),
      sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)⟫_ℝ := by
  classical
  let I : Hi →L[ℝ] Half := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : Half →L[ℝ] Neg := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Z : Half →L[ℝ] SphereSobolev 0 := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Q : Half → Neg → ℝ := sphereSobolevDualPairing (1/2 : ℝ)
  let Fh : Fin 3 → Hi →L[ℝ] Hi := fun i =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,y),fderiv ℝ R y) i
  let Fl : Fin 3 → Half →L[ℝ] Half := fun i =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
  let Fbh : Fin 3 → Hi →L[ℝ] Hi := fun i =>
    referenceNativeMovingParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,y),fderiv ℝ R y) i
  let Fbl : Fin 3 → Half →L[ℝ] Half := fun i =>
    referenceNativeMovingParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
  let Eh : Fin 3 → Hi →L[ℝ] Half := fun i =>
    referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  let El : Fin 3 → Half →L[ℝ] Neg := fun i =>
    referenceLowerAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  let Eb : Fin 3 → Hi →L[ℝ] Half := fun i =>
    referenceAdjointMovingDifferenceQuotientPivotHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  let coeff : Fin 3 → Fin 3 → ℝ := referenceDensityPrincipalFrameCoefficient g g2 L q y
  have hInc (a b : Half) : Q a (J b) = ⟪Z a,Z b⟫_ℝ := by
    have hFlip : Q a (J b) = sphereSobolevDualPairing (-(1/2 : ℝ)) (J b) a := by
      change ⟪a,J b⟫_ℝ = ⟪J b,a⟫_ℝ
      exact real_inner_comm (J b) a
    exact hFlip.trans ((sphereSobolevDualPairing_inclusion_eq_inner_zero
      (1/2 : ℝ) (by norm_num) b a).trans (real_inner_comm (Z a) (Z b)))
  have hEnd : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
    simpa only [one_mul] using hSegment 1 ⟨zero_le_one,le_rfl⟩
  have hE (i : Fin 3) (vA : Hi) : J (Eh i vA) = El i (I vA) :=
    congrArg (fun A : Hi →L[ℝ] Neg => A vA)
      (referenceAdjointMovingDifferenceQuotient_high_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R y hy i hInv hEnd)
  have hPairE (i : Fin 3) (vA vB : Hi) :
      ⟪Z (I vB),Z (Eh i vA)⟫_ℝ = ⟪Z (Eb i vB),Z (I vA)⟫_ℝ := by
    have hRaw := (sphereSobolevDualPairing_referenceAdjointMovingDifferenceQuotientPivot
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR y hy hr hInv hSegment i vB (I vA)).1
    have hTyped : Q (I vB) (El i (I vA)) = ⟪Z (I vA),Z (Eb i vB)⟫_ℝ := hRaw
    exact (hInc (I vB) (Eh i vA)).symm.trans
      ((congrArg (Q (I vB)) (hE i vA)).trans (hTyped.trans
        (real_inner_comm (Z (Eb i vB)) (Z (I vA)))))
  have hFPair (i : Fin 3) (a b : Half) :
      ⟪Z b,Z (Fl i a)⟫_ℝ = ⟪Z (Fbl i b),Z a⟫_ℝ :=
    inner_zero_referenceNativeMovingParametricCorrection_adjoint hF hO hD g L
      ((q,y),fderiv ℝ R y) i a b
  have hFc (i : Fin 3) (a : Hi) : I (Fh i a) = Fl i (I a) :=
    referenceNativeMovingAdjointParametricCorrection_inclusion hF hO hD g L
      (3/2 : ℝ) (1/2 : ℝ) (by norm_num) ((q,y),fderiv ℝ R y) i a
  have hFbc (i : Fin 3) (a : Hi) : I (Fbh i a) = Fbl i (I a) :=
    referenceNativeMovingParametricCorrection_inclusion hF hO hD g L
      (3/2 : ℝ) (1/2 : ℝ) (by norm_num) ((q,y),fderiv ℝ R y) i a
  have hFirst (i j : Fin 3) :
      ⟪Z (I v),Z (Fl i (Eh j u))⟫_ℝ = ⟪Z (Eb j (Fbh i v)),Z (I u)⟫_ℝ :=
    (hFPair i (Eh j u) (I v)).trans
      ((congrArg (fun z : Half => ⟪Z z,Z (Eh j u)⟫_ℝ) (hFbc i v).symm).trans
        (hPairE j u (Fbh i v)))
  have hSecond (i j : Fin 3) :
      ⟪Z (I v),Z (Eh i (Fh j u))⟫_ℝ = ⟪Z (Fbl j (Eb i v)),Z (I u)⟫_ℝ :=
    (hPairE i (Fh j u) v).trans
      ((congrArg (fun z : Half => ⟪Z (Eb i v),Z z⟫_ℝ) (hFc j u)).trans
        (hFPair j (I u) (Eb i v)))
  have hTerms (i j : Fin 3) :
      ⟪Z (I v),Z (Fl i (Eh j u)+Eh i (Fh j u))⟫_ℝ =
      ⟪Z (Eb j (Fbh i v)+Fbl j (Eb i v)),Z (I u)⟫_ℝ := by
    simp only [map_add,inner_add_right,inner_add_left]
    exact congrArg₂ (fun a b : ℝ => a+b) (hFirst i j) (hSecond i j)
  have hSum (c : ℝ) (a : Fin 3 → Fin 3 → ℝ) (z : Fin 3 → Fin 3 → Half) (b : Half) :
      ⟪Z b,Z (c • (∑ i : Fin 3, ∑ j : Fin 3, a i j • z i j))⟫_ℝ =
      c * (∑ i : Fin 3, ∑ j : Fin 3, a i j * ⟪Z b,Z (z i j)⟫_ℝ) := by
    simp only [map_smul,map_sum,real_inner_smul_right,inner_sum]
  have hReal : (∑ i : Fin 3, ∑ j : Fin 3, coeff i j *
      ⟪Z (I v),Z (Fl i (Eh j u)+Eh i (Fh j u))⟫_ℝ) =
      ∑ i : Fin 3, ∑ j : Fin 3, coeff i j *
        ⟪Z (I u),Z (Eb j (Fbh i v)+Fbl j (Eb i v))⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun t : ℝ => coeff i j*t) ((hTerms i j).trans
      (real_inner_comm (Z (I u)) (Z (Eb j (Fbh i v)+Fbl j (Eb i v)))))
  have hMain : ⟪Z (I v),Z ((R y)^2 • (∑ i : Fin 3, ∑ j : Fin 3,
      coeff i j • (Fl i (Eh j u)+Eh i (Fh j u))))⟫_ℝ =
      ⟪Z ((R y)^2 • (∑ i : Fin 3, ∑ j : Fin 3,
        coeff i j • (Eb j (Fbh i v)+Fbl j (Eb i v)))),Z (I u)⟫_ℝ :=
    (hSum ((R y)^2) coeff (fun i j => Fl i (Eh j u)+Eh i (Fh j u)) (I v)).trans
      ((congrArg (fun t : ℝ => (R y)^2*t) hReal).trans
        ((hSum ((R y)^2) coeff (fun i j => Eb j (Fbh i v)+Fbl j (Eb i v)) (I u)).symm.trans
          (real_inner_comm (Z ((R y)^2 • (∑ i : Fin 3, ∑ j : Fin 3,
            coeff i j • (Eb j (Fbh i v)+Fbl j (Eb i v))))) (Z (I u)))))
  simpa only [referencePhysicalDensityProductsHalfOperator,
    referencePhysicalDensityProductsAdjointHalfOperator,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    I,Z,Fh,Fl,Fbh,Fbl,Eh,Eb,coeff] using hMain



end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.inner_zero_referencePhysicalDensityProductsAdjointHalfOperator
