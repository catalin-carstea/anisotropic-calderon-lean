import Calderon.ActualHighAdjointConditionalRadiusPowerWordBounds
import Calderon.ActualLowerAdjointConditionalRadiusPowerWordBounds
import Calderon.ActualPairedRadialJacobiProfileScaledJets
import Calderon.ActualFinitePairedRadialQuarticDomain

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualHigherRadiusProfile
  ConformalDepth RadiusProfile ReferenceWeightedApproximation
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  ActualReferenceLocalCoordinateWordJets ActualReferenceDDHigherGeometryJets
  ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherLogFrameJets
  ActualReferenceDecomposition PrincipalCommutator ReferenceDensityBounds
  AmbientReferenceRaising NormalCoordinatesFrame SmoothMetricFrame MovingFrameConnection


theorem exists_referencePairedAdjointMovingDifferenceQuotient_profile_radiusPower_coordinate_word_bounds
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (hg : IsAdmissibleMetric g) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (hKgeom : K ⊆ closedBall y0 ρ) :
    let Sh : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
      referenceSharpRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2
    let Sl : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun z =>
      referenceLowerRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2
    let Th : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
      secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    let Tl : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun z =>
      secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    let Nhi : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := fun i j z =>
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j z)
    let Nhalf : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
        (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun i j z =>
      nativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j z)
    let Nneg : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
        (SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun i j z =>
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j z)
    ∃ dGeom Cscaled CE : ℝ, 0 < dGeom ∧ dGeom ≤ ρ ∧ dGeom ≤ 1 ∧
      ((Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dGeom) dGeom)) ⊆
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      1 ≤ Cscaled ∧ 0 < CE ∧ ∃ p0 : ℕ, 2 ≤ p0 ∧
      ∀ p : ℕ, p0 ≤ p → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
      ∃ A : ℝ, 0 < A ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ x ∈ K,
        let beta := actualReferenceBeta g L q delta A p x
        referenceRadius delta A p L x ≤ dGeom ∧ 1 ≤ beta ∧
        referenceRadius delta A p L x * beta^2 ≤ eta ∧
        (∀ s : ℝ, |s| ≤ 1 → ∀ power : ℕ, 1 ≤ power → power ≤ 3 →
        ∀ order : ℕ, order ≤ 3 →
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (s * referenceRadius delta A p L y)^power •
              Sh (q,(y,s * referenceRadius delta A p L y))) x‖ ≤
            Cscaled * eta^power * beta^order / beta^(2*power) ∧
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (s * referenceRadius delta A p L y)^power •
              Sl (q,(y,s * referenceRadius delta A p L y))) x‖ ≤
            Cscaled * eta^power * beta^order / beta^(2*power) ∧
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (s * referenceRadius delta A p L y)^power •
              Th (q,(y,s * referenceRadius delta A p L y))) x‖ ≤
            Cscaled * eta^power * beta^order / beta^(2*power) ∧
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (s * referenceRadius delta A p L y)^power •
              Tl (q,(y,s * referenceRadius delta A p L y))) x‖ ≤
            Cscaled * eta^power * beta^order / beta^(2*power) ∧
          ∀ i j : Fin 3,
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (s * referenceRadius delta A p L y)^power •
              Nhi i j (q,(y,s * referenceRadius delta A p L y))) x‖ ≤
            Cscaled * eta^power * beta^order / beta^(2*power) ∧
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (s * referenceRadius delta A p L y)^power •
              Nhalf i j (q,(y,s * referenceRadius delta A p L y))) x‖ ≤
            Cscaled * eta^power * beta^order / beta^(2*power) ∧
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (s * referenceRadius delta A p L y)^power •
              Nneg i j (q,(y,s * referenceRadius delta A p L y))) x‖ ≤
            Cscaled * eta^power * beta^order / beta^(2*power)) ∧
        ∀ power : ℕ, 1 ≤ power → power ≤ 2 →
        ∀ i : Fin 3, ∀ word : List (Fin 3), word.length ≤ 3 →
          ‖coordinateFieldWordPartial word
            (fun y : R3 => (referenceRadius delta A p L y)^power •
              referenceHighAdjointMovingDifferenceQuotient
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q
                  (referenceRadius delta A p L) y i) x‖ ≤
            CE * eta^power * beta^word.length / beta^(2*power) ∧
          ‖coordinateFieldWordPartial word
            (fun y : R3 => (referenceRadius delta A p L y)^power •
              referenceLowerAdjointMovingDifferenceQuotient
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q
                  (referenceRadius delta A p L) y i) x‖ ≤
            CE * eta^power * beta^word.length / beta^(2*power) := by
  classical
  intro Sh Sl Th Tl Nhi Nhalf Nneg
  have hHighConditional :=
    exists_referenceHighAdjointMovingDifferenceQuotient_conditional_radiusPower_coordinate_word_bounds
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg hg hL K hK hKgeom
  rcases hHighConditional with ⟨Bh,Fh,mh,hBh,hFh,hmh1,hHighApply⟩
  have hLowConditional :=
    exists_referenceLowerAdjointMovingDifferenceQuotient_conditional_radiusPower_coordinate_word_bounds
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg hg hL K hK hKgeom
  rcases hLowConditional with ⟨Bl,Fl,ml,hBl,hFl,hml1,hLowApply⟩
  have hProfile := exists_referencePairedRadialJacobi_profile_scaled_jets
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg hg hL K hK hKgeom
  rcases hProfile with ⟨dGeom,Cscaled,hdGeom,hdGeomρ,hdGeom1,hRoom,hCscaled,p0,hp02,hProfiles⟩
  have hC0 : 0 ≤ Cscaled := zero_le_one.trans hCscaled
  have hmh : 0 ≤ mh := zero_le_one.trans hmh1
  have hml : 0 ≤ ml := zero_le_one.trans hml1
  let Ch : ℝ := Cscaled*mh+24*Bh*Cscaled+24*Bh*mh*Cscaled+
    24*Cscaled^2*mh+8*Fh*Cscaled
  let Cl : ℝ := Cscaled*ml+24*Bl*Cscaled+24*Bl*ml*Cscaled+
    24*Cscaled^2*ml+8*Fl*Cscaled
  let CE : ℝ := 1+Ch+Cl
  have hCh : 0 ≤ Ch := by dsimp only [Ch]; positivity
  have hCl : 0 ≤ Cl := by dsimp only [Cl]; positivity
  have hCE : 0 < CE := by dsimp only [CE]; positivity
  have hChCE : Ch ≤ CE := by dsimp only [CE]; linarith only [hCl]
  have hClCE : Cl ≤ CE := by dsimp only [CE]; linarith only [hCh]
  refine ⟨dGeom,Cscaled,CE,hdGeom,hdGeomρ,hdGeom1,hRoom,hCscaled,hCE,p0,hp02,?_⟩
  intro p hp eta heta heta1
  have hAmplitude := hProfiles p hp eta heta heta1
  rcases hAmplitude with ⟨A,hA,hAll⟩
  refine ⟨A,hA,?_⟩
  intro q hq delta hdelta hdelta1 x hx beta
  have hPoint := hAll q hq delta hdelta hdelta1 x hx
  refine ⟨hPoint.1,hPoint.2.1,hPoint.2.2.1,hPoint.2.2.2,?_⟩
  have hp1 : 1 ≤ p := by omega
  have hRawHigh (a : ℕ) (ha1 : 1 ≤ a) (ha3 : a ≤ 3)
      (order : ℕ) (horder : order ≤ 3) :
      ‖iteratedFDeriv ℝ order
        (fun y : R3 => (referenceRadius delta A p L y)^a •
          Th (q,(y,referenceRadius delta A p L y))) x‖ ≤
        Cscaled*eta^a*beta^order/beta^(2*a) ∧
      ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ order
        (fun y : R3 => (referenceRadius delta A p L y)^a •
          Nhi i j (q,(y,referenceRadius delta A p L y))) x‖ ≤
        Cscaled*eta^a*beta^order/beta^(2*a) := by
    have hPrimitive := hPoint.2.2.2 1 (by norm_num) a ha1 ha3 order horder
    refine ⟨?_,?_⟩
    · simpa only [one_mul] using hPrimitive.2.2.1
    · intro i j
      simpa only [one_mul] using (hPrimitive.2.2.2.2 i j).1
  have hRawLow (a : ℕ) (ha1 : 1 ≤ a) (ha3 : a ≤ 3)
      (order : ℕ) (horder : order ≤ 3) :
      ‖iteratedFDeriv ℝ order
        (fun y : R3 => (referenceRadius delta A p L y)^a •
          Tl (q,(y,referenceRadius delta A p L y))) x‖ ≤
        Cscaled*eta^a*beta^order/beta^(2*a) ∧
      ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ order
        (fun y : R3 => (referenceRadius delta A p L y)^a •
          Nhalf i j (q,(y,referenceRadius delta A p L y))) x‖ ≤
        Cscaled*eta^a*beta^order/beta^(2*a) := by
    have hPrimitive := hPoint.2.2.2 1 (by norm_num) a ha1 ha3 order horder
    refine ⟨?_,?_⟩
    · simpa only [one_mul] using hPrimitive.2.2.2.1
    · intro i j
      simpa only [one_mul] using (hPrimitive.2.2.2.2 i j).2.1
  intro power hpower1 hpower2 i word hw
  have hScale : 0 ≤ eta^power*beta^word.length/beta^(2*power) :=
    div_nonneg (mul_nonneg (pow_nonneg heta.le _)
      (pow_nonneg (zero_le_one.trans hPoint.2.1) _))
      (pow_nonneg (zero_le_one.trans hPoint.2.1) _)
  have hHigh := hHighApply dGeom hdGeom hdGeomρ hdGeom1 hRoom
    Cscaled hC0 p hp1 eta heta heta1 A hA q hq delta hdelta hdelta1 x hx
    hPoint.1 hPoint.2.1 hRawHigh power hpower1 hpower2 i word hw
  have hLow := hLowApply dGeom hdGeom hdGeomρ hdGeom1 hRoom
    Cscaled hC0 p hp1 eta heta heta1 A hA q hq delta hdelta hdelta1 x hx
    hPoint.1 hPoint.2.1 hRawLow power hpower1 hpower2 i word hw
  refine ⟨hHigh.trans ?_,hLow.trans ?_⟩
  · calc
      Ch*eta^power*beta^word.length/beta^(2*power) =
          Ch*(eta^power*beta^word.length/beta^(2*power)) := by ring
      _ ≤ CE*(eta^power*beta^word.length/beta^(2*power)) :=
        mul_le_mul_of_nonneg_right hChCE hScale
      _ = CE*eta^power*beta^word.length/beta^(2*power) := by ring
  · calc
      Cl*eta^power*beta^word.length/beta^(2*power) =
          Cl*(eta^power*beta^word.length/beta^(2*power)) := by ring
      _ ≤ CE*(eta^power*beta^word.length/beta^(2*power)) :=
        mul_le_mul_of_nonneg_right hClCE hScale
      _ = CE*eta^power*beta^word.length/beta^(2*power) := by ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referencePairedAdjointMovingDifferenceQuotient_profile_radiusPower_coordinate_word_bounds
