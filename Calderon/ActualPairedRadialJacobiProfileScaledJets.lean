import Calderon.ActualPairedRadialJacobiConditionalProfileJets
import Calderon.ActualRadiusThreeJetProfileRoom
import Calderon.ActualFinitePairedRadialQuarticDomain

/-! Full before-source: actual-covariant-leading-algebra-author-oct16-v001/
EXPANSION-original-common-profile-direct-conditional-consumer-v073.md.
ONE profile amplitude for four literal remainder components and all three Jacobi native endpoints.
The explicit finite-quartic import requests the original production import union. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualHigherRadiusProfile
  ConformalDepth RadiusProfile ReferenceWeightedApproximation
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier

local instance referencePairedJacobiProfileHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referencePairedJacobiProfileNegativeCompleteSpace :
    CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referencePairedJacobiProfileHighOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
  infer_instance

local instance referencePairedJacobiProfileLowOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := by
  infer_instance

attribute [local irreducible] harmonicSphereSubspace referenceSharpRadialTraceSecondRemainder
  referenceLowerRadialTraceSecondRemainder referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily referenceRadialEndpointInvertibleLocus secondTaylorRemainder

theorem exists_referencePairedRadialJacobi_profile_scaled_jets
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
    ∃ dGeom Cscaled : ℝ, 0 < dGeom ∧ dGeom ≤ ρ ∧ dGeom ≤ 1 ∧
      ((Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dGeom) dGeom)) ⊆
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      1 ≤ Cscaled ∧ ∃ p0 : ℕ, 2 ≤ p0 ∧
      ∀ p : ℕ, p0 ≤ p → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
      ∃ A : ℝ, 0 < A ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ x ∈ K,
        let beta := actualReferenceBeta g L q delta A p x
        referenceRadius delta A p L x ≤ dGeom ∧ 1 ≤ beta ∧
        referenceRadius delta A p L x * beta^2 ≤ eta ∧
        ∀ s : ℝ, |s| ≤ 1 → ∀ power : ℕ, 1 ≤ power → power ≤ 3 →
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
            Cscaled * eta^power * beta^order / beta^(2*power) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_JACOBI_PROFILE BODY_ENTER"
    out.flush
  intro Sh Sl Th Tl Nhi Nhalf Nneg
  have hConditional := exists_referencePairedRadialJacobi_scaled_jets_of_profile_bounds
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg hg hL K hK hKgeom
  rcases hConditional with
    ⟨dGeom,Cscaled,hdGeom,hdGeomρ,hdGeom1,hRoom,hCscaled,hApply⟩
  let scalar := Classical.choice (exists_referenceRadiusThreeJetProfileRoom g hg L hL K hK)
  let p0 : ℕ := scalar.threshold
  have hp02 : 2 ≤ p0 := scalar.two_le_threshold
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_JACOBI_PROFILE CONDITIONAL_READY"
    out.flush
  refine ⟨dGeom,Cscaled,hdGeom,hdGeomρ,hdGeom1,hRoom,hCscaled,p0,hp02,?_⟩
  intro p hp eta heta heta1
  let etaEff : ℝ := min eta dGeom
  have hetaEff : 0 < etaEff := lt_min heta hdGeom
  have hetaEffEta : etaEff ≤ eta := min_le_left _ _
  have hetaEffD : etaEff ≤ dGeom := min_le_right _ _
  have hetaEff1 : etaEff ≤ 1 := hetaEffEta.trans heta1
  have hProfile := scalar.profile p hp etaEff hetaEff hetaEff1
  rcases hProfile with ⟨A,hA,hAll⟩
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_JACOBI_PROFILE AMPLITUDE_READY"
    out.flush
  refine ⟨A,hA,?_⟩
  intro q hq delta hdelta hdelta1 x hx
  have hPoint := hAll q hq delta hdelta hdelta1 x hx
  have hbeta := hPoint.1
  have hPower := hPoint.2.1.trans hetaEffEta
  have hRadius := hPoint.2.2.trans hetaEffD
  have hp1 : 1 ≤ p := by omega
  have hJets := hApply q hq delta hdelta hdelta1 A hA p hp1 eta heta x hx
    hbeta hRadius hPower
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_JACOBI_PROFILE ASSEMBLY_READY"
    out.flush
  exact ⟨hRadius,hbeta,hPower,hJets⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
