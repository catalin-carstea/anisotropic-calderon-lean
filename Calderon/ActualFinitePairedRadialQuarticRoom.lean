import Calderon.ActualFinitePairedRadialRemainderGraphRoom
import Calderon.ActualReferenceSignedRemainderPivot
import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.SphereSobolevQuarticPivotIdentity

/-! Full before-source: actual-high-first-output-domain-plan-oct16-v001/
EXPANSION-actual-nominal-quartic-room-v016.md and
EXPANSION-nominal-quartic-room-implementation-v017.md. Actual canonical
uncompressed first outputs; every second output remains Hhalf. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

attribute [local irreducible] harmonicSphereSubspace
  referenceSharpRadialTraceSecondRemainder referenceLowerRadialTraceSecondRemainder
  referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily secondTaylorRemainder
  sphereSobolevInclusionL nativeThreeHalfCoefficientMulL sphereSobolevPartialSum
  sphereSobolevDualPairing referenceFiniteHarmonicProductHighSecondRemainder
  referenceFiniteGaugeAdjointSecondRemainder referenceRadialEndpointInvertibleLocus
  referenceSharpRadialTraceFamily

structure ReferenceFinitePairedRadialQuarticRoom
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) where
  domain : ReferenceFinitePairedRadialRemainderSectionRoom
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ ρ
  primal_radius_bound : radius ≤ domain.primalRadius
  adjoint_radius_bound : radius ≤ domain.adjointRadius
  endpointRoom :
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-radius) radius)) ⊆
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  orderedPivot :
    ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ →
      ∀ r : ℝ, |r| ≤ radius →
      ∀ (n N : ℕ) (Q V : SmoothCoefficientJets 3)
        (f h : SphereSobolev (3/2 : ℝ)),
        let Sh : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
          referenceSharpRadialTraceSecondRemainder
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
        let Sl : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
          referenceLowerRadialTraceSecondRemainder
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
        let Th : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
          secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
        let Tl : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
          secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
        let Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
          sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        let P : SphereSobolev (-(1/2 : ℝ)) → SphereSobolev (1/2 : ℝ) → ℝ :=
          fun x z => sphereSobolevDualPairing (-(1/2 : ℝ)) x z
        let u : SphereSobolev (3/2 : ℝ) := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
          (sphereSobolevPartialSum (3/2 : ℝ) n f)
        let v : SphereSobolev (3/2 : ℝ) := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 V
          (sphereSobolevPartialSum (3/2 : ℝ) N h)
        let su : SphereSobolev (3/2 : ℝ) := referenceFiniteHarmonicProductHighSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n Q q y r f
        let tu : SphereSobolev (3/2 : ℝ) := referenceFiniteGaugeAdjointSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 domain.gauge n Q q y r f
        let sv : SphereSobolev (3/2 : ℝ) := referenceFiniteHarmonicProductHighSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 N V q y r h
        let tv : SphereSobolev (3/2 : ℝ) := referenceFiniteGaugeAdjointSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 domain.gauge N V q y r h
        P (Tl (Sh su) - Sl (Th su)) (Sh v) +
          P (Tl (Sh u)) (Th sv - Sh tv) +
          P (Tl (Th su - Sh tu)) (Th v) +
          P (Tl (Sh tu) - Sl (Th tu)) (Th v) =
            ⟪Z (Sh su),Z (Sh sv)⟫_ℝ - ⟪Z (Th tu),Z (Th tv)⟫_ℝ

run_cmd do
  let out ← IO.getStdout
  out.putStrLn "ACTUAL_QUARTIC_ROOM_DATA_DECLARED"
  out.flush

theorem exists_referenceFinitePairedRadialQuarticRoom
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) :
    Nonempty (ReferenceFinitePairedRadialQuarticRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_QUARTIC_ROOM_BODY"
    out.flush
  let D : ReferenceFinitePairedRadialRemainderSectionRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 :=
    Classical.choice (exists_referenceFinitePairedRadialRemainderSectionRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_QUARTIC_ROOM_DOMAIN"
    out.flush
  obtain ⟨dΩ,hdΩ,hdΩρ,hΩ⟩ := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_QUARTIC_ROOM_OMEGA_RADIUS"
    out.flush
  let δ : ℝ := min dΩ (min D.primalRadius D.adjointRadius)
  have hδ : 0 < δ := lt_min hdΩ (lt_min D.primalRadius_pos D.adjointRadius_pos)
  have hδΩ : δ ≤ dΩ := min_le_left _ _
  have hδP : δ ≤ D.primalRadius := (min_le_right _ _).trans (min_le_left _ _)
  have hδA : δ ≤ D.adjointRadius := (min_le_right _ _).trans (min_le_right _ _)
  have hRoom : (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)) ⊆
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
    intro p hp
    exact hΩ ⟨hp.1,hp.2.1,(Icc_subset_Icc (neg_le_neg hδΩ) hδΩ) hp.2.2⟩
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_QUARTIC_ROOM_SAFE_ROOM"
    out.flush
  refine ⟨{
    domain := D
    radius := δ
    radius_pos := hδ
    radius_le := hδΩ.trans hdΩρ
    primal_radius_bound := hδP
    adjoint_radius_bound := hδA
    endpointRoom := hRoom
    orderedPivot := ?_
  }⟩
  intro q hq y hy r hr n N Q V f h
  intro Sh Sl Th Tl Z P u v su tu sv tv
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hsu : I su = Sh u := by
    simpa only [Sh,referenceSharpRadialTraceSecondRemainder] using
      (D.primalGraph q hq y hy r (hr.trans hδP) n Q f)
  have htu : I tu = Th u :=
    D.adjointGraph q hq y hy r (hr.trans hδA) n Q f
  have hsv : I sv = Sh v := by
    simpa only [Sh,referenceSharpRadialTraceSecondRemainder] using
      (D.primalGraph q hq y hy r (hr.trans hδP) N V h)
  have htv : I tv = Th v :=
    D.adjointGraph q hq y hy r (hr.trans hδA) N V h
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_QUARTIC_ROOM_FOUR_FIRST_OUTPUT_GRAPHS"
    out.flush
  have hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
    intro θ hθ
    have hθabs : |θ| ≤ 1 := by
      rw [abs_of_nonneg hθ.1]
      exact hθ.2
    have hθrAbs : |θ*r| ≤ |r| := by
      simpa only [abs_mul,one_mul] using
        (mul_le_mul_of_nonneg_right hθabs (abs_nonneg r))
    have hθr : |θ*r| ≤ δ := hθrAbs.trans hr
    exact hRoom ⟨hq,⟨by simpa only [mem_closedBall,dist_eq_norm] using hy,abs_le.mp hθr⟩⟩
  have hPivots := referenceRadialSecondRemainder_genuine_pivot_pairings
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment
  have hSAdj : ∀ z : SphereSobolev (1/2 : ℝ), ∀ b : SphereSobolev (3/2 : ℝ),
      P (Sl z) (I b) = ⟪Z z,Z (Th b)⟫_ℝ := hPivots.1
  have hTAdj : ∀ z : SphereSobolev (1/2 : ℝ), ∀ b : SphereSobolev (3/2 : ℝ),
      P (Tl z) (I b) = ⟪Z z,Z (Sh b)⟫_ℝ := hPivots.2
  have hT := referenceAdjointRadialSecondRemainder_high_half_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment
  have hTsu : J (Th su) = Tl (I su) := by
    have hEval := congrArg
      (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T su) hT
    simpa only [ContinuousLinearMap.comp_apply] using hEval
  have hTS : Tl (Sh u) = J (Th su) :=
    (congrArg Tl hsu.symm).trans hTsu.symm
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_QUARTIC_ROOM_GENUINE_PIVOTS_COHERENCE"
    out.flush
  have hOne : P (Tl (Sh su) - Sl (Th su)) (Sh v) =
      ⟪Z (Sh su),Z (Sh sv)⟫_ℝ - ⟪Z (Th su),Z (Th sv)⟫_ℝ := by
    have hTest := congrArg
      (fun z : SphereSobolev (1/2 : ℝ) => P (Tl (Sh su) - Sl (Th su)) z) hsv.symm
    have hSplit : P (Tl (Sh su) - Sl (Th su)) (I sv) =
        P (Tl (Sh su)) (I sv) - P (Sl (Th su)) (I sv) :=
      sphereSobolevHalfDualPairing_sub_left (Tl (Sh su)) (Sl (Th su)) (I sv)
    exact hTest.trans (hSplit.trans
      (congrArg₂ (fun x z : ℝ => x-z) (hTAdj (Sh su) sv) (hSAdj (Th su) sv)))
  have hTwo : P (Tl (Sh u)) (Th sv - Sh tv) =
      ⟪Z (Th su),Z (Th sv)⟫_ℝ - ⟪Z (Th su),Z (Sh tv)⟫_ℝ := by
    have hGraph := congrArg
      (fun z : SphereSobolev (-(1/2 : ℝ)) => P z (Th sv - Sh tv)) hTS
    have hPairing : P (J (Th su)) (Th sv - Sh tv) =
        ⟪Z (Th su),Z (Th sv - Sh tv)⟫_ℝ :=
      sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num)
        (Th su) (Th sv - Sh tv)
    have hInner : ⟪Z (Th su),Z (Th sv - Sh tv)⟫_ℝ =
        ⟪Z (Th su),Z (Th sv)⟫_ℝ - ⟪Z (Th su),Z (Sh tv)⟫_ℝ := by
      have hSub : Z (Th sv - Sh tv) = Z (Th sv) - Z (Sh tv) :=
        Z.map_sub (Th sv) (Sh tv)
      have hLift : ⟪Z (Th su),Z (Th sv - Sh tv)⟫_ℝ =
          ⟪Z (Th su),Z (Th sv) - Z (Sh tv)⟫_ℝ :=
        congrArg (fun z : SphereSobolev 0 => ⟪Z (Th su),z⟫_ℝ) hSub
      exact hLift.trans (inner_sub_right (Z (Th su)) (Z (Th sv)) (Z (Sh tv)))
    exact hGraph.trans (hPairing.trans hInner)
  have hThree : P (Tl (Th su - Sh tu)) (Th v) =
      ⟪Z (Th su),Z (Sh tv)⟫_ℝ - ⟪Z (Sh tu),Z (Sh tv)⟫_ℝ := by
    have hTest := congrArg
      (fun z : SphereSobolev (1/2 : ℝ) => P (Tl (Th su - Sh tu)) z) htv.symm
    have hInner : ⟪Z (Th su - Sh tu),Z (Sh tv)⟫_ℝ =
        ⟪Z (Th su),Z (Sh tv)⟫_ℝ - ⟪Z (Sh tu),Z (Sh tv)⟫_ℝ := by
      have hSub : Z (Th su - Sh tu) = Z (Th su) - Z (Sh tu) :=
        Z.map_sub (Th su) (Sh tu)
      have hLift : ⟪Z (Th su - Sh tu),Z (Sh tv)⟫_ℝ =
          ⟪Z (Th su) - Z (Sh tu),Z (Sh tv)⟫_ℝ :=
        congrArg (fun z : SphereSobolev 0 => ⟪z,Z (Sh tv)⟫_ℝ) hSub
      exact hLift.trans (inner_sub_left (Z (Th su)) (Z (Sh tu)) (Z (Sh tv)))
    exact hTest.trans ((hTAdj (Th su - Sh tu) tv).trans hInner)
  have hFour : P (Tl (Sh tu) - Sl (Th tu)) (Th v) =
      ⟪Z (Sh tu),Z (Sh tv)⟫_ℝ - ⟪Z (Th tu),Z (Th tv)⟫_ℝ := by
    have hTest := congrArg
      (fun z : SphereSobolev (1/2 : ℝ) => P (Tl (Sh tu) - Sl (Th tu)) z) htv.symm
    have hSplit : P (Tl (Sh tu) - Sl (Th tu)) (I tv) =
        P (Tl (Sh tu)) (I tv) - P (Sl (Th tu)) (I tv) :=
      sphereSobolevHalfDualPairing_sub_left (Tl (Sh tu)) (Sl (Th tu)) (I tv)
    exact hTest.trans (hSplit.trans
      (congrArg₂ (fun x z : ℝ => x-z) (hTAdj (Sh tu) tv) (hSAdj (Th tu) tv)))
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_QUARTIC_ROOM_FOUR_SCALAR_DIFFERENCES"
    out.flush
  have h12 := (congrArg₂ (fun x z : ℝ => x+z) hOne hTwo).trans
    (sub_add_sub_cancel
      (⟪Z (Sh su),Z (Sh sv)⟫_ℝ)
      (⟪Z (Th su),Z (Th sv)⟫_ℝ)
      (⟪Z (Th su),Z (Sh tv)⟫_ℝ))
  have h123 := (congrArg₂ (fun x z : ℝ => x+z) h12 hThree).trans
    (sub_add_sub_cancel
      (⟪Z (Sh su),Z (Sh sv)⟫_ℝ)
      (⟪Z (Th su),Z (Sh tv)⟫_ℝ)
      (⟪Z (Sh tu),Z (Sh tv)⟫_ℝ))
  exact (congrArg₂ (fun x z : ℝ => x+z) h123 hFour).trans
    (sub_add_sub_cancel
      (⟪Z (Sh su),Z (Sh sv)⟫_ℝ)
      (⟪Z (Sh tu),Z (Sh tv)⟫_ℝ)
      (⟪Z (Th tu),Z (Th tv)⟫_ℝ))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceFinitePairedRadialQuarticRoom
