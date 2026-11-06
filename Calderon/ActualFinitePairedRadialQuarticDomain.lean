import Calderon.ActualFiniteGaugePairedRadialRemainderDomain
import Calderon.ActualReferenceSignedRemainderPivot
import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.SphereSobolevQuarticPivotIdentity
import Calderon.ActualFinitePairedRadialRemainderDomainOnLocus
import Calderon.ActualFinitePairedRadialQuarticRoom

/-! Direct actual four-difference weak identity. Common radius before both original
finite product inputs; no generic gained theorem or strong fourth composition. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceSharpRadialTraceSecondRemainder
  referenceLowerRadialTraceSecondRemainder referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily secondTaylorRemainder sphereSobolevInclusionL
  nativeThreeHalfCoefficientMulL sphereSobolevPartialSum
  referencePairedRadialSecondRemainderGraph sphereSobolevDualPairing

theorem exists_reference_commonRadius_finitePairedRadialSecondRemainder_ordered_pivot
    (hg : IsAdmissibleMetric g)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ δ →
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
          let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
            sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
          let Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
            sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
          let P : SphereSobolev (-(1/2 : ℝ)) → SphereSobolev (1/2 : ℝ) → ℝ :=
            fun x z => sphereSobolevDualPairing (-(1/2 : ℝ)) x z
          let u : SphereSobolev (3/2 : ℝ) := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
            (sphereSobolevPartialSum (3/2 : ℝ) n f)
          let v : SphereSobolev (3/2 : ℝ) := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 V
            (sphereSobolevPartialSum (3/2 : ℝ) N h)
          ∃ su tu sv tv : SphereSobolev (3/2 : ℝ),
            I su = Sh u ∧ I tu = Th u ∧ I sv = Sh v ∧ I tv = Th v ∧
            P (Tl (Sh su) - Sl (Th su)) (Sh v) +
              P (Tl (Sh u)) (Th sv - Sh tv) +
              P (Tl (Th su - Sh tu)) (Th v) +
              P (Tl (Sh tu) - Sl (Th tu)) (Th v) =
                ⟪Z (Sh su),Z (Sh sv)⟫_ℝ - ⟪Z (Th tu),Z (Th tv)⟫_ℝ := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_FINITE_QUARTIC_BODY"
    out.flush
  let R : ReferenceFinitePairedRadialQuarticRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 :=
    Classical.choice (exists_referenceFinitePairedRadialQuarticRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_FINITE_QUARTIC_OWN_QUARTIC_ROOM"
    out.flush
  refine ⟨R.radius,R.radius_pos,R.radius_le,?_⟩
  intro q hq y hy r hr n N Q V f h
  intro Sh Sl Th Tl I Z P u v
  let su : SphereSobolev (3/2 : ℝ) := referenceFiniteHarmonicProductHighSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n Q q y r f
  let tu : SphereSobolev (3/2 : ℝ) := referenceFiniteGaugeAdjointSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R.domain.gauge n Q q y r f
  let sv : SphereSobolev (3/2 : ℝ) := referenceFiniteHarmonicProductHighSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 N V q y r h
  let tv : SphereSobolev (3/2 : ℝ) := referenceFiniteGaugeAdjointSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R.domain.gauge N V q y r h
  have hsu : I su = Sh u := by
    simpa only [Sh,referenceSharpRadialTraceSecondRemainder] using
      (R.domain.primalGraph q hq y hy r (hr.trans R.primal_radius_bound) n Q f)
  have htu : I tu = Th u :=
    R.domain.adjointGraph q hq y hy r (hr.trans R.adjoint_radius_bound) n Q f
  have hsv : I sv = Sh v := by
    simpa only [Sh,referenceSharpRadialTraceSecondRemainder] using
      (R.domain.primalGraph q hq y hy r (hr.trans R.primal_radius_bound) N V h)
  have htv : I tv = Th v :=
    R.domain.adjointGraph q hq y hy r (hr.trans R.adjoint_radius_bound) N V h
  refine ⟨su,tu,sv,tv,hsu,htu,hsv,htv,?_⟩
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_FINITE_QUARTIC_FOUR_FIRST_OUTPUTS"
    out.flush
  exact R.orderedPivot q hq y hy r hr n N Q V f h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finitePairedRadialSecondRemainder_ordered_pivot
