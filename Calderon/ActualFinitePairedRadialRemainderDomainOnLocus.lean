import Calderon.ActualFinitePairedRadialRemainderGraphRoom
import Calderon.ActualFiniteGaugePairedRadialRemainderDomain
import Calderon.ActualReferenceRadialEndpointOpenLocus

/-! Full before-source: actual-high-first-output-domain-plan-oct16-v001/
EXPANSION-quartic-actual-domain-on-locus-factor-v013.md and
EXPANSION-domain-on-locus-implementation-v014.md. One actual inverse room and
paired signed-R2 first-output domain before every original finite product input. -/
set_option autoImplicit false
noncomputable section
open Set Metric
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

attribute [local irreducible] harmonicSphereSubspace secondTaylorRemainder
  referenceSharpRadialTraceFamily referenceAdjointThreeHalfRadialFamily
  referenceFiniteHarmonicProductHighSecondRemainder referenceFiniteGaugeAdjointSecondRemainder
  nativeThreeHalfCoefficientMulL sphereSobolevInclusionL sphereSobolevPartialSum
  referencePairedRadialSecondRemainderGraph referenceRadialEndpointInvertibleLocus

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem exists_reference_commonRadius_finitePairedRadialSecondRemainder_domain_on_locus
    (hg : IsAdmissibleMetric g)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)) ⊆
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ →
        ∀ r : ℝ, |r| ≤ δ →
        ∀ (n : ℕ) (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2 : ℝ)),
          referencePairedRadialSecondRemainderGraph
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
            (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
              (sphereSobolevPartialSum (3/2 : ℝ) n f)) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_PAIRED_DOMAIN_LOCUS_BODY"
    out.flush
  let R : ReferenceFinitePairedRadialRemainderSectionRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 :=
    Classical.choice (exists_referenceFinitePairedRadialRemainderSectionRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_PAIRED_DOMAIN_LOCUS_NOMINAL_ROOM"
    out.flush
  obtain ⟨dΩ,hdΩ,hdΩρ,hΩ⟩ := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL_PAIRED_DOMAIN_LOCUS_OMEGA_RADIUS"
    out.flush
  let δ : ℝ := min dΩ (min R.primalRadius R.adjointRadius)
  have hδ : 0 < δ := lt_min hdΩ (lt_min R.primalRadius_pos R.adjointRadius_pos)
  have hδΩ : δ ≤ dΩ := min_le_left _ _
  have hδP : δ ≤ R.primalRadius := (min_le_right _ _).trans (min_le_left _ _)
  have hδA : δ ≤ R.adjointRadius := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,hδ,hδΩ.trans hdΩρ,?_,?_⟩
  · intro p hp
    exact hΩ ⟨hp.1,hp.2.1,(Icc_subset_Icc (neg_le_neg hδΩ) hδΩ) hp.2.2⟩
  · intro q hq y hy r hr n Q f
    let su : SphereSobolev (3/2 : ℝ) := referenceFiniteHarmonicProductHighSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n Q q y r f
    let tu : SphereSobolev (3/2 : ℝ) := referenceFiniteGaugeAdjointSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R.gauge n Q q y r f
    run_tac do
      let out ← IO.getStdout
      out.putStrLn "ACTUAL_PAIRED_DOMAIN_LOCUS_ORIGINAL_PAIR_GRAPHS"
      out.flush
    unfold referencePairedRadialSecondRemainderGraph
    refine ⟨su,tu,?_,?_⟩
    · exact R.primalGraph q hq y hy r (hr.trans hδP) n Q f
    · exact R.adjointGraph q hq y hy r (hr.trans hδA) n Q f

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finitePairedRadialSecondRemainder_domain_on_locus
