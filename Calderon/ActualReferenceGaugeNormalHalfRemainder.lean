import Calderon.ActualReferenceGaugeNormalHalfCommutator
import Calderon.LocalSmoothSignedTaylorRemainder
import Calderon.CompactInverseDerivativeBounds

/-! Full upfront: general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-actual-gauge-normal-half-remainder-v073.md. Literal signed integral
normal remainder; correct generally nonzero firstjet is subtracted. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

local instance instCompleteSpaceGaugeNormalHalfRemainder : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance instCompleteSpaceGaugeNormalHalfRemainderEnd : CompleteSpace
    (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance

def referenceGaugeNormalHalfSecondRemainder (q : ℝ) (y : R3) (r : ℝ) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  secondTaylorRemainder (fun t : ℝ => referenceGaugeNormalHalfCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,t))) r

attribute [local irreducible] referenceGaugeNormalHalfSecondRemainder
  referenceGaugeNormalHalfCommutatorFamily referenceRadialEndpointInvertibleLocus
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceNormalBoundaryMultiplierFamily
  sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL referenceCenterDrift

lemma contDiffAt_referenceGaugeNormalHalfSecondRemainder_of_segment
    (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (R3 × ℝ) => referenceGaugeNormalHalfSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p.1 p.2.1 p.2.2) (q,(y,r)) := by
  let F : (ℝ × R3) × ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun p =>
    referenceGaugeNormalHalfCommutatorFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      (p.1.1,(p.1.2,p.2))
  let Ω : Set ((ℝ × R3) × ℝ) := {p | (p.1.1,(p.1.2,p.2)) ∈
    referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0}
  have hΩ : IsOpen Ω := (isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).preimage
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hF : ContDiffOn ℝ ∞ F Ω := by
    intro p hp
    have h := contDiffAt_referenceGaugeNormalHalfCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (p.1.1,(p.1.2,p.2)) hp
    exact (h.comp (f := fun z : (ℝ × R3) × ℝ => (z.1.1,(z.1.2,z.2))) p
      (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))).contDiffWithinAt
  have hR := contDiffAt_secondTaylorRemainder_joint_of_open_segment F Ω hΩ hF (q,y) r hSegment
  have hPerm : ContDiffAt ℝ ∞ (fun p : ℝ × (R3 × ℝ) => ((p.1,p.2.1),p.2.2)) (q,(y,r)) :=
    (contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd
  simpa only [referenceGaugeNormalHalfSecondRemainder,Function.comp_def] using
    hR.comp (f := fun p : ℝ × (R3 × ℝ) => ((p.1,p.2.1),p.2.2)) (q,(y,r)) hPerm

set_option diagnostics true in
lemma referenceGaugeNormalHalfCommutatorFamily_radial_taylor
    (hKernel : UnitBallValueTraceKernel τ0) (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r : ℝ)
    (hSegment : ∀ t ∈ uIcc (0 : ℝ) r, (q,(y,t)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceGaugeNormalHalfCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r)) =
    r • (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y) -
      sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y)) +
    r^2 • referenceGaugeNormalHalfSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r := by
  run_tac do
    let h ← IO.getStdout
    h.putStrLn "normal half Taylor enter"
    h.flush
  let F : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun t =>
    referenceGaugeNormalHalfCommutatorFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,t))
  let V : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y) -
      sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y)
  have hSmooth (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) r) : ContDiffAt ℝ ∞ F t :=
    (contDiffAt_referenceGaugeNormalHalfCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,t)) (hSegment t ht)).comp
        (f := fun z : ℝ => (q,(y,z))) t
        (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  run_tac do
    let h ← IO.getStdout
    h.putStrLn "normal half Taylor smooth-ready"
    h.flush
  have hTaylor : F r = F 0 + r • deriv F 0 + r^2 • secondTaylorRemainder F r :=
    signed_taylor_integral_remainder F r hSmooth
  run_tac do
    let h ← IO.getStdout
    h.putStrLn "normal half Taylor integral-ready"
    h.flush
  have hJets : F 0 = 0 ∧ HasDerivAt F V 0 :=
    referenceGaugeNormalHalfCommutatorFamily_zero_radial_jet
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hKernel hreg q hq y hy
  run_tac do
    let h ← IO.getStdout
    h.putStrLn "normal half Taylor jets-ready"
    h.flush
  have hF0 : F 0 = 0 := hJets.1
  have hF1 : deriv F 0 = V := by
    have hFrechet := hJets.2.hasFDerivAt.fderiv
    have hEval := congrArg
      (fun T : ℝ →L[ℝ] (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) => T 1) hFrechet
    simpa only [deriv,ContinuousLinearMap.toSpanSingleton_apply,one_smul] using hEval
  run_tac do
    let h ← IO.getStdout
    h.putStrLn "normal half Taylor derivative-ready"
    h.flush
  have hPolynomial : F 0 + r • deriv F 0 + r^2 • secondTaylorRemainder F r =
      r • V + r^2 • secondTaylorRemainder F r := by
    have hValues := congrArg₂
      (fun x v : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
        x + r • v + r^2 • secondTaylorRemainder F r) hF0 hF1
    exact hValues.trans (congrArg
      (fun z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
        z + r^2 • secondTaylorRemainder F r) (zero_add (r • V)))
  have hRemainder : secondTaylorRemainder F r = referenceGaugeNormalHalfSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r := by
    unfold referenceGaugeNormalHalfSecondRemainder
    rfl
  have hResult : F r = r • V + r^2 • referenceGaugeNormalHalfSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r :=
    hTaylor.trans (hPolynomial.trans (congrArg
      (fun z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => r • V + r^2 • z) hRemainder))
  exact hResult


lemma exists_reference_commonRadius_gaugeNormalHalfSecondRemainder_jets
    (hreg : FixedDirichletRegularity) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ),
        p ∈ referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
        ∀ k : ℕ, k ≤ N → ‖iteratedFDeriv ℝ k
          (fun z : ℝ × (R3 × ℝ) => referenceGaugeNormalHalfSecondRemainder
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 z.1 z.2.1 z.2.2) p‖ ≤ M := by
  let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hRadius : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ) ⊆ Ω :=
    exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  obtain ⟨δ,hδ,hδρ,hRoom⟩ := hRadius
  let K : Set (ℝ × (R3 × ℝ)) := Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)
  let F := fun p : ℝ × (R3 × ℝ) => referenceGaugeNormalHalfSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p.1 p.2.1 p.2.2
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  have hSmooth : ∀ p ∈ K, ContDiffAt ℝ ∞ F p := by
    intro p hp
    apply contDiffAt_referenceGaugeNormalHalfSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p.1 p.2.1 p.2.2
    intro θ hθ
    have ht : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hr : |p.2.2| ≤ δ := abs_le.mpr hp.2.2
    have htr : |θ*p.2.2| ≤ δ := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans (by simpa only [one_mul] using hr)
    exact hRoom ⟨hp.1,hp.2.1,abs_le.mp htr⟩
  refine ⟨δ,hδ,hδρ,?_⟩
  intro N
  obtain ⟨M,hM,hBound⟩ := exists_compact_iteratedFDeriv_bound F K hK hSmooth N
  exact ⟨M,hM,fun p hp => ⟨hRoom hp,fun k hk => hBound k hk p hp⟩⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalHalfSecondRemainder
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceGaugeNormalHalfSecondRemainder_of_segment
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalHalfCommutatorFamily_radial_taylor
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_gaugeNormalHalfSecondRemainder_jets
