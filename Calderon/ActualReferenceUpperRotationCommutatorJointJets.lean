import Calderon.ActualReferenceUpperRotationCommutator
import Calderon.LocalRadialDerivative
import Calderon.CompactInverseDerivativeBounds
import Calderon.ActualReferenceRadialEndpointOpenLocus

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation

/-! The actual upper angular derivative has its original Sobolev orders. The radius below
is selected from the original three-inverse locus before N and before all nine pairs. -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceSharpRadialRotationCommutatorL_eq_fderiv
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p =
    fderiv ℝ (fun z : ℝ × (ℝ × (R3 × ℝ)) =>
      referenceOrthogonalSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
          (coordinateRotationIsometry i j z.1) z.2) (0,p) (1,0) := by
  let Q : ℝ × (ℝ × (R3 × ℝ)) →
      SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) := fun z =>
    referenceOrthogonalSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
        (coordinateRotationIsometry i j z.1) z.2
  have hQ : ContDiffAt ℝ ∞ Q (0,p) :=
    contDiffAt_referenceOrthogonalSharpRadialTraceFamily_joint_zero_angle
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hStrong hWeak
  have hc : HasDerivAt (fun θ : ℝ => (θ,p)) (1,0) 0 :=
    (hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) p)
  change deriv (fun θ : ℝ => Q (θ,p)) 0 = fderiv ℝ Q (0,p) (1,0)
  simpa only [Function.comp_def] using
    ((hQ.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc).deriv

lemma contDiffAt_referenceSharpRadialRotationCommutatorL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ContDiffAt ℝ ∞
      (referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) p := by
  let Q : ℝ × (ℝ × (R3 × ℝ)) →
      SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) := fun z =>
    referenceOrthogonalSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
        (coordinateRotationIsometry i j z.1) z.2
  let F : (ℝ × (R3 × ℝ)) × ℝ →
      SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) := fun z => Q (z.2,z.1)
  have hQ : ContDiffAt ℝ ∞ Q (0,p) :=
    contDiffAt_referenceOrthogonalSharpRadialTraceFamily_joint_zero_angle
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hStrong hWeak
  have hF : ContDiffAt ℝ ∞ F (p,0) :=
    hQ.comp (p,0) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hG : ContDiffAt ℝ ∞ (fun p' : ℝ × (R3 × ℝ) => radialFirstDerivative F (p',0)) p :=
    (contDiffAt_radialFirstDerivative F (p,0) hF).comp p
      (contDiffAt_id.prodMk contDiffAt_const)
  have hNearby : ∀ᶠ z in 𝓝 (p,(0:ℝ)), DifferentiableAt ℝ F z := by
    filter_upwards [(hF.of_le (show (1:ℕ∞ω) ≤ (∞:ℕ∞ω) by simp)).eventually (by simp)] with z hz
    exact hz.differentiableAt (by norm_num)
  have hNearbySlice := (continuous_id.prodMk (continuous_const (y := (0:ℝ)))).continuousAt.eventually hNearby
  apply hG.congr_of_eventuallyEq
  filter_upwards [hNearbySlice] with p' hp'
  change deriv (fun θ : ℝ => F (p',θ)) 0 = radialFirstDerivative F (p',0)
  exact deriv_radialSlice_of_differentiableAt F p' 0 hp'

theorem exists_reference_commonRadius_sharpRadialRotationCommutator_jets
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ N : ℕ,
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ p ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ),
          p ∈ referenceRadialEndpointInvertibleLocus
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
          ∀ i j : Fin 3,
            ContDiffAt ℝ ∞
              (referenceSharpRadialRotationCommutatorL
                g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) p ∧
            ∀ k : ℕ, k ≤ N →
              ‖iteratedFDeriv ℝ k
                (referenceSharpRadialRotationCommutatorL
                  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) p‖ ≤ M := by
  classical
  obtain ⟨δ,hδ,hδρ,hRoom⟩ := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  let K : Set (ℝ × (R3 × ℝ)) :=
    Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)
  let Cij : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
      SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hK : IsCompact K :=
    isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  have hSmooth : ∀ i j : Fin 3, ∀ p ∈ K, ContDiffAt ℝ ∞ (Cij i j) p := by
    intro i j p hp
    have hi := hRoom hp
    exact contDiffAt_referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hi.1 hi.2.1
  refine ⟨δ,hδ,hδρ,?_⟩
  intro N
  have hb (i j : Fin 3) : ∃ M : ℝ, 0 ≤ M ∧
      ∀ k : ℕ, k ≤ N → ∀ p ∈ K, ‖iteratedFDeriv ℝ k (Cij i j) p‖ ≤ M :=
    exists_compact_iteratedFDeriv_bound (Cij i j) K hK (hSmooth i j) N
  let Mij : Fin 3 → Fin 3 → ℝ := fun i j => Classical.choose (hb i j)
  have hM (i j : Fin 3) : 0 ≤ Mij i j ∧
      ∀ k : ℕ, k ≤ N → ∀ p ∈ K, ‖iteratedFDeriv ℝ k (Cij i j) p‖ ≤ Mij i j :=
    Classical.choose_spec (hb i j)
  have hSum (i : Fin 3) : 0 ≤ ∑ j : Fin 3, Mij i j :=
    Finset.sum_nonneg (fun j _ => (hM i j).1)
  refine ⟨∑ i : Fin 3, ∑ j : Fin 3, Mij i j,
    Finset.sum_nonneg (fun i _ => hSum i),?_⟩
  intro p hp
  refine ⟨hRoom hp,?_⟩
  intro i j
  refine ⟨hSmooth i j p hp,?_⟩
  intro k hk
  exact ((hM i j).2 k hk p hp).trans
    ((Finset.single_le_sum (fun j' _ => (hM i j').1) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i' _ => hSum i') (Finset.mem_univ i)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialRotationCommutatorL_eq_fderiv
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceSharpRadialRotationCommutatorL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_sharpRadialRotationCommutator_jets
