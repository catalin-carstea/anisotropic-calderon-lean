import Calderon.ActualReferenceAdjointHighRotationCovariance
import Calderon.SphereSobolevUpperRotationDistributionSpecialization
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Calderon.CompactInverseDerivativeBounds
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic SmoothSphereRotation SpectralWeightedGraph
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3)
attribute [local irreducible] referenceRotationAdjointThreeHalfRadialFamily

def referenceAdjointHighAngleDerivativeFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  fderiv ℝ (referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j) (0,p) (1,0)

lemma referenceAdjointHighAngleDerivativeFamily_eq_deriv
    (hreg : FixedDirichletRegularity)
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceAdjointHighAngleDerivativeFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p =
      deriv (fun θ : ℝ => referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 i j (θ,p)) 0 := by
  let M := referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j
  have hM : ContDiffAt ℝ ∞ M (0,p) :=
    (contDiffOn_referenceRotationAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j hreg).contDiffAt
        ((isOpen_univ.prod (isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)).mem_nhds ⟨mem_univ _,hp⟩)
  have hc : HasDerivAt (fun θ : ℝ => (θ,p)) (1,0) 0 :=
    (hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) p)
  change fderiv ℝ M (0,p) (1,0) = deriv (fun θ : ℝ => M (θ,p)) 0
  exact ((hM.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc).deriv.symm

lemma contDiffOn_referenceAdjointHighAngleDerivativeFamily_invertibleLocus
    (hreg : FixedDirichletRegularity) :
    ContDiffOn ℝ ∞
      (referenceAdjointHighAngleDerivativeFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  let Ω := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let M := referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ Ω) :=
    contDiffOn_referenceRotationAdjointThreeHalfRadialFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 i j hreg
  have hDM : ContDiffOn ℝ ∞ (fderiv ℝ M) (Set.univ ×ˢ Ω) :=
    hM.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) (isOpen_univ.prod hΩ) (by simp)
  have hEval : ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × (R3 × ℝ)) => fderiv ℝ M z (1,0)) (Set.univ ×ˢ Ω) :=
    hDM.clm_apply contDiffOn_const
  change ContDiffOn ℝ ∞ (fun p : ℝ × (R3 × ℝ) => fderiv ℝ M (0,p) (1,0)) Ω
  exact hEval.comp (contDiffOn_const.prodMk contDiffOn_id) (fun p hp => ⟨mem_univ _,hp⟩)

lemma referenceAdjointHighAngleDerivativeFamily_rotation_graph
    (hreg : FixedDirichletRegularity) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (f : SphereSobolev (5/2:ℝ)) :
    sphereSobolevRotationL (1/2:ℝ) i j
      (referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f)) -
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
          (sphereSobolevRotationL (5/2:ℝ) i j f)) =
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceAdjointHighAngleDerivativeFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
          (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f)) := by
  let M := referenceRotationAdjointThreeHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j
  have hM : ContDiffAt ℝ ∞ M (0,p) :=
    (contDiffOn_referenceRotationAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j hreg).contDiffAt
        ((isOpen_univ.prod (isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)).mem_nhds ⟨mem_univ _,hp⟩)
  have hc : HasDerivAt (fun θ : ℝ => (θ,p)) (1,0) 0 :=
    (hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) p)
  have hDerivative : HasDerivAt (fun θ : ℝ => M (θ,p))
      (referenceAdjointHighAngleDerivativeFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p) 0 :=
    (hM.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hCov : ∀ᶠ θ in 𝓝 (0:ℝ), ∀ u : SphereSobolev (3/2:ℝ),
      M (θ,p) (sphereSobolevOrthogonalPullbackL (3/2:ℝ) (coordinateRotationIsometry i j θ) u) =
        sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry i j θ)
          (referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p u) :=
    Filter.Eventually.of_forall (fun θ u =>
      referenceRotationAdjointThreeHalfRadialFamily_coordinate_covariance
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg i j θ p hp.2.2 hp.1 hp.2.1 u)
  have h := sphereSobolev_upper_rotation_derivative_distribution hO hD i j
    (fun θ => M (θ,p))
    (referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)
    (referenceAdjointHighAngleDerivativeFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p)
    hDerivative hCov f
  rw [map_add] at h
  exact sub_eq_iff_eq_add.mpr h

theorem exists_reference_commonRadius_adjointHighAngleDerivative_jets
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
              (referenceAdjointHighAngleDerivativeFamily
                g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) p ∧
            ∀ k : ℕ, k ≤ N →
              ‖iteratedFDeriv ℝ k
                (referenceAdjointHighAngleDerivativeFamily
                  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) p‖ ≤ M := by
  classical
  obtain ⟨δ,hδ,hδρ,hRoom⟩ := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  let K : Set (ℝ × (R3 × ℝ)) :=
    Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)
  let Cij : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
      SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    referenceAdjointHighAngleDerivativeFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hK : IsCompact K :=
    isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  have hSmooth : ∀ i j : Fin 3, ∀ p ∈ K, ContDiffAt ℝ ∞ (Cij i j) p := by
    intro i j p hp
    have hi := hRoom hp
    exact (contDiffOn_referenceAdjointHighAngleDerivativeFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j hreg).contDiffAt
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hi)
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
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointHighAngleDerivativeFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointHighAngleDerivativeFamily_eq_deriv
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceAdjointHighAngleDerivativeFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointHighAngleDerivativeFamily_rotation_graph

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_adjointHighAngleDerivative_jets
