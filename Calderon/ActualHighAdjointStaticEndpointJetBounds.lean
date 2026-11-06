import Calderon.ActualAdjointMovingBoundaryFamilyFoundation
import Calderon.JointRadialDerivativeLocalSmoothness
import Calderon.FinitePairedEndpointJetBounds

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

attribute [local irreducible] referenceAdjointThreeHalfRadialFamily
  referenceHighAdjointCoordinateBoundaryFamily referenceRadialEndpointInvertibleLocus

theorem exists_referenceHighAdjoint_staticEndpoint_joint_jet_bounds
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) :
    let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let C0 : Fin 3 → (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun i z =>
      referenceHighAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z i
    let D : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
      deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧ ∀ N : ℕ,
      ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d),
        z ∈ Ω ∧ ContDiffAt ℝ ∞ D z ∧ ∀ i : Fin 3,
          ContDiffAt ℝ ∞ (C0 i) z ∧ ∀ k : ℕ, k ≤ N →
            ‖iteratedFDeriv ℝ k (C0 i) z‖ ≤ M ∧
            ‖iteratedFDeriv ℝ k D z‖ ≤ M := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HIGH_ADJOINT_STATIC_JETS_BODY"
    out.flush
  intro Ω C0 D
  let A : (ℝ × (R3 × ℝ)) →
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hA : ContDiffOn ℝ ∞ A Ω :=
    contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  have hDSmooth : ContDiffOn ℝ ∞ D Ω := contDiffOn_deriv_joint_radialSlice A Ω hΩ hA
  let K : ℝ → Set (ℝ × (R3 × ℝ)) := fun d =>
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)
  have hK (d : ℝ) : IsCompact (K d) :=
    isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  have hRadiusRaw := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  rcases hRadiusRaw with ⟨d0,hd0,hd0ρ,hRoom0⟩
  let F0 : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun i _ => C0 i
  let F1 : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun _ _ => D
  let d : ℝ := min d0 1
  have hd : 0 < d := lt_min hd0 (by norm_num)
  have hdd0 : d ≤ d0 := min_le_left _ _
  have hdρ : d ≤ ρ := hdd0.trans hd0ρ
  have hd1 : d ≤ 1 := min_le_right _ _
  have hRoom (z : ℝ × (R3 × ℝ)) (hz : z ∈ K d) : z ∈ Ω :=
    hRoom0 ⟨hz.1,hz.2.1,(Icc_subset_Icc (neg_le_neg hdd0) hdd0) hz.2.2⟩
  have hSmooth0 : ∀ i j : Fin 3, ∀ z ∈ K d, ContDiffAt ℝ ∞ (F0 i j) z := by
    intro i j z hz
    exact contDiffAt_referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg z i (hRoom z hz)
  have hSmooth1 : ∀ i j : Fin 3, ∀ z ∈ K d, ContDiffAt ℝ ∞ (F1 i j) z := by
    intro i j z hz
    exact hDSmooth.contDiffAt (hΩ.mem_nhds (hRoom z hz))
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HIGH_ADJOINT_STATIC_JETS_RADIUS_INPUT"
    out.flush
  refine ⟨d,hd,hdρ,hd1,?_⟩
  intro N
  have hBounds := exists_compact_finite_pair_iteratedFDeriv_bound
    F0 F1 (K d) (hK d) hSmooth0 hSmooth1 N
  refine Exists.elim hBounds ?_
  intro M hM
  refine ⟨M,hM.1,?_⟩
  intro z hz
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "HIGH_ADJOINT_STATIC_JETS_BOUNDS_RESULT"
    out.flush
  refine ⟨hRoom z hz,hDSmooth.contDiffAt (hΩ.mem_nhds (hRoom z hz)),?_⟩
  intro i
  exact ⟨hSmooth0 i (0 : Fin 3) z hz,hM.2 z hz i (0 : Fin 3)⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceHighAdjoint_staticEndpoint_joint_jet_bounds
