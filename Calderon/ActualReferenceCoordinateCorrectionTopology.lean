import Calderon.ActualReferenceCoordinateDefectGain
import Calderon.ActualReferenceCoordinateForcingTopology
import Calderon.ActualReferenceInvertibleWeakLiftTopology
import Calderon.ActualReferenceRadialEndpointOpenLocus

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal ContDiff Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem contDiffAt_referenceCoordinateStrongDefectFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (k : Fin 3)
    (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceCoordinateStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF k) p := by
  letI : CompleteSpace (StrongDirichletSpace 0) := instCompleteSpaceStrongDirichletSpace 0
  have hA := contDiff_joint_referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0
  have hInv : ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) =>
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 t.1 t.2).inverse) p :=
    by
      have hMap := hStrong.contDiffAt_map_inverse (n := ∞)
      try simp only [real_nontriviallyNormedField_normedField_eq,
        submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
        clm_normedAddCommGroup_seminormedAddCommGroup_eq,
        normedAddCommGroup_ofSeparation_eq,
        submodule_seminormedAddCommGroup_topologicalSpace_eq,
        submodule_seminormedAddCommGroup_addCommMonoid_eq,
        submodule_normedSpace_module_eq,
        lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
        clm_seminormedAddCommGroup_topologicalSpace_eq,
        clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hMap
      simpa only [Function.comp_def] using hMap.comp p hA.contDiffAt
  have hQ := contDiff_referenceCoordinateCommutatorForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc k
  have hW := contDiffAt_referenceWeakHalfLiftFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF p hWeak
  unfold referenceCoordinateStrongDefectFamily
  exact contDiffAt_const.clm_comp (hInv.clm_comp (hQ.contDiffAt.clm_comp hW))

theorem contDiffAt_referenceCoordinateWeakDefectFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coordinateSmoothDatum k).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coordinateSmoothDatum k).1 x‖ ≤ M)
    (p : ℝ × (R3 × ℝ))
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ContDiffAt ℝ ∞
      (referenceCoordinateWeakDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k hM hm hg) p := by
  have hW := contDiffAt_referenceWeakHalfLiftFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF p hWeak
  unfold referenceCoordinateWeakDefectFamily
  exact (hW.clm_comp contDiffAt_const).sub (contDiffAt_const.clm_comp hW)

theorem contDiffOn_referenceCoordinateStrongDefectFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (k : Fin 3) :
    ContDiffOn ℝ ∞ (referenceCoordinateStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF k)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  intro p hp
  exact (contDiffAt_referenceCoordinateStrongDefectFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF k p hp.1 hp.2.1).contDiffWithinAt

theorem exists_reference_commonRadius_coordinateStrongDefect_smooth_room
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ),
        p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
        ∀ k : Fin 3, ContDiffAt ℝ ∞
          (referenceCoordinateStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF k) p := by
  obtain ⟨δ,hδ,hδρ,hRoom⟩ := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  refine ⟨δ,hδ,hδρ,?_⟩
  intro p hp
  have hi := hRoom hp
  refine ⟨hi,?_⟩
  intro k
  exact contDiffAt_referenceCoordinateStrongDefectFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF k p hi.1 hi.2.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
