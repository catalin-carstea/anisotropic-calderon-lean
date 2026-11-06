import Calderon.ActualJacobiNativeMultiplierEndpointJointJets

/-! One actual common scalar bound; three separate original native operator norms. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier

structure ReferenceJacobiNativeMultiplierJointJetBounds
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) where
  bound : ℝ
  one_le_bound : 1 ≤ bound
  highBound : ∀ k : ℕ, k ≤ 3 →
    ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ),
    ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ k
        (fun t : ℝ × (R3 × ℝ) => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryThreeHalfCoefficientFamily
            g hg L y0 Φ B ε C ρ H a w hData i j t)) p‖ ≤ bound
  halfBound : ∀ k : ℕ, k ≤ 3 →
    ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ),
    ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ k
        (fun t : ℝ × (R3 × ℝ) => nativeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryCoefficientFamily
            g hg L y0 Φ B ε C ρ H a w hData i j t)) p‖ ≤ bound
  negativeBound : ∀ k : ℕ, k ≤ 3 →
    ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ),
    ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ k
        (fun t : ℝ × (R3 × ℝ) => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryCoefficientFamily
            g hg L y0 Φ B ε C ρ H a w hData i j t)) p‖ ≤ bound

theorem exists_referenceJacobiNativeMultiplierJointJetBounds
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    Nonempty (ReferenceJacobiNativeMultiplierJointJetBounds
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-BOUNDS BODY_ENTER"
    out.flush
  obtain ⟨Mh,hMh,hBoundH⟩ :=
    exists_referenceJacobi_nativeThreeHalfMultiplier_joint_jet_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-BOUNDS HIGH_READY"
    out.flush
  obtain ⟨Mm,hMm,hBoundM⟩ :=
    exists_referenceJacobi_nativeHalfMultiplier_joint_jet_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-BOUNDS HALF_READY"
    out.flush
  obtain ⟨Ml,hMl,hBoundL⟩ :=
    exists_referenceJacobi_nativeNegativeHalfMultiplier_joint_jet_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-BOUNDS NEGATIVE_READY"
    out.flush
  let M : ℝ := 1+Mh+Mm+Ml
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hMhM : Mh ≤ M := by dsimp [M]; linarith
  have hMmM : Mm ≤ M := by dsimp [M]; linarith
  have hMlM : Ml ≤ M := by dsimp [M]; linarith
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-BOUNDS ASSEMBLY_ENTER"
    out.flush
  exact ⟨{
    bound := M
    one_le_bound := hM
    highBound := fun k hk p hp i j => (hBoundH k hk p hp i j).trans hMhM
    halfBound := fun k hk p hp i j => (hBoundM k hk p hp i j).trans hMmM
    negativeBound := fun k hk p hp i j => (hBoundL k hk p hp i j).trans hMlM
  }⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceJacobiNativeMultiplierJointJetBounds
