import Calderon.ActualJacobiThreeHalfBoundaryMultiplierFamily
import Calderon.ActualJacobiFullJointJets

/-! Full before-source: actual-covariant-leading-algebra-author-oct16-v001/
EXPANSION-paired-room-and-Jacobi-endpoint-declaration-splits-v013.md;
separate original native endpoint codomains; preflight v014. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier

theorem exists_referenceJacobi_nativeThreeHalfMultiplier_joint_jet_bound
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ 3 →
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ),
      ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ k
          (fun t : ℝ × (R3 × ℝ) =>
            nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
              (referenceJacobiBoundaryThreeHalfCoefficientFamily
                g hg L y0 Φ B ε C ρ H a w hData i j t)) p‖ ≤ M := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-ENDPOINT HIGH BODY_ENTER"
    out.flush
  let Kgeom : Set (ℝ × (R3 × ℝ)) :=
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)
  have hKgeom : IsCompact Kgeom :=
    isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  have hρ : 0 < ρ := hData.1.2.1
  have hInv (p : ℝ × (R3 × ℝ)) (hp : p ∈ Kgeom) : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible := by
    intro x
    have hy : ‖p.2.1-y0‖ ≤ ρ := by
      simpa only [mem_closedBall,dist_eq_norm] using hp.2.1
    have hr : |p.2.2| ≤ ρ := abs_le.mpr hp.2.2
    have hx : ‖x.val‖ = 1 := by
      simpa [UnitSphere,Metric.sphere,dist_eq_norm] using x.property
    apply referenceFramedNormalizedJacobian_isInvertible_on_actual_drift_room
      g L y0 Φ B ε C ρ H a w hData p.1 hp.1 p.2.1 (by linarith)
        p.2.2 (by linarith) x.val
    simpa only [mem_closedBall,dist_zero_right,hx] using (show (1 : ℝ) ≤ 2 by norm_num)
  let N : (Fin 3 × Fin 3) → (ℝ × (R3 × ℝ)) →
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := fun ij t =>
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryThreeHalfCoefficientFamily
        g hg L y0 Φ B ε C ρ H a w hData ij.1 ij.2 t)
  have hSmooth (ij : Fin 3 × Fin 3) (p : ℝ × (R3 × ℝ)) (hp : p ∈ Kgeom) :
      ContDiffAt ℝ ∞ (N ij) p :=
    contDiffAt_nativeThreeHalf_referenceJacobiBoundaryThreeHalfCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ij.1 ij.2 p (hInv p hp)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-ENDPOINT HIGH SMOOTH_READY"
    out.flush
  obtain ⟨M,hM,hBound⟩ :=
    exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      N Kgeom hKgeom hSmooth 3
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-ENDPOINT HIGH COMPACT_READY"
    out.flush
  refine ⟨M,hM,?_⟩
  intro k hk p hp i j
  exact hBound k hk p hp (i,j)

theorem exists_referenceJacobi_nativeHalfMultiplier_joint_jet_bound
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ 3 →
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ),
      ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ k
          (fun t : ℝ × (R3 × ℝ) =>
            nativeHalfCoefficientMulL hcalc hF hO hD τ0
              (referenceJacobiBoundaryCoefficientFamily
                g hg L y0 Φ B ε C ρ H a w hData i j t)) p‖ ≤ M := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-ENDPOINT HALF BODY_ENTER"
    out.flush
  let Kgeom : Set (ℝ × (R3 × ℝ)) :=
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)
  have hKgeom : IsCompact Kgeom :=
    isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  have hρ : 0 < ρ := hData.1.2.1
  have hInv (p : ℝ × (R3 × ℝ)) (hp : p ∈ Kgeom) : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible := by
    intro x
    have hy : ‖p.2.1-y0‖ ≤ ρ := by
      simpa only [mem_closedBall,dist_eq_norm] using hp.2.1
    have hr : |p.2.2| ≤ ρ := abs_le.mpr hp.2.2
    have hx : ‖x.val‖ = 1 := by
      simpa [UnitSphere,Metric.sphere,dist_eq_norm] using x.property
    apply referenceFramedNormalizedJacobian_isInvertible_on_actual_drift_room
      g L y0 Φ B ε C ρ H a w hData p.1 hp.1 p.2.1 (by linarith)
        p.2.2 (by linarith) x.val
    simpa only [mem_closedBall,dist_zero_right,hx] using (show (1 : ℝ) ≤ 2 by norm_num)
  let N : (Fin 3 × Fin 3) → (ℝ × (R3 × ℝ)) →
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun ij t =>
    nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryCoefficientFamily
        g hg L y0 Φ B ε C ρ H a w hData ij.1 ij.2 t)
  have hSmooth (ij : Fin 3 × Fin 3) (p : ℝ × (R3 × ℝ)) (hp : p ∈ Kgeom) :
      ContDiffAt ℝ ∞ (N ij) p :=
    contDiffAt_nativeHalf_referenceJacobiBoundaryCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ij.1 ij.2 p (hInv p hp)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-ENDPOINT HALF SMOOTH_READY"
    out.flush
  obtain ⟨M,hM,hBound⟩ :=
    exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      N Kgeom hKgeom hSmooth 3
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-ENDPOINT HALF COMPACT_READY"
    out.flush
  refine ⟨M,hM,?_⟩
  intro k hk p hp i j
  exact hBound k hk p hp (i,j)

theorem exists_referenceJacobi_nativeNegativeHalfMultiplier_joint_jet_bound
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ 3 →
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ),
      ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ k
          (fun t : ℝ × (R3 × ℝ) =>
            nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
              (referenceJacobiBoundaryCoefficientFamily
                g hg L y0 Φ B ε C ρ H a w hData i j t)) p‖ ≤ M := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-ENDPOINT NEGATIVE BODY_ENTER"
    out.flush
  let Kgeom : Set (ℝ × (R3 × ℝ)) :=
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)
  have hKgeom : IsCompact Kgeom :=
    isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  have hρ : 0 < ρ := hData.1.2.1
  have hInv (p : ℝ × (R3 × ℝ)) (hp : p ∈ Kgeom) : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,x.val))).IsInvertible := by
    intro x
    have hy : ‖p.2.1-y0‖ ≤ ρ := by
      simpa only [mem_closedBall,dist_eq_norm] using hp.2.1
    have hr : |p.2.2| ≤ ρ := abs_le.mpr hp.2.2
    have hx : ‖x.val‖ = 1 := by
      simpa [UnitSphere,Metric.sphere,dist_eq_norm] using x.property
    apply referenceFramedNormalizedJacobian_isInvertible_on_actual_drift_room
      g L y0 Φ B ε C ρ H a w hData p.1 hp.1 p.2.1 (by linarith)
        p.2.2 (by linarith) x.val
    simpa only [mem_closedBall,dist_zero_right,hx] using (show (1 : ℝ) ≤ 2 by norm_num)
  let N : (Fin 3 × Fin 3) → (ℝ × (R3 × ℝ)) →
      (SphereSobolev (-(1/2) : ℝ) →L[ℝ] SphereSobolev (-(1/2) : ℝ)) := fun ij t =>
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryCoefficientFamily
        g hg L y0 Φ B ε C ρ H a w hData ij.1 ij.2 t)
  have hSmooth (ij : Fin 3 × Fin 3) (p : ℝ × (R3 × ℝ)) (hp : p ∈ Kgeom) :
      ContDiffAt ℝ ∞ (N ij) p :=
    contDiffAt_nativeNegativeHalf_referenceJacobiBoundaryCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ij.1 ij.2 p (hInv p hp)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-ENDPOINT NEGATIVE SMOOTH_READY"
    out.flush
  obtain ⟨M,hM,hBound⟩ :=
    exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      N Kgeom hKgeom hSmooth 3
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-JACOBI-ENDPOINT NEGATIVE COMPACT_READY"
    out.flush
  refine ⟨M,hM,?_⟩
  intro k hk p hp i j
  exact hBound k hk p hp (i,j)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceJacobi_nativeThreeHalfMultiplier_joint_jet_bound
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceJacobi_nativeHalfMultiplier_joint_jet_bound
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceJacobi_nativeNegativeHalfMultiplier_joint_jet_bound
