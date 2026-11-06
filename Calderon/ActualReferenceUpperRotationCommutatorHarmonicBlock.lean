import Calderon.ActualUpperRotationSingleGraphDiagnostic

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation SmoothSphereRotationProjection SpectralWeightedGraph

/-! Full upfront argument is EXPANSION-v006.json in this immutable author directory.
This is the actual harmonic block identity and its exact degree-weighted upper bound.
The degree weights are retained; no uniform Sylvester half-form premise is introduced. -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceSharpRadialTraceFamily referenceSharpRadialRotationCommutatorL

lemma referenceSharpRadialRotationCommutatorL_harmonic_block
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (m n : ℕ) (u : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (1/2:ℝ) m
      (referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
          (sphereSobolevSingleL (3/2:ℝ) n u)) =
    harmonicSphereRotation m i j
      (sphereSobolevCoefficientL (1/2:ℝ) m
        (referenceSharpRadialTraceFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
            (sphereSobolevSingleL (3/2:ℝ) n u))) -
    sphereSobolevCoefficientL (1/2:ℝ) m
      (referenceSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
          (sphereSobolevSingleL (3/2:ℝ) n (harmonicSphereRotation n i j u))) := by
  let T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  have h := referenceSharpRadialRotationCommutatorL_single_graph_diagnostic
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hStrong hWeak n u
  have hh := congrArg
    (fun z : SphereSobolev (-(1/2:ℝ)) => sphereSobolevCoefficientL (-(1/2:ℝ)) m z) h
  simp only [map_sub,sphereSobolevCoefficientL_inclusion] at hh
  have hOutput : sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (sphereSobolevRotationL (1/2:ℝ) i j (T (sphereSobolevSingleL (3/2:ℝ) n u))) =
      harmonicSphereRotation m i j
        (sphereSobolevCoefficientL (1/2:ℝ) m (T (sphereSobolevSingleL (3/2:ℝ) n u))) := by
    have hCoefficient (w : SphereSobolev (-(1/2:ℝ))) :
        sphereSobolevCoefficientL ((1/2:ℝ)-1) m w =
          sphereSobolevCoefficientL (-(1/2:ℝ)) m w := by
      change besselWeight (-((1/2:ℝ)-1)) m • w m =
        besselWeight (-(-(1/2:ℝ))) m • w m
      exact congrArg (fun r : ℝ => r • w m)
        (congrArg (fun s : ℝ => besselWeight (-s) m)
          (show (1/2:ℝ)-1 = -(1/2:ℝ) from by norm_num))
    exact (hCoefficient (sphereSobolevRotationL (1/2:ℝ) i j
      (T (sphereSobolevSingleL (3/2:ℝ) n u)))).symm.trans
        (sphereSobolevCoefficientL_rotation (1/2:ℝ) i j m (T (sphereSobolevSingleL (3/2:ℝ) n u)))
  rw [hOutput] at hh
  exact hh.symm

lemma norm_referenceSharpRadialRotationCommutatorL_harmonic_block_le
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (m n : ℕ) (u : harmonicSphereSubspace n) :
    ‖harmonicSphereRotation m i j
      (sphereSobolevCoefficientL (1/2:ℝ) m
        (referenceSharpRadialTraceFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
            (sphereSobolevSingleL (3/2:ℝ) n u))) -
      sphereSobolevCoefficientL (1/2:ℝ) m
        (referenceSharpRadialTraceFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
            (sphereSobolevSingleL (3/2:ℝ) n (harmonicSphereRotation n i j u)))‖ ≤
    besselWeight (-(1/2:ℝ)) m *
      ‖referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p‖ *
      besselWeight (3/2:ℝ) n * ‖u‖ := by
  rw [← referenceSharpRadialRotationCommutatorL_harmonic_block
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hStrong hWeak m n u]
  let D : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
  change ‖besselWeight (-(1/2:ℝ)) m • (D (sphereSobolevSingleL (3/2:ℝ) n u)) m‖ ≤
    besselWeight (-(1/2:ℝ)) m * ‖D‖ * besselWeight (3/2:ℝ) n * ‖u‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (besselWeight_pos (-(1/2:ℝ)) m)]
  calc
    _ ≤ besselWeight (-(1/2:ℝ)) m * ‖D (sphereSobolevSingleL (3/2:ℝ) n u)‖ :=
      mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num) _ m)
        (besselWeight_pos (-(1/2:ℝ)) m).le
    _ ≤ besselWeight (-(1/2:ℝ)) m * (‖D‖ * ‖sphereSobolevSingleL (3/2:ℝ) n u‖) :=
      mul_le_mul_of_nonneg_left (D.le_opNorm _) (besselWeight_pos (-(1/2:ℝ)) m).le
    _ = _ := by rw [norm_sphereSobolevSingleL_apply]; ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialRotationCommutatorL_harmonic_block
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_referenceSharpRadialRotationCommutatorL_harmonic_block_le
