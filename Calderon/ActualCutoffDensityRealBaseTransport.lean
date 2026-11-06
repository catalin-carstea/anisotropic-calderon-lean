import Calderon.ActualReferenceSphereL2BaseTransport

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic ExteriorSource WeightedBaseSpectral ConformalDepth

/-- A finite fixed-frame reference-base lift bound gives the exact Euclidean
cutoff density norm required by the source-matched Taylor/L² interpolation.
The lift bound itself remains a separate conditional input. -/
theorem exists_uniform_cutoff_density_Euclidean_le_real_referenceBaseLift
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ chi : R3 → ℝ,
        Continuous chi → HasCompactSupport chi →
        ∀ Psi : R3 → SphereSobolev (3/2 : ℝ), ContDiff ℝ ∞ Psi →
          let V : R3 → SphereL2 := fun y => chi y •
            (sphereSobolevZeroEquiv hO hD).symm
              (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) (Psi y))
          ∃ hV : Continuous V, ∃ hVc : HasCompactSupport V,
            ∀ D : ℝ, 0 ≤ D →
              ‖referenceBaseLift g hg L lam V hV hVc‖ₑ ≤ ENNReal.ofReal D →
              eLpNorm V 2 ((volume : Measure R3).restrict cylinder) ≤
                ENNReal.ofReal (A * D) := by
  obtain ⟨C,hC,hTransport⟩ :=
    exists_uniform_cutoff_density_Euclidean_le_referenceBaseLift g hg L hO hD
  let A : ℝ := C.toReal
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  refine ⟨A,hA,?_⟩
  intro lam hLam chi hChi hChiCompact Psi hPsi V
  obtain ⟨hV,hVc,hCompare⟩ :=
    hTransport lam hLam chi hChi hChiCompact Psi hPsi
  refine ⟨hV,hVc,?_⟩
  intro D hD hLift
  calc
    eLpNorm V 2 ((volume : Measure R3).restrict cylinder)
        ≤ C * ‖referenceBaseLift g hg L lam V hV hVc‖ₑ := hCompare
    _ ≤ C * ENNReal.ofReal D := by gcongr
    _ = ENNReal.ofReal (A * D) := by
      rw [← ENNReal.ofReal_toReal hC, ENNReal.ofReal_mul hA]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
