import Calderon.ActualOriginalNormalizedSourceMean
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic ActualFiniteHarmonicCore WeightedBaseSpectral ConformalDepth ReferenceDensityBounds
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevConstantOne harmonicSphereSubspace

theorem exists_uniform_original_density_norm_bound_of_finite_physical_graph
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (g:MatrixField) (hg:IsAdmissibleMetric g) (L B:ℝ):
    ∃ C:ℝ,0 < C ∧ ∀ q∈Icc (0:ℝ) 1,
      ∀ (chi:R3→ℝ) (hchi:Continuous chi) (hchic:HasCompactSupport chi),
      tsupport chi⊆closedBall (0:R3) B → range chi⊆Icc (0:ℝ) 1 →
      ∀ (Psi:R3→SphereSobolev (3/2:ℝ)) (hPsi:Continuous Psi),
      ∀ (W:R3→SphereL2) (hW:Continuous W) (hWc:HasCompactSupport W),
      ∀ c D:ℝ,0 < c → ‖referenceBaseLift g hg L q W hW hWc‖ ≤ D →
      let T:=nativeDensitySphereL2L hO hD
      let U:R3→SphereL2 := fun y => chi y • (T (Psi y)-T (sphereSobolevConstantOne (3/2:ℝ)))
      let hU:Continuous U := hchi.smul ((T.continuous.comp hPsi).sub continuous_const)
      let hUc:HasCompactSupport U := hchic.smul_right
      ∀ (Us Vs:ℕ→R3→SphereL2),
      (∀ n,Continuous (Us n)) → (∀ n,HasCompactSupport (Us n)) →
      (∀ n,Continuous (Vs n)) → (∀ n,HasCompactSupport (Vs n)) →
      Tendsto (fun n:ℕ => ∫ y,referenceDensityFamily g L (q,y)*‖Us n y-U y‖^2) atTop (𝓝 0) →
      Tendsto (fun n:ℕ => ∫ y,referenceDensityFamily g L (q,y)*‖Vs n y-W y‖^2) atTop (𝓝 0) →
      (∀ n:ℕ,c*(∫ y,referenceDensityFamily g L (q,y)*‖Us n y‖^2) ≤
        ∫ y,referenceDensityFamily g L (q,y)*‖Vs n y‖^2) →
      ‖referenceBaseLift g hg L q (fun y => chi y • T (Psi y))
        (hchi.smul (T.continuous.comp hPsi)) hchic.smul_right‖ ≤ D/Real.sqrt c+C := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_original_cutoff_density_source_norm_shift hO hD g hg L B
  refine ⟨C,hC,?_⟩
  intro q hq chi hchi hchic hSupport hRange Psi hPsi W hW hWc c D hc hD0
  dsimp only
  intro Us Vs hUs hUsc hVs hVsc hSource hOutput hFinite
  let T:=nativeDensitySphereL2L hO hD
  let U:R3→SphereL2 := fun y => chi y • (T (Psi y)-T (sphereSobolevConstantOne (3/2:ℝ)))
  have hU:Continuous U := hchi.smul ((T.continuous.comp hPsi).sub continuous_const)
  have hUc:HasCompactSupport U := hchic.smul_right
  have hCoercive:=norm_referenceBaseLift_le_of_finite_physical_graph_coercivity
    g hg L q c hc Us U Vs W hUs hU hVs hW hUsc hUc hVsc hWc hSource hOutput hFinite
  have hNorm:‖referenceBaseLift g hg L q U hU hUc‖ ≤ D/Real.sqrt c :=
    hCoercive.trans (div_le_div_of_nonneg_right hD0 (Real.sqrt_nonneg c))
  exact (HC q hq chi hchi hchic hSupport hRange Psi hPsi).trans (add_le_add hNorm (le_refl C))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
