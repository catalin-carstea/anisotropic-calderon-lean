import Calderon.RadiusTwoSourceCoordinates
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff Distributions Matrix BigOperators
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

theorem continuousAt_radiusTwoSourceCovectorMatrix
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
    (x : R3) (hx : x ∈ (radiusTwoOpens : Set R3)) :
    ContinuousAt (fun y : R3 => Matrix.of (fun i j =>
      d (radiusTwoSmoothSourceResponse hreg hcalc g hg (f i)) y j)) x := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  have hSmooth := (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg (f i)).2.1
  have hDeriv : ContinuousAt (fderiv ℝ
      (radiusTwoSmoothSourceResponse hreg hcalc g hg (f i))) x :=
    (hSmooth.contDiffAt
      (radiusTwoOpens.isOpen.mem_nhds hx)).continuousAt_fderiv (by simp)
  exact hDeriv.clm_apply continuousAt_const

theorem continuousAt_radiusTwoSourceCovectorGram
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
    (x : R3) (hx : x ∈ (radiusTwoOpens : Set R3)) :
    ContinuousAt (fun y : R3 =>
      Matrix.of (fun i j => d (radiusTwoSmoothSourceResponse hreg hcalc g hg (f i)) y j) * (g y)⁻¹ *
      Matrix.of (fun i j => d (radiusTwoSmoothSourceResponse hreg hcalc g hg (f i)) y j)ᵀ) x := by
  let K : R3 → Matrix (Fin 3) (Fin 3) ℝ := fun y i j =>
    d (radiusTwoSmoothSourceResponse hreg hcalc g hg (f i)) y j
  change ContinuousAt (fun y : R3 => K y * (g y)⁻¹ * (K y)ᵀ) x
  have hK : ContinuousAt K x :=
    continuousAt_radiusTwoSourceCovectorMatrix hreg hcalc g hg f x hx
  have hEntry (i j : Fin 3) : ContinuousAt (fun y : R3 => K y i j) x :=
    continuousAt_pi.mp (continuousAt_pi.mp hK i) j
  have hInverseEntry (i j : Fin 3) :
      ContinuousAt (fun y : R3 => (g y)⁻¹ i j) x :=
    (contDiff_metric_inverse_entry g hg i j).continuous.continuousAt
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  change ContinuousAt (fun y : R3 => ∑ k : Fin 3,
    (∑ l : Fin 3, K y i l * (g y)⁻¹ l k) * K y j k) x
  exact tendsto_finsetSum Finset.univ (fun k _ =>
    (tendsto_finsetSum Finset.univ (fun l _ =>
      (hEntry i l).mul (hInverseEntry l k))).mul (hEntry j k))

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.continuousAt_radiusTwoSourceCovectorMatrix
#print axioms OAI.AnisotropicCalderon.ExteriorSource.continuousAt_radiusTwoSourceCovectorGram
