import Calderon.RadiusTwoSmoothSourceSeparation
import Calderon.RadiusTwoSmoothSourceJetLinear
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Coordinates made of actual source responses. -/
set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature

def radiusTwoSourceCoordinates
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ)) (x : R3) : Fin 3 → ℝ :=
  fun i => radiusTwoSmoothSourceResponse hreg hcalc g hg (f i) x

theorem contDiffOn_radiusTwoSourceCoordinates
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ)) :
    ContDiffOn ℝ ∞ (radiusTwoSourceCoordinates hreg hcalc g hg f) (radiusTwoOpens : Set R3) := by
  apply contDiffOn_pi.mpr
  intro i
  exact (radiusTwoSmoothSourceResponse_spec hreg hcalc g hg (f i)).2.1

theorem exists_radiusTwoSourceCoordinates_hasFDerivAt
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) :
    ∃ f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ),
      HasFDerivAt (radiusTwoSourceCoordinates hreg hcalc g hg f)
        (EuclideanSpace.equiv (Fin 3) ℝ : R3 →L[ℝ] (Fin 3 → ℝ)) p := by
  have hExist (i : Fin 3) := radiusTwoSmoothSourceResponse_fderiv_surjective
    hreg hcalc hSep g hg p hp (EuclideanSpace.proj i)
  choose f hf using hExist
  refine ⟨f,?_⟩
  apply hasFDerivAt_pi'.mpr
  intro i
  have h := (differentiableAt_radiusTwoSmoothSourceResponse hreg hcalc g hg (f i) p hp).hasFDerivAt
  have hi : fderiv ℝ (radiusTwoSmoothSourceResponse hreg hcalc g hg (f i)) p =
      EuclideanSpace.proj i := hf i
  rw [hi] at h
  exact h

theorem exists_radiusTwoSourceCoordinates_localChart
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3)) :
    ∃ (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
      (e : OpenPartialHomeomorph R3 (Fin 3 → ℝ)),
      (e : R3 → (Fin 3 → ℝ)) = radiusTwoSourceCoordinates hreg hcalc g hg f ∧
      p ∈ e.source ∧ ContDiffAt ℝ ∞ e.symm (e p) := by
  obtain ⟨f,hD⟩ := exists_radiusTwoSourceCoordinates_hasFDerivAt hreg hcalc hSep g hg p hp
  have hS : ContDiffAt ℝ ∞ (radiusTwoSourceCoordinates hreg hcalc g hg f) p :=
    (contDiffOn_radiusTwoSourceCoordinates hreg hcalc g hg f).contDiffAt
      (radiusTwoOpens.isOpen.mem_nhds hp)
  let e := hS.toOpenPartialHomeomorph (radiusTwoSourceCoordinates hreg hcalc g hg f) hD (by simp)
  refine ⟨f,e,rfl,hS.mem_toOpenPartialHomeomorph_source hD (by simp),?_⟩
  exact hS.to_localInverse hD (by simp)

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceCoordinates
#print axioms OAI.AnisotropicCalderon.ExteriorSource.contDiffOn_radiusTwoSourceCoordinates
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSourceCoordinates_hasFDerivAt
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSourceCoordinates_localChart
